// Ported from tsc/internal/contentmapper/transform.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go's `*ast.SourceFile` results become arena-based: [`ParsedSourceFile`]
//   carries the `NodeId` of the `SourceFile` plus the node arena containing
//   it (`NodeId`s carry the file index, so ids from different arenas are
//   comparable, as Go's pointers are).
// - `sourceFile.SetContentMapperInfo` mutates the parsed `SourceFile` inside
//   its arena; the port sets it before returning (the setter panics if the
//   info is already present, matching Go's publish-once contract).
// - Go attaches mapper diagnostics to the canonical file via a live
//   `*SourceFile` before `SetContentMapperInfo`; `DiagnosticFile` snapshots
//   `original_text` at construction, so the Rust port builds diagnostic file
//   handles after setting the info — matching what a Go diagnostic reader
//   observes (the file's untransformed text).
// - `project Project` → `&Arc<dyn Project>` (Go's interface reference);
//   `fileExists func(tspath.RootedFilePath) bool` → `impl Fn(&RootedFilePath)`.
// - Go's `NewTransformError(KindResponse, nil)` / `(KindMappings, nil)` have
//   a nil inner error — `TransformError::new(kind, None)`.

use std::sync::Arc;

use tsc_ast as ast;
use tsc_ast::Node;
use tsc_ast::NodeId;
use tsc_ast::ast_generated::SourceFile;
use tsc_ast::diagnostic::{DiagnosticFile, DiagnosticRef, lock_diagnostic};
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_parser as parser;
use tsc_spanmap::SpanMap;
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::contentmapper::{Mapper, is_supported_virtual_extension};
use crate::host::{
    Error, Project, Request, Result, SupplementalFileCollisionError, TransformError,
    TransformErrorKind,
};

/// `type SourceFiles struct` — the canonical output and its unnamed
/// supplemental compiler inputs.
#[derive(Clone, Default)]
pub struct SourceFiles {
    /// `Canonical` — the virtual source file named after the original.
    pub canonical: ParsedSourceFile,
    /// `Supplemental` — additional compiler inputs (in declaration order).
    pub supplemental: Vec<ParsedSourceFile>,
}

/// A parsed `SourceFile` — Go's `*ast.SourceFile` becomes the `(NodeId,
/// arena)` pair. `file` indexes `nodes`. `Clone` is a shallow structural
/// copy of the arena (the cache holds the canonical instance; programs
/// re-bind their own copy).
#[derive(Clone, Default)]
pub struct ParsedSourceFile {
    /// The `NodeId` of the parsed `SourceFile` inside `nodes`.
    pub file: NodeId,
    /// `SourceFile.Nodes` — the arena that owns `file` and its descendants.
    pub nodes: Vec<Node>,
}

impl ParsedSourceFile {
    /// The `SourceFile` payload (Go's dereference of the file pointer).
    pub fn source_file(&self) -> &SourceFile {
        self.nodes[self.file].as_source_file()
    }

    /// `sourceFile.Text()`
    pub fn text(&self) -> &str {
        self.source_file().text()
    }

    /// `sourceFile.FileName()`
    pub fn file_name(&self) -> &RootedFilePath {
        self.source_file().file_name()
    }

    /// `sourceFile.PathKey()`
    pub fn path_key(&self) -> &tspath::PathKey {
        self.source_file().path_key()
    }

    /// `sourceFile.ScriptKind`
    pub fn script_kind(&self) -> ScriptKind {
        self.source_file().script_kind
    }

    /// `sourceFile.ParseOptions()`
    pub fn parse_options(&self) -> &SourceFileParseOptions {
        self.source_file().parse_options()
    }

    /// `sourceFile.SupplementalSourceFiles()`
    pub fn supplemental_source_files(&self) -> &[NodeId] {
        self.source_file().supplemental_source_files()
    }

    /// `sourceFile.CanonicalSourceFile()`
    pub fn canonical_source_file(&self) -> Option<NodeId> {
        self.source_file().canonical_source_file()
    }

    /// `sourceFile.ContentMapperTransformIdentity()`
    pub fn content_mapper_transform_identity(&self) -> &str {
        self.source_file().content_mapper_transform_identity()
    }

    /// `sourceFile.Diagnostics()`
    pub fn diagnostics(&self) -> &[DiagnosticRef] {
        self.source_file().diagnostics()
    }
}

/// `func TransformAndParse(parseOptions, content, mapper, project) (SourceFiles, error)`
pub fn transform_and_parse(
    parse_options: &SourceFileParseOptions,
    content: &str,
    mapper: &Arc<Mapper>,
    project: &Arc<dyn Project>,
) -> std::result::Result<SourceFiles, Error> {
    let transform_identity = project
        .identity(mapper)
        .map_err(|e| Error::transform(TransformErrorKind::Project, e))?;
    let result = project.transform(
        mapper,
        &Request {
            file_name: parse_options.file_name.clone(),
            content: content.to_string(),
        },
    )?;
    parse_result(parse_options, content, mapper, &transform_identity, result)
}

/// `func ParseResult(parseOptions, content, mapper, transformIdentity, result) (SourceFiles, error)`
pub fn parse_result(
    parse_options: &SourceFileParseOptions,
    content: &str,
    mapper: &Arc<Mapper>,
    transform_identity: &str,
    result: Result,
) -> std::result::Result<SourceFiles, Error> {
    let Some(mappings) = result.mappings.as_deref() else {
        return Err(Error::Transform(TransformError::new(
            TransformErrorKind::Mappings,
            None,
        )));
    };
    if let Some(problem) = SpanMap::validate(Some(mappings), &result.text, content) {
        return Err(Error::Mapping(problem));
    }
    let virtual_extension = &result.virtual_extension;
    if !is_supported_virtual_extension(virtual_extension) {
        return Err(Error::Transform(TransformError::new(
            TransformErrorKind::Response,
            None,
        )));
    }
    let base_parse_options = parse_options.clone();
    let virtual_file_name = base_parse_options
        .file_name
        .append_suffix(virtual_extension);
    let mut canonical_parse_options = base_parse_options.clone();
    if is_module_virtual_extension(virtual_extension) {
        canonical_parse_options
            .external_module_indicator_options
            .force = true;
    }
    let script_kind = tsc_core::core::get_script_kind_from_file_name(&virtual_file_name);
    let (file, nodes) =
        parser::parse_source_file(canonical_parse_options.clone(), &result.text, script_kind);
    let mut canonical = ParsedSourceFile { file, nodes };
    if !result.diagnostics.is_empty() {
        // The runner produces diagnostics without a source file (it doesn't
        // have one yet); associate them with the file now so they are
        // reported against it.
        let mut diags = canonical.source_file().diagnostics().to_vec();
        diags.extend(result.diagnostics.iter().cloned());
        canonical.nodes[canonical.file]
            .as_source_file_mut()
            .set_diagnostics(diags);
    }
    let mut files = SourceFiles {
        canonical,
        supplemental: Vec::with_capacity(result.supplemental.len()),
    };
    for (i, supplemental) in result.supplemental.iter().enumerate() {
        if supplemental.mappings.is_none() {
            return Err(Error::Transform(TransformError::new(
                TransformErrorKind::Mappings,
                None,
            )));
        }
        if let Some(problem) = SpanMap::validate(
            supplemental.mappings.as_deref(),
            &supplemental.text,
            content,
        ) {
            return Err(Error::Mapping(problem));
        }
        let mut supplemental_options = base_parse_options.clone();
        if !is_supported_virtual_extension(&supplemental.virtual_extension) {
            return Err(Error::Transform(TransformError::new(
                TransformErrorKind::Response,
                None,
            )));
        }
        // `"." + strconv.Itoa(i) + supplemental.VirtualExtension`
        let suffix = format!(".{i}{}", supplemental.virtual_extension);
        supplemental_options.file_name = supplemental_options.file_name.append_suffix(&suffix);
        supplemental_options.path_key = canonical_parse_options
            .path_key
            .append_canonical_suffix(&suffix);
        if is_module_virtual_extension(&supplemental.virtual_extension) {
            supplemental_options.external_module_indicator_options.force = true;
        }
        let supplemental_script_kind =
            tsc_core::core::get_script_kind_from_file_name(&supplemental_options.file_name);
        let (file, nodes) = parser::parse_source_file(
            supplemental_options,
            &supplemental.text,
            supplemental_script_kind,
        );
        files.supplemental.push(ParsedSourceFile { file, nodes });
    }
    let mapper_identity = mapper.identity();
    // `sourceFile.SetContentMapperInfo` — before building the diagnostic
    // file handles below so their `original_text` snapshots the input
    // content (Go's live `*SourceFile` sees it through `OriginalText()`).
    files.canonical.nodes[files.canonical.file]
        .as_source_file_mut()
        .set_content_mapper_info(ast::ContentMapperSourceFileInfo {
            content_mapper: mapper_identity.clone(),
            transform_identity: transform_identity.to_string(),
            parse_options: base_parse_options.clone(),
            virtual_file_name: virtual_file_name.clone(),
            original_text: content.to_string(),
            span_map: result.mappings.clone(),
            diagnostic_directives: result.diagnostic_directives.clone(),
            supplemental_source_files: files.supplemental.iter().map(|f| f.file).collect(),
            canonical_source_file: None,
            canonical_file_name: None,
        });
    // `diagnostic.SetFile(sourceFile)` on each mapper diagnostic.
    for d in &result.diagnostics {
        lock_diagnostic(d).set_file(Some(DiagnosticFile::from_node(
            files.canonical.file,
            &files.canonical.nodes,
        )));
    }
    for i in 0..files.supplemental.len() {
        let supplemental = &result.supplemental[i];
        let file = &mut files.supplemental[i];
        let virtual_file_name = file.source_file().file_name().clone();
        file.nodes[file.file]
            .as_source_file_mut()
            .set_content_mapper_info(ast::ContentMapperSourceFileInfo {
                content_mapper: mapper_identity.clone(),
                transform_identity: transform_identity.to_string(),
                parse_options: base_parse_options.clone(),
                virtual_file_name,
                original_text: content.to_string(),
                span_map: supplemental.mappings.clone(),
                diagnostic_directives: supplemental.diagnostic_directives.clone(),
                supplemental_source_files: Vec::new(),
                canonical_source_file: Some(files.canonical.file),
                // `canonical.FileName()` — resolved here where the canonical
                // arena is in scope (the id is not dereferenceable from the
                // supplemental arena).
                canonical_file_name: Some(
                    files.canonical.nodes[files.canonical.file]
                        .as_source_file()
                        .file_name()
                        .clone(),
                ),
            });
    }
    Ok(files)
}

/// `isModuleVirtualExtension` — `.mts`, `.cts`, `.mjs`, `.cjs`.
fn is_module_virtual_extension(extension: &str) -> bool {
    [
        tspath::EXTENSION_MTS,
        tspath::EXTENSION_CTS,
        tspath::EXTENSION_MJS,
        tspath::EXTENSION_CJS,
    ]
    .contains(&extension)
}

/// `func CheckSupplementalFileNameCollisions(files SourceFiles, fileExists) error`
///
/// Rejects compiler-assigned virtual filenames that name physical files.
pub fn check_supplemental_file_name_collisions(
    files: &SourceFiles,
    file_exists: impl Fn(&RootedFilePath) -> bool,
) -> std::result::Result<(), Error> {
    for file in &files.supplemental {
        if file_exists(file.file_name()) {
            return Err(Error::SupplementalFileCollision(
                SupplementalFileCollisionError {
                    file_name: file.file_name().clone(),
                },
            ));
        }
    }
    Ok(())
}
