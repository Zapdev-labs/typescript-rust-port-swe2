// Ported from tsc/internal/transformers/declarations/supplementalreferences.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// SupplementalReferencesTransformer adds triple-slash path references from a
// content mapper's canonical declaration output to the declaration files
// emitted for its supplemental files. This ensures that consumers loading
// the canonical declaration also include the supplemental types.
//
// PORT: `*ast.SourceFile` → the SourceFile node's `NodeId`. The Go type is
// not a `transformers.Transformer` (it mutates `ReferencedFiles` in place);
// the Rust port mirrors that — it mutates the arena directly rather than
// using a `NodeVisitor`.

use std::rc::Rc;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::{FileReference, Node, NodeId};
use tsc_core::options_generated::ModuleKind;
use tsc_core::text::TextRange;
use tsc_tspath::RootedFilePath;

use crate::declarations::host::DeclarationEmitHost;

/// `type SupplementalReferencesTransformer struct`.
pub struct SupplementalReferencesTransformer<'a> {
    /// `host`.
    host: Rc<dyn DeclarationEmitHost + 'a>,
    /// `supplementalFiles` — NodeIds of the canonical file's supplemental
    /// source files.
    supplemental_files: Vec<NodeId>,
    /// `declarationFilePath` — the canonical declaration output path.
    declaration_file_path: RootedFilePath,
    /// `forceDeclarationPaths`.
    force_declaration_paths: bool,
}

impl<'a> SupplementalReferencesTransformer<'a> {
    /// `NewSupplementalReferencesTransformer(host, sourceFile, declarationFilePath, forceDeclarationPaths)`.
    pub fn new(
        host: Rc<dyn DeclarationEmitHost + 'a>,
        source_file: NodeId,
        declaration_file_path: RootedFilePath,
        force_declaration_paths: bool,
        nodes: &[Node],
    ) -> SupplementalReferencesTransformer<'a> {
        SupplementalReferencesTransformer {
            host,
            supplemental_files: nodes[source_file]
                .as_source_file()
                .supplemental_source_files()
                .to_vec(),
            declaration_file_path,
            force_declaration_paths,
        }
    }

    /// `(t *SupplementalReferencesTransformer) TransformSourceFile` —
    /// mutates `sourceFile`'s `referenced_files` in place, like the Go
    /// implementation (which appends to `sourceFile.ReferencedFiles`).
    pub fn transform_source_file(&self, source_file: NodeId, nodes: &mut Vec<Node>) -> NodeId {
        for &supplemental in &self.supplemental_files {
            if !self.host.source_file_may_be_emitted(
                supplemental,
                self.force_declaration_paths,
                nodes,
            ) {
                continue;
            }
            let Some(paths) =
                self.host
                    .get_output_paths_for(supplemental, self.force_declaration_paths, nodes)
            else {
                continue;
            };
            let declaration_path = paths.declaration_file_path();
            if declaration_path.as_string().is_empty() {
                continue;
            }
            let Some(relative_path) = self
                .host
                .case_sensitivity()
                .relative_path_from_file(&self.declaration_file_path, declaration_path)
            else {
                panic!(
                    "supplemental declaration output must share a root with the primary declaration"
                )
            };
            // `referenced_files` is a `Box<[FileReference]>` — rebuild it
            // like Go's `append`.
            let mut referenced_files = nodes[source_file]
                .as_source_file()
                .referenced_files
                .to_vec();
            referenced_files.push(FileReference {
                text_range: TextRange::new(-1, -1),
                file_name: relative_path.as_module_specifier().as_string().to_string(),
                resolution_mode: ModuleKind::None,
                preserve: false,
            });
            nodes[source_file].as_source_file_mut().referenced_files =
                referenced_files.into_boxed_slice();
        }
        source_file
    }

    /// `(t *SupplementalReferencesTransformer) GetDiagnostics`.
    pub fn get_diagnostics(&self) -> Vec<DiagnosticRef> {
        Vec::new()
    }
}
