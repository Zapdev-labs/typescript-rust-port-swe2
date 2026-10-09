// Ported from the `DeclarationEmitHost`/`OutputPaths` interfaces in
// tsc/internal/transformers/declarations/transform.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//   - Go's `DeclarationEmitHost` embeds
//     `modulespecifiers.ModuleSpecifierGenerationHost`. The modulespecifiers
//     package is not ported yet, so this trait carries only the members
//     declared directly on `DeclarationEmitHost`; module-specifier
//     generation flows through `EmitResolver` methods instead. When the
//     modulespecifiers port lands, embed its host trait here.
//   - `OutputPaths` is the concrete `tsc_outputpaths::OutputPaths` struct
//     rather than an interface — it has the same `declaration_file_path()` /
//     `js_file_path()` accessors.
//   - `*ast.SourceFile` → the SourceFile node's `NodeId`; `ref` is borrowed
//     from the SourceFile's `referenced_files` slice.

use tsc_ast::{FileReference, Node, NodeId};
use tsc_outputpaths::OutputPaths;
use tsc_tspath::CaseSensitivity;

/// `type DeclarationEmitHost interface`.
pub trait DeclarationEmitHost {
    /// `CaseSensitivity() tspath.CaseSensitivity`.
    fn case_sensitivity(&self) -> CaseSensitivity;

    /// `GetSourceFileFromReference(origin *ast.SourceFile, ref *ast.FileReference) *ast.SourceFile`.
    /// `None` mirrors Go nil.
    fn get_source_file_from_reference(
        &self,
        origin: NodeId,
        ref_: &FileReference,
        nodes: &[Node],
    ) -> Option<NodeId>;

    /// `GetOutputPathsFor(file *ast.SourceFile, forceDtsPaths bool) OutputPaths`.
    fn get_output_paths_for(
        &self,
        file: NodeId,
        force_dts_paths: bool,
        nodes: &[Node],
    ) -> Option<OutputPaths>;

    /// `SourceFileMayBeEmitted(file *ast.SourceFile, forceDtsEmit bool) bool`.
    fn source_file_may_be_emitted(
        &self,
        file: NodeId,
        force_dts_emit: bool,
        nodes: &[Node],
    ) -> bool;
}
