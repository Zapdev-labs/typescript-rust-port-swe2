// Ported from tsc/internal/printer/emithost.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// NOTE: EmitHost operations must be thread-safe

use tsc_ast::SourceFile;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::options_generated::ModuleKind;
use tsc_tsoptions::parsedcommandline::SourceOutputAndProjectReference;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};

use crate::emit_context::EmitContext;
use crate::emit_resolver::EmitResolver;

/// `type EmitHost interface`
///
/// NOTE: EmitHost operations must be thread-safe
///
/// PORT: `WriteFile` returns `std::io::Result<()>` in place of Go's `error`.
/// `NewEmitResolver` returns `Box<dyn EmitResolver>` since Go returns the
/// interface.
pub trait EmitHost {
    /// `Options() *core.CompilerOptions`
    fn options(&self) -> &CompilerOptions;
    /// `SourceFiles() []*ast.SourceFile`
    fn source_files(&self) -> &[SourceFile];
    /// `CaseSensitivity() tspath.CaseSensitivity`
    fn case_sensitivity(&self) -> CaseSensitivity;
    /// `CommonSourceDirectory() tspath.RootedDirectoryPath`
    fn common_source_directory(&self) -> &RootedDirectoryPath;
    /// `IsEmitBlocked(file tspath.RootedFilePath) bool`
    fn is_emit_blocked(&self, file: &RootedFilePath) -> bool;
    /// `WriteFile(fileName tspath.RootedFilePath, text string) error`
    fn write_file(&self, file_name: &RootedFilePath, text: &str) -> std::io::Result<()>;
    /// `GetEmitModuleFormatOfFile(file ast.HasFileName) core.ModuleKind`
    fn get_emit_module_format_of_file(&self, file: &SourceFile) -> ModuleKind;
    /// `NewEmitResolver(emitContext *EmitContext) EmitResolver`
    fn new_emit_resolver(&self, emit_context: &EmitContext) -> Box<dyn EmitResolver + '_>;
    /// `GetProjectReferenceFromSource(path tspath.PathKey) *tsoptions.SourceOutputAndProjectReference`
    fn get_project_reference_from_source(
        &self,
        path: PathKey,
    ) -> Option<&SourceOutputAndProjectReference>;
    /// `IsSourceFileFromExternalLibrary(file *ast.SourceFile) bool`
    fn is_source_file_from_external_library(&self, file: &SourceFile) -> bool;
}
