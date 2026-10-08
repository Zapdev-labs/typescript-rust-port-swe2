// Ported from tsc/internal/printer/sourcefilemetadataprovider.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::SourceFileMetaData;
use tsc_tspath::PathKey;

/// `type SourceFileMetaDataProvider interface`
pub trait SourceFileMetaDataProvider {
    /// `GetSourceFileMetaData(path tspath.PathKey) *ast.SourceFileMetaData`
    fn get_source_file_meta_data(&self, path: PathKey) -> Option<&SourceFileMetaData>;
}
