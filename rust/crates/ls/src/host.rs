// Ported from tsc/internal/ls/host.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::rc::Rc;

use tsc_lsconv::converters::Converters;
use tsc_lsutil::userpreferences_generated::UserPreferences;
use tsc_sourcemap::EcmaLineInfo;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath};

use crate::autoimport::Registry;

/// `type Host interface`
///
/// PORT: `Converters` returns an owned `Converters<'s>` borrowing the host's
/// line-map storage for `'s` (Go returns a `*lsconv.Converters` owned by the
/// host). Hosts that keep converters pre-built can return
/// `self.converters.clone()`; hosts that own the line maps build one on the
/// spot — the closure captures `&'s self`.
///
/// `AutoImportRegistry` likewise returns `&'s Registry` — the registry is a
/// shared, interior-mutable structure owned by the session (Go: `*Registry`).
pub trait Host {
    /// `CaseSensitivity() tspath.CaseSensitivity`.
    fn case_sensitivity(&self) -> CaseSensitivity;
    /// `ReadFile(path tspath.RootedFilePath) (contents string, ok bool)`.
    fn read_file(&self, path: &RootedFilePath) -> Option<String>;
    /// `Converters() *lsconv.Converters`.
    fn converters<'s>(&'s self) -> Converters<'s>;
    /// `GetPreferences(activeFile string) lsutil.UserPreferences`.
    fn get_preferences(&self, active_file: &str) -> UserPreferences;
    /// `GetECMALineInfo(fileName tspath.RootedFilePath) *sourcemap.ECMALineInfo`.
    fn get_ecma_line_info(&self, file_name: &RootedFilePath) -> Option<Rc<EcmaLineInfo>>;
    /// `AutoImportRegistry() *autoimport.Registry`.
    fn auto_import_registry<'s>(&'s self) -> &'s Registry;

    // Used for module specifier completions.
    // ! Do not use for anything else, as this violates the principle that
    // the host is a snapshot-in-time.

    /// `ReadDirectory(path tspath.RootedDirectoryPath, extensions []string, excludes []string, includes []string, depth int) []tspath.RootedFilePath`.
    /// Go's `nil` excludes slice maps to an empty `&[]`.
    fn read_directory(
        &self,
        path: &RootedDirectoryPath,
        extensions: &[&str],
        excludes: &[&str],
        includes: &[&str],
        depth: i64,
    ) -> Vec<RootedFilePath>;
    /// `GetDirectories(path tspath.RootedDirectoryPath) []string`.
    fn get_directories(&self, path: &RootedDirectoryPath) -> Vec<String>;
    /// `DirectoryExists(path tspath.RootedDirectoryPath) bool`.
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool;
    /// `FileExists(path tspath.RootedFilePath) bool`.
    fn file_exists(&self, path: &RootedFilePath) -> bool;
}
