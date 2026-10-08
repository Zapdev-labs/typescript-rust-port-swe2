// Ported from tsc/internal/tsoptions/parsedoptions.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_contentmapper::Mapper;
use tsc_core::options_generated::{CompilerOptions, TypeAcquisition};
use tsc_core::projectreference::ProjectReference;
use tsc_tspath::RootedFilePath;

/// `type ParsedOptions struct`.
///
/// PORT: `*core.CompilerOptions` / `*core.TypeAcquisition` /
/// `[]*core.ProjectReference` / `[]*contentmapper.Mapper` are all optional
/// in Go (nil); `Option` preserves that. `ContentMappers` elements are
/// `Arc<Mapper>` because `Mapper::equals` uses pointer identity (Go
/// `slices.EqualFunc` with `(*Mapper).Equals` compares `m == other` first).
#[derive(Clone, Default, Debug)]
pub struct ParsedOptions {
    /// `json:"compilerOptions"`
    pub compiler_options: Option<CompilerOptions>,
    /// `json:"typeAcquisition"`
    pub type_acquisition: Option<TypeAcquisition>,
    /// `json:"fileNames"`
    pub file_names: Vec<RootedFilePath>,
    /// `json:"projectReferences"`
    pub project_references: Vec<ProjectReference>,
    /// `json:"contentMappers"`
    pub content_mappers: Vec<Arc<Mapper>>,
}

impl ParsedOptions {
    /// `(p *ParsedOptions) Equals` — compares parsed configuration values
    /// using each option type's equality semantics.
    ///
    /// PORT: nil receivers become `Option<&ParsedOptions>` at the call
    /// boundary; `file_names == nil` vs `[]` is unobservable since the Rust
    /// field is a `Vec` (Go's `(p.FileNames == nil) == ...` check has no
    /// representation here — the nil-vs-empty distinction is not carried).
    // PORT: `FileNames`/`ProjectReferences`/`ContentMappers` nil-vs-empty is
    // not preserved (Go checks `(x == nil) == (y == nil)` separately); the
    // Rust fields are plain `Vec`s. `slices.EqualFunc` on nil receiver
    // segments is equivalent to `Vec` element-wise equality.
    pub fn equals(&self, other: &ParsedOptions) -> bool {
        if std::ptr::eq(self, other) {
            return true;
        }
        if !CompilerOptions::equals(
            self.compiler_options.as_ref(),
            other.compiler_options.as_ref(),
        ) || !TypeAcquisition::equals(
            self.type_acquisition.as_ref(),
            other.type_acquisition.as_ref(),
        ) {
            return false;
        }
        self.file_names == other.file_names
            && self.project_references == other.project_references
            && self.content_mappers.len() == other.content_mappers.len()
            && self
                .content_mappers
                .iter()
                .zip(other.content_mappers.iter())
                .all(|(a, b)| a.equals(b))
    }
}
