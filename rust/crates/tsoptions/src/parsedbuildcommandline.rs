// Ported from tsc/internal/tsoptions/parsedbuildcommandline.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::OnceLock;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_core::core;
use tsc_core::options_generated::{BuildOptions, CompilerOptions};
use tsc_core::projectreference::resolve_config_file_name_of_project_reference;
use tsc_locale::Locale;
use tsc_tspath::{RootedDirectoryPath, RootedFilePath};

use crate::value::Value;

/// `type ParsedBuildCommandLine struct`.
///
/// PORT: each Go `sync.Once` + field pair becomes a `OnceLock`.
#[derive(Default)]
pub struct ParsedBuildCommandLine {
    /// `BuildOptions *core.BuildOptions`
    pub build_options: Option<BuildOptions>,
    /// `CompilerOptions *core.CompilerOptions`
    pub compiler_options: Option<CompilerOptions>,
    /// `Projects []string`
    pub projects: Vec<String>,
    /// `Errors []*ast.Diagnostic`
    pub errors: Vec<DiagnosticRef>,
    /// `Raw any`
    pub raw: Option<Value>,

    /// `currentDirectory`
    pub current_directory: RootedDirectoryPath,

    pub(crate) resolved_project_paths: OnceLock<Vec<RootedFilePath>>,

    pub(crate) locale: OnceLock<Locale>,
}

impl ParsedBuildCommandLine {
    /// `(p *ParsedBuildCommandLine) ResolvedProjectPaths`.
    pub fn resolved_project_paths(&self) -> &Vec<RootedFilePath> {
        self.resolved_project_paths.get_or_init(|| {
            core::map(&self.projects, |project| {
                resolve_config_file_name_of_project_reference(
                    &self.current_directory.resolve_file(project).as_path(),
                )
            })
        })
    }

    /// `(p *ParsedBuildCommandLine) Locale`.
    ///
    /// PORT: Go dereferences `p.CompilerOptions.Locale` directly (panics on
    /// nil); the `Option` unwrap mirrors that — callers always set
    /// `compiler_options` during parsing.
    pub fn locale(&self) -> &Locale {
        self.locale.get_or_init(|| {
            tsc_locale::parse(
                &self
                    .compiler_options
                    .as_ref()
                    .expect("compiler_options")
                    .locale,
            )
            .0
        })
    }
}
