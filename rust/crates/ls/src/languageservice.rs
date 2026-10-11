// Ported from tsc/internal/ls/languageservice.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(lifetimes): Go's `LanguageService` holds a `Host` interface value, a
// `*lsconv.Converters` owned by that host, and a `*compiler.Program`. Here the
// host is a borrowed `&'h dyn Host` and `converters: Converters<'h>` borrows
// the host's line-map storage, so the struct (and every `impl` block in
// sibling files) carries the `'h` lifetime: `impl<'h> LanguageService<'h>`.
// `program` is `Rc<Program>` — shared with the session. Go's
// `documentPositionMappers` caches `nil` results as well, hence `Option` in
// the map values.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use tsc_ast::NodeId;
use tsc_checker::checker_core::Checker;
use tsc_compiler::program::Program;
use tsc_lsconv::converters::Converters;
use tsc_lsproto::DocumentUri;
use tsc_lsutil::userpreferences_generated::{FormatCodeSettings, UserPreferences};
use tsc_sourcemap::{DocumentPositionMapper, EcmaLineInfo, get_document_position_mapper};
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::vfsmatch;

use crate::api::Error;
use crate::autoimport::{ProjectId, View};
use crate::completions::ERR_NEEDS_AUTO_IMPORTS;
use crate::host::Host;

/// `type LanguageService struct`
pub struct LanguageService<'h> {
    /// `projectID`.
    pub(crate) project_id: ProjectId,
    /// `host`.
    pub(crate) host: &'h dyn Host,
    /// `activeConfig`.
    pub(crate) active_config: UserPreferences,
    /// `program`.
    pub(crate) program: Rc<Program>,
    /// `converters`.
    pub(crate) converters: Converters<'h>,
    /// `documentPositionMappers` — caches negative (`None`) results too,
    /// matching Go's `map[PathKey]*DocumentPositionMapper` storing nil.
    pub(crate) document_position_mappers:
        RefCell<HashMap<PathKey, Option<Rc<DocumentPositionMapper>>>>,
}

/// `NewLanguageService`.
pub fn new_language_service<'h>(
    project_id: ProjectId,
    program: Rc<Program>,
    host: &'h dyn Host,
    active_file: &str,
) -> LanguageService<'h> {
    LanguageService {
        project_id,
        host,
        program,
        converters: host.converters(),
        active_config: host.get_preferences(active_file),
        document_position_mappers: RefCell::new(HashMap::new()),
    }
}

impl<'h> LanguageService<'h> {
    /// `GetProgram`.
    pub fn get_program(&self) -> Rc<Program> {
        self.program.clone()
    }

    /// `UserPreferences`.
    pub fn user_preferences(&self) -> &UserPreferences {
        &self.active_config
    }

    /// `FormatOptions`.
    pub fn format_options(&self) -> FormatCodeSettings {
        self.active_config.format_code_settings.clone()
    }

    /// `tryGetProgramAndFile` — `file` is the source file's `NodeId`
    /// (`*ast.SourceFile` → `NodeId`; index its arena via
    /// `program.nodes(file.file_index())`).
    pub(crate) fn try_get_program_and_file(
        &self,
        file_name: &RootedFilePath,
    ) -> (Rc<Program>, Option<NodeId>) {
        let program = self.get_program();
        let file = program.get_source_file(file_name);
        (program, file)
    }

    /// `getProgramAndFile`.
    pub(crate) fn get_program_and_file(&self, document_uri: &DocumentUri) -> (Rc<Program>, NodeId) {
        let file_name = document_uri.file_name();
        let (program, file) = self.try_get_program_and_file(&file_name);
        let Some(file) = file else {
            panic!("file not found: {}", file_name.as_string());
        };
        (program, file)
    }

    /// `GetDocumentPositionMapper`.
    pub fn get_document_position_mapper(
        &self,
        file_name: &RootedFilePath,
    ) -> Option<Rc<DocumentPositionMapper>> {
        let path = self.program.path_key_for_file_name(file_name);
        let cached = self.document_position_mappers.borrow().get(&path).cloned();
        if let Some(d) = cached {
            return d;
        }
        let d = get_document_position_mapper(self, file_name.clone()).map(Rc::new);
        self.document_position_mappers
            .borrow_mut()
            .insert(path, d.clone());
        d
    }

    /// `ReadFile` — implements `sourcemap.Host`.
    pub fn read_file(&self, file_name: &RootedFilePath) -> Option<String> {
        self.host.read_file(file_name)
    }

    /// `CaseSensitivity` — implements `sourcemap.Host`.
    pub fn case_sensitivity(&self) -> CaseSensitivity {
        self.host.case_sensitivity()
    }

    /// `GetECMALineInfo` — implements `sourcemap.Host`.
    pub fn get_ecma_line_info(&self, file_name: &RootedFilePath) -> Option<Rc<EcmaLineInfo>> {
        self.host.get_ecma_line_info(file_name)
    }

    /// `getPreparedAutoImportView` returns an auto-import view for the given
    /// file if the registry is prepared to provide up-to-date auto-imports
    /// for it. If not, it returns ErrNeedsAutoImports.
    ///
    /// PORT(deferred): `autoimport::View` is sibling-owned; reconcile the
    /// `View::new` argument list once it lands (`typeChecker` is passed as
    /// the `Rc<RefCell<Checker>>` pool handle).
    pub(crate) fn get_prepared_auto_import_view(
        &self,
        from_file: NodeId,
        type_checker: &Rc<RefCell<Checker>>,
    ) -> Result<Rc<View>, Error> {
        let registry = self.host.auto_import_registry();
        let mut registry_file = from_file;
        {
            let nodes = self.program.arena_of(from_file);
            if let Some(canonical) = nodes[from_file].as_source_file().canonical_source_file() {
                registry_file = canonical;
            }
        }
        let registry_file_name = {
            let nodes = self.program.arena_of(registry_file);
            nodes[registry_file].as_source_file().file_name().clone()
        };
        if !registry.is_prepared_for_importing_file(
            &registry_file_name,
            &self.project_id,
            self.user_preferences(),
        ) {
            return Err(ERR_NEEDS_AUTO_IMPORTS);
        }

        let view = View::new(
            registry,
            from_file,
            self.project_id.clone(),
            self.program.clone(),
            type_checker,
            self.user_preferences().clone(),
        );
        Ok(view)
    }

    /// `getCurrentAutoImportView` returns an auto-import view for the given
    /// file, based on the current state of the auto-import registry, which
    /// may or may not be up-to-date.
    ///
    /// PORT(deferred): see `get_prepared_auto_import_view`.
    pub(crate) fn get_current_auto_import_view(
        &self,
        from_file: NodeId,
        type_checker: &Rc<RefCell<Checker>>,
    ) -> Rc<View> {
        View::new(
            self.host.auto_import_registry(),
            from_file,
            self.project_id.clone(),
            self.program.clone(),
            type_checker,
            self.user_preferences().clone(),
        )
    }

    /// `DirectoryExists` — used for module specifier completions.
    pub fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.host.directory_exists(path)
    }

    /// `ReadDirectory` — used for module specifier completions.
    pub fn read_directory(
        &self,
        path: &RootedDirectoryPath,
        extensions: &[&str],
        includes: &[&str],
    ) -> Vec<RootedFilePath> {
        self.host.read_directory(
            path,
            extensions,
            &[], /*excludes*/
            includes,
            vfsmatch::UNLIMITED_DEPTH,
        )
    }

    /// `GetDirectories`.
    pub fn get_directories(&self, path: &RootedDirectoryPath) -> Vec<String> {
        self.host.get_directories(path)
    }
}

/// `LanguageService` implements `sourcemap.Host` — Go's
/// `GetDocumentPositionMapper(l, fileName)` passes the service itself.
impl tsc_sourcemap::Host for LanguageService<'_> {
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.host.case_sensitivity()
    }

    fn get_ecma_line_info(&self, file_name: &RootedFilePath) -> Option<Rc<EcmaLineInfo>> {
        self.host.get_ecma_line_info(file_name)
    }

    fn read_file(&self, file_name: &RootedFilePath) -> Option<String> {
        self.host.read_file(file_name)
    }
}
