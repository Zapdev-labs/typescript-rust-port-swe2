// Ported from tsc/internal/project/project.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// PORT(skeleton): pending full port.
//
// PORT(sibling): `project.go` is owned by the sibling session/project
// worker. The project-ID types, `Kind`, `ProgramUpdateKind`, `PendingReload`,
// and the `Project` field shell below are the minimum required by owned
// infrastructure (configfileregistry.rs, projectcollection.rs,
// snapshot.rs, compilerhost.rs). Project behavior (program creation,
// diagnostics, ATA, language service) is NOT ported here.

use std::rc::Rc;
use std::sync::{Arc, OnceLock};

use tsc_compiler::program::Program;
use tsc_collections::Set;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tspath::{
    PathKey, RootedDirectoryPath, RootedFilePath, try_path_key_from_canonical,
};

use crate::ata::TypingsInfo;
use crate::checkerpool::CheckerPool;
use crate::compilerhost::ProjectCompilerHost;
use crate::snapshot::ModuleResolverFactory;
use crate::watch::{PatternsAndIgnored, WatchedFiles};

/// `hr` — the log separator used by project/session logging.
pub const HR: &str = "-----------------------------------------------";

/// `inferredProjectName` — lowercase so canonicalization is a no-op
/// regardless of case sensitivity.
pub const INFERRED_PROJECT_NAME: &str = "/dev/null/inferred";
/// `syntheticProjectPrefix`.
pub const SYNTHETIC_PROJECT_PREFIX: &str = "/dev/null/synthetic/";

/// `type ID string` (project.go).
///
/// PORT: Go's `ID` is a plain string with methods (`Configured`,
/// `Inferred`, `Synthetic`); a newtype preserves that surface.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id(pub String);

impl Id {
    /// `ID.String()`.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// `id.Configured()` — a configured-project ID is the canonical
    /// `PathKey` of its config file.
    pub fn configured(&self) -> Option<ConfiguredProjectId> {
        let value = try_path_key_from_canonical(&self.0)?;
        parse_configured_project_id(&value)
    }

    /// `id.Inferred()`.
    pub fn inferred(&self) -> Option<InferredProjectId> {
        if self.0 == INFERRED_PROJECT_NAME {
            Some(InferredProjectId)
        } else {
            None
        }
    }

    /// `id.Synthetic()`.
    pub fn synthetic(&self) -> Option<SyntheticProjectId> {
        parse_synthetic_project_id(&self.0)
    }
}

impl From<String> for Id {
    fn from(s: String) -> Self {
        Id(s)
    }
}

impl From<&str> for Id {
    fn from(s: &str) -> Self {
        Id(s.to_string())
    }
}

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// `type ConfiguredProjectID struct` — identifies a configured project by
/// the `PathKey` of its config file.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConfiguredProjectId {
    path_key: PathKey,
}

impl ConfiguredProjectId {
    /// `id.PathKey()`.
    pub fn path_key(&self) -> &PathKey {
        &self.path_key
    }
    /// `id.AsID()`.
    pub fn as_id(&self) -> Id {
        Id(self.path_key.as_string().to_string())
    }
}

impl std::fmt::Display for ConfiguredProjectId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.path_key.as_string())
    }
}

/// `ParseConfiguredProjectID`.
pub fn parse_configured_project_id(value: &PathKey) -> Option<ConfiguredProjectId> {
    let id = Id(value.as_string().to_string());
    if id.0.is_empty() {
        return None;
    }
    if id.inferred().is_some() {
        return None;
    }
    if id.synthetic().is_some() {
        return None;
    }
    Some(ConfiguredProjectId {
        path_key: value.clone(),
    })
}

/// `ConfiguredProjectIDFromPathKey` — panics on invalid IDs like Go.
pub fn configured_project_id_from_path_key(value: &PathKey) -> ConfiguredProjectId {
    parse_configured_project_id(value)
        .unwrap_or_else(|| panic!("invalid configured project ID: {}", value.as_string()))
}

/// `type InferredProjectID string` — `inferredProjectID` is the single
/// inferred-project ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InferredProjectId;

impl InferredProjectId {
    /// `id.AsID()`.
    pub fn as_id(&self) -> Id {
        Id(INFERRED_PROJECT_NAME.to_string())
    }
}

/// `type SyntheticProjectID string` — identifies a project created
/// explicitly through the API (`createProgram`).
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntheticProjectId(pub String);

impl SyntheticProjectId {
    /// `id.AsID()`.
    pub fn as_id(&self) -> Id {
        Id(self.0.clone())
    }
}

impl std::fmt::Display for SyntheticProjectId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// `NewSyntheticProjectID` — panics on non-positive ids like Go.
pub fn new_synthetic_project_id(id: i64) -> SyntheticProjectId {
    if id <= 0 {
        panic!("invalid synthetic project ID: {id}");
    }
    SyntheticProjectId(format!("{SYNTHETIC_PROJECT_PREFIX}{id}"))
}

/// `ParseSyntheticProjectID`.
pub fn parse_synthetic_project_id(value: &str) -> Option<SyntheticProjectId> {
    let suffix = value.strip_prefix(SYNTHETIC_PROJECT_PREFIX)?;
    let id: i64 = suffix.parse().ok()?;
    if id <= 0 {
        return None;
    }
    Some(new_synthetic_project_id(id))
}

/// `type Kind int` (project.go).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Kind {
    #[default]
    Inferred,
    Configured,
    Synthetic,
}

/// `type ProgramUpdateKind int` (project.go).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ProgramUpdateKind {
    #[default]
    None,
    Cloned,
    SameFileNames,
    NewFiles,
}

/// `type PendingReload int` (project.go).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum PendingReload {
    #[default]
    None = 0,
    FileNames = 1,
    Full = 2,
}

/// `Project` (project.go).
///
/// PORT(sibling): field shell carrying the state the snapshot layer reads
/// (`program`, `program_last_update`, `program_update_kind`,
/// `content_mapper_watched_files`, `checker_pool`, `host`, `command_line`)
/// plus the remaining fields of the Go struct as inert storage. The sibling
/// project port supplies constructors and behavior.
pub struct Project {
    /// `Kind`.
    pub kind: Kind,
    /// `id`.
    pub id: Id,
    /// `projectDirectory`.
    pub project_directory: RootedDirectoryPath,
    /// `configFileName`.
    pub config_file_name: RootedFilePath,
    /// `configFilePath`.
    pub config_file_path: PathKey,

    /// `dirty`.
    pub dirty: bool,
    /// `dirtyFilePath`.
    pub dirty_file_path: PathKey,

    /// `host *compilerHost` — erased over the concrete
    /// `CompilerHostWrapper<B, P>` via [`ProjectCompilerHost`].
    pub host: Option<Arc<dyn ProjectCompilerHost>>,
    /// `CommandLine`.
    pub command_line: Option<Arc<ParsedCommandLine>>,
    /// `commandLineWithTypingsFilesOnce` — `commandLineWithTypingsFiles` is
    /// computed lazily by the sibling project port.
    pub command_line_with_typings_files: OnceLock<Option<Arc<ParsedCommandLine>>>,
    /// `Program`.
    pub program: Option<Rc<Program>>,
    /// `ProgramUpdateKind` — the kind of update performed on the program the
    /// last time it was updated.
    pub program_update_kind: ProgramUpdateKind,
    /// `ProgramLastUpdate` — the ID of the snapshot that created the
    /// program stored in this project.
    pub program_last_update: u64,
    /// `potentialProjectReferences` — set of projects that this project
    /// could be referencing; only set before actually loading the config
    /// file to get actual project references.
    pub potential_project_references: Option<Set<PathKey>>,

    /// `programFilesWatch`.
    pub program_files_watch: Option<
        Arc<WatchedFiles<Arc<tsc_collections::SyncMap<PathKey, RootedFilePath>>>>,
    >,
    /// `typingsWatch`.
    pub typings_watch: Option<Arc<WatchedFiles<PatternsAndIgnored>>>,
    /// `contentMapperWatch`.
    pub content_mapper_watch: Option<Arc<WatchedFiles<Vec<RootedFilePath>>>>,
    /// `contentMapperWatchedFiles`.
    pub content_mapper_watched_files: Option<Set<PathKey>>,

    /// `checkerPool`.
    pub checker_pool: Option<CheckerPool>,

    /// `moduleResolverFactory`.
    pub module_resolver_factory: Option<Arc<dyn ModuleResolverFactory>>,
    /// `moduleResolverID`.
    pub module_resolver_id: u64,

    /// `installedTypingsInfo` — the value of `project.ComputeTypingsInfo()`
    /// used during the most recently completed typings installation.
    pub installed_typings_info: Option<Arc<TypingsInfo>>,
    /// `typingsFiles` — the root files added by the typings installer.
    pub typings_files: Vec<RootedFilePath>,
}

impl Project {
    /// `p.ID()`.
    pub fn id(&self) -> &Id {
        &self.id
    }

    /// `p.Id()`.
    pub fn id_str(&self) -> &str {
        self.id.as_str()
    }

    /// `p.ConfigFileName()` — panics if `kind` is not `Kind::Configured`.
    pub fn config_file_name(&self) -> &RootedFilePath {
        if self.kind != Kind::Configured {
            panic!("ConfigFileName called on non-configured project");
        }
        &self.config_file_name
    }

    /// `p.ConfigFilePath()` — panics if `kind` is not `Kind::Configured`.
    pub fn config_file_path(&self) -> &PathKey {
        if self.kind != Kind::Configured {
            panic!("ConfigFilePath called on non-configured project");
        }
        &self.config_file_path
    }

    /// `p.GetProgram()`.
    pub fn get_program(&self) -> Option<&Rc<Program>> {
        self.program.as_ref()
    }

    /// `p.IsDirty()`.
    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// `p.HasFile` — `p.host.FS().CaseSensitivity().PathKey(...)`.
    pub fn has_file(&self, file_name: &RootedFilePath) -> bool {
        let Some(host) = &self.host else {
            return false;
        };
        self.contains_file(&host.fs().case_sensitivity().path_key(&file_name.as_path()))
    }

    /// `p.containsFile`.
    pub fn contains_file(&self, path: &PathKey) -> bool {
        self.program
            .as_ref()
            .is_some_and(|p| p.get_source_file_by_path(path).is_some())
    }

    /// `p.IsSourceFromProjectReference`.
    pub fn is_source_from_project_reference(&self, path: &PathKey) -> bool {
        self.program
            .as_ref()
            .is_some_and(|p| p.is_source_from_project_reference(path))
    }

    /// `p.DisplayName` — a short, human-readable name for the project,
    /// relative to the given workspace root directory. For configured
    /// projects, this is the config file path made relative; for inferred
    /// projects, the last component of the project directory.
    pub fn display_name(&self, cwd: &RootedDirectoryPath) -> String {
        if self.kind == Kind::Inferred {
            return self.project_directory.base_name().to_string();
        }
        let mut name = tsc_tspath::rooted_file_path_from_normalized(&self.id.0);
        if self.kind == Kind::Configured {
            name = self.config_file_name.clone();
        }
        if let Some(relative_path) = tsc_tspath::CaseSensitivity::CaseInsensitive
            .relative_path_from_directory(cwd, &name)
        {
            return relative_path.as_string().to_string();
        }
        name.as_string().to_string()
    }

    /// `p.GetProjectDiagnostics` — program diagnostics combined with any
    /// global diagnostics discovered during checking; reported on the
    /// tsconfig.json file.
    pub fn get_project_diagnostics(&self) -> Vec<tsc_ast::diagnostic::DiagnosticRef> {
        let mut global_diags = Vec::new();
        if let Some(pool) = &self.checker_pool {
            global_diags = pool.get_global_diagnostics();
        }
        let mut all = Vec::new();
        if let Some(program) = &self.program {
            all.extend(program.get_config_file_parsing_diagnostics());
            all.extend(program.get_program_diagnostics());
        }
        all.extend(global_diags);
        tsc_compiler::checker_pool::sort_and_deduplicate_diagnostics(all)
    }

    /// `p.GetTypeAcquisition` — inferred/synthetic projects use default
    /// settings; configured projects read their command line.
    pub fn get_type_acquisition(&self) -> Option<tsc_core::options_generated::TypeAcquisition> {
        if self.kind == Kind::Inferred || self.kind == Kind::Synthetic {
            return Some(tsc_core::options_generated::TypeAcquisition {
                enable: tsc_core::tristate::TS_TRUE,
                include: None,
                exclude: None,
                disable_filename_based_type_acquisition: tsc_core::tristate::TS_FALSE,
            });
        }
        self.command_line
            .as_ref()
            .and_then(|cl| cl.type_acquisition().cloned())
    }

    /// `p.GetUnresolvedImports`.
    pub fn get_unresolved_imports(&self) -> Option<Set<String>> {
        let program = self.program.as_ref()?;
        Some(tsc_collections::new_set_from_items(
            program.get_unresolved_imports().iter().cloned(),
        ))
    }

    /// `p.ComputeTypingsInfo`.
    pub fn compute_typings_info(&self) -> TypingsInfo {
        TypingsInfo {
            compiler_options: self
                .command_line
                .as_ref()
                .and_then(|cl| cl.compiler_options().cloned())
                .map(Arc::new)
                .unwrap_or_default(),
            type_acquisition: self
                .get_type_acquisition()
                .map(Arc::new)
                .unwrap_or_default(),
            unresolved_imports: self.get_unresolved_imports(),
        }
    }

    /// `p.ShouldTriggerATA` — whether ATA should be triggered for this
    /// project at `snapshot_id`.
    pub fn should_trigger_ata(&self, snapshot_id: u64) -> bool {
        if self.program.is_none() || self.command_line.is_none() {
            return false;
        }
        let Some(type_acquisition) = self.get_type_acquisition() else {
            return false;
        };
        if !type_acquisition.enable.is_true() {
            return false;
        }
        if self.installed_typings_info.is_none()
            || (self.program_last_update == snapshot_id
                && self.program_update_kind == ProgramUpdateKind::NewFiles)
        {
            return true;
        }
        !self
            .installed_typings_info
            .as_ref()
            .is_some_and(|info| info.equals(&self.compute_typings_info()))
    }

    /// `p.print` — logs the project header plus, when `write_file_names`,
    /// the list of source files (Go's `writeFileExplanation` is a `// !!!`
    /// no-op there too).
    pub fn print(&self, write_file_names: bool, _write_file_explanation: bool) -> String {
        let mut builder = String::new();
        builder.push_str(&format!("\nProject '{}'\n", self.id));
        match &self.program {
            None => builder.push_str("\tFiles (0) NoProgram\n"),
            Some(program) => {
                let source_files = program.source_files();
                builder.push_str(&format!("\tFiles ({})\n", source_files.len()));
                if write_file_names {
                    for source_file in source_files {
                        let nodes = program.nodes(source_file.file_index());
                        let file_name = nodes[source_file]
                            .as_source_file()
                            .file_name()
                            .clone();
                        builder.push_str("\t\t");
                        builder.push_str(file_name.as_string());
                        builder.push('\n');
                    }
                }
            }
        }
        builder.push_str(HR);
        builder
    }
}
