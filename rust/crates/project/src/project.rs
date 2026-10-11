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
}
