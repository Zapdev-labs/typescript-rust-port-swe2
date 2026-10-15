// Ported from tsc/internal/project/project.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Project-ID types, `Kind`, `ProgramUpdateKind`, `PendingReload`, the
// `Project` fields, and its lifecycle: constructors, `clone_project`,
// `set_command_line`, `clone_watchers`, `create_program`, potential
// project references, and typings accessors.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, OnceLock};

use tsc_collections::{Set, SyncMap};
use tsc_compiler::program::{
    Program, ProgramConfig, ProgramFactories, ProgramHosts, ProgramOptions,
    new_program, update_program,
};
use tsc_contentmapper::Mapper;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::projectreference::ProjectReference;
use tsc_core::tristate::TS_TRUE;
use tsc_dirty::Cloneable;
use tsc_lsproto::WatchKind;
use tsc_module::{DefaultResolver, Resolver, ResolverOptions};
use tsc_project_logging::{LogTree, Logger};
use tsc_tsoptions::parsedcommandline::{
    ParsedCommandLine, new_parsed_command_line_opt,
};
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath,
    try_path_key_from_canonical,
};

use crate::ata::TypingsInfo;
use crate::checkerpool::{CheckerPool, new_checker_pool};
use crate::compilerhost::ProjectCompilerHost;
use crate::parsecache::{
    content_mapped_parse_cache_key_for_duplicate,
    content_mapped_parse_cache_key_for_file, parse_cache_key_for_duplicate,
    parse_cache_key_for_file,
};
use crate::projectcollectionbuilder::ProjectCollectionBuilder;
use crate::snapshot::{ModuleResolverFactory, ProjectTreeRequest};
use crate::watch::{
    PatternsAndIgnored, WatchedFiles, create_resolution_lookup_glob_mapper,
    new_watched_files, new_watched_files_for_paths,
};

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

    /// `programFilesWatch` — input is `sourceFS.seenFiles` (Go `*SyncMap`,
    /// nil before the first program is built → `None`).
    pub program_files_watch: Option<
        Arc<WatchedFiles<Option<Arc<SyncMap<PathKey, RootedFilePath>>>>>,
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

/// `Kind.String`.
impl Kind {
    /// `func (k Kind) String() string`.
    pub fn as_str(&self) -> &'static str {
        match self {
            Kind::Inferred => "inferred ",
            Kind::Configured => "configured ",
            Kind::Synthetic => "synthetic ",
        }
    }
}

/// Copy the value of a `OnceLock` into a fresh one (Go copies the raw field).
fn clone_once_lock<T: Clone>(src: &OnceLock<T>) -> OnceLock<T> {
    match src.get() {
        Some(v) => OnceLock::from(v.clone()),
        None => OnceLock::new(),
    }
}

impl Project {
    /// `p.Clone()` — Go's `Clone()` resets `ProgramUpdateKind` to
    /// `ProgramUpdateKindNone`.
    fn clone_project(&self) -> Project {
        Project {
            kind: self.kind,
            id: self.id.clone(),
            project_directory: self.project_directory.clone(),
            config_file_name: self.config_file_name.clone(),
            config_file_path: self.config_file_path.clone(),
            dirty: self.dirty,
            dirty_file_path: self.dirty_file_path.clone(),
            host: self.host.clone(),
            command_line: self.command_line.clone(),
            command_line_with_typings_files: clone_once_lock(
                &self.command_line_with_typings_files,
            ),
            program: self.program.clone(),
            program_update_kind: ProgramUpdateKind::None,
            program_last_update: self.program_last_update,
            potential_project_references: self.potential_project_references.clone(),
            program_files_watch: self.program_files_watch.clone(),
            typings_watch: self.typings_watch.clone(),
            content_mapper_watch: self.content_mapper_watch.clone(),
            content_mapper_watched_files: self.content_mapper_watched_files.clone(),
            checker_pool: None,
            module_resolver_factory: self.module_resolver_factory.clone(),
            module_resolver_id: self.module_resolver_id,
            installed_typings_info: self.installed_typings_info.clone(),
            typings_files: self.typings_files.clone(),
        }
    }

    /// `p.SetCommandLine` — reassigns the project's command line and resets
    /// all state derived from it. Changing the command line always requires
    /// a full program rebuild, so the project is marked fully dirty.
    pub fn set_command_line(&mut self, command_line: Arc<ParsedCommandLine>) {
        self.command_line = Some(command_line);
        self.command_line_with_typings_files = OnceLock::new();
        self.potential_project_references = None;
        self.dirty = true;
        self.dirty_file_path = PathKey::default();
    }

    /// `p.getCommandLineWithTypingsFiles` — the command line augmented with
    /// typing files if ATA is enabled.
    pub fn get_command_line_with_typings_files(&self) -> Arc<ParsedCommandLine> {
        if self.typings_files.is_empty() {
            return self.command_line.clone().expect("command line not set");
        }
        let type_acquisition = self.get_type_acquisition();
        if !type_acquisition
            .as_ref()
            .is_some_and(|ta| ta.enable.is_true())
        {
            return self.command_line.clone().expect("command line not set");
        }
        self.command_line_with_typings_files
            .get_or_init(|| {
                let command_line =
                    self.command_line.as_ref().expect("command line not set");
                let mut new_root_names =
                    Vec::with_capacity(command_line.file_names().len() + self.typings_files.len());
                new_root_names.extend_from_slice(command_line.file_names());
                new_root_names.extend(self.typings_files.iter().cloned());
                Some(Arc::new(command_line.with_file_names(new_root_names)))
            })
            .clone()
            .expect("command line with typings files not set")
    }

    /// `p.setPotentialProjectReference`.
    pub fn set_potential_project_reference(&mut self, config_file_path: PathKey) {
        match &mut self.potential_project_references {
            None => {
                let mut set = Set::new();
                set.add(config_file_path);
                self.potential_project_references = Some(set);
            }
            Some(set) => {
                let mut set = set.clone();
                set.add(config_file_path);
                self.potential_project_references = Some(set);
            }
        }
    }

    /// `p.hasPotentialProjectReference`.
    pub fn has_potential_project_reference(
        &self,
        project_tree_request: &ProjectTreeRequest,
    ) -> bool {
        if let Some(command_line) = &self.command_line {
            let case_sensitivity = self
                .host
                .as_ref()
                .expect("host not set")
                .fs()
                .case_sensitivity();
            for path in command_line.resolved_project_reference_paths() {
                if project_tree_request.is_project_referenced(
                    &case_sensitivity.path_key(&path.as_path()),
                ) {
                    return true;
                }
            }
        } else if let Some(references) = &self.potential_project_references {
            for path in references.keys() {
                if project_tree_request.is_project_referenced(path) {
                    return true;
                }
            }
        }
        false
    }

    /// `p.CurrentDirectory`.
    pub fn current_directory(&self) -> RootedDirectoryPath {
        self.project_directory.clone()
    }

    /// `p.CloneWatchers`.
    pub fn clone_watchers(
        &self,
    ) -> Arc<WatchedFiles<Option<Arc<SyncMap<PathKey, RootedFilePath>>>>> {
        let host = self.host.as_ref().expect("host not set");
        self.program_files_watch
            .as_ref()
            .expect("program files watch not set")
            .clone_with(Some(host.source_fs().seen_files()))
    }

    /// `p.CreateProgram`.
    pub fn create_program(&mut self) -> CreateProgramResult {
        let host = self.host.as_ref().expect("host not set");
        let mut update_kind = ProgramUpdateKind::NewFiles;
        let mut program_cloned = false;

        let checker_pool_options = host.session_options().checker_pool_options.clone();
        // Go reads `result.Program.GetCheckerPool().(*checkerPool)` after
        // `CreateProgram` — the erased `Rc<dyn CheckerPool>` can't downcast,
        // so the factory captures the concrete pool it hands the program.
        let created_checker_pool: Rc<RefCell<Option<CheckerPool>>> =
            Rc::new(RefCell::new(None));
        let created_checker_pool_slot = Rc::clone(&created_checker_pool);
        let create_checker_pool: Arc<
            dyn Fn(&Rc<Program>) -> Rc<dyn tsc_compiler::checker_pool::CheckerPool>,
        > = Arc::new(move |program| {
            let pool = new_checker_pool(
                checker_pool_options.clone(),
                program.clone() as Rc<dyn tsc_checker::checker_types::Program>,
                None, /* p.log — Go's `// !!!` stub */
            );
            *created_checker_pool_slot.borrow_mut() = Some(pool.clone());
            Rc::new(pool)
        });
        let module_resolver_factory = self.module_resolver_factory.clone();
        let builder_ctx = host.builder_ctx();
        let cleanup_module_resolver: Rc<RefCell<Option<Box<dyn FnOnce() + Send>>>> =
            Rc::new(RefCell::new(None));
        let cleanup_slot = Rc::clone(&cleanup_module_resolver);
        let create_module_resolver: Arc<dyn Fn(ResolverOptions) -> Arc<dyn Resolver>> =
            Arc::new(move |options| match &module_resolver_factory {
                None => Arc::new(DefaultResolver::new(options)),
                Some(factory) => {
                    let (resolver, cleanup) = factory.new_resolver(&builder_ctx, options);
                    *cleanup_slot.borrow_mut() = Some(cleanup);
                    resolver
                }
            });

        let parse_cache = host.parse_cache();
        let content_mapped_parse_cache = host.content_mapped_parse_cache();

        // Create the command line, potentially augmented with typing files.
        let command_line = self.get_command_line_with_typings_files();
        let mut new_program_rc: Rc<Program>;
        let mut dirty_file = None;
        if !self.dirty_file_path.is_empty()
            && self.program.is_some()
            && self
                .program
                .as_ref()
                .is_some_and(|p| Arc::ptr_eq(p.command_line(), &command_line))
        {
            let (updated, dirty, cloned) = update_program(
                self.program.as_ref().unwrap(),
                &self.dirty_file_path,
                host.compiler_host(),
                Some(create_checker_pool.clone()),
                Some(create_module_resolver.clone()),
            );
            new_program_rc = updated;
            dirty_file = dirty;
            program_cloned = cloned;
            if program_cloned {
                update_kind = ProgramUpdateKind::Cloned;
                // Use the dirty file's arena + NodeId: `update_program`
                // acquired the changed file only; everything else needs a
                // ref. (`d.nodes` is the same allocation `arena_of` hands
                // out for the dirty file.)
                let dirty_arena = dirty_file
                    .as_ref()
                    .map(|d| (new_program_rc.arena_of(d.file), d.file));
                for &file in new_program_rc.source_files_slice() {
                    let nodes = new_program_rc.arena_of(file);
                    let source_file = nodes[file].as_source_file();
                    let is_dirty_file = dirty_arena.as_ref().is_some_and(
                        |(arena, dirty_id)| {
                            *dirty_id == file && Rc::ptr_eq(arena, &nodes)
                        },
                    );
                    if !is_dirty_file
                        && !source_file.is_content_mapper_failure_stub()
                        && !source_file.is_content_mapper_supplemental()
                    {
                        if !source_file.content_mapper().is_empty() {
                            content_mapped_parse_cache.ref_(
                                &content_mapped_parse_cache_key_for_file(&nodes, file),
                            );
                        } else {
                            parse_cache.ref_(&parse_cache_key_for_file(&nodes, file));
                        }
                    }
                }
                for file in new_program_rc.duplicate_source_files() {
                    if !file.is_content_mapper_failure_stub {
                        if !file.content_mapper.is_empty() {
                            content_mapped_parse_cache.ref_(
                                &content_mapped_parse_cache_key_for_duplicate(file),
                            );
                        } else {
                            parse_cache.ref_(&parse_cache_key_for_duplicate(file));
                        }
                    }
                }
            } else if let Some(dirty) = &dirty_file {
                // `update_program` always acquires the dirty file before
                // deciding whether it can reuse the old program. If it falls
                // back to a full rebuild, release that speculative acquire.
                let nodes = dirty.nodes.snapshot();
                let source_file = nodes[dirty.file].as_source_file();
                if !source_file.content_mapper().is_empty() {
                    content_mapped_parse_cache.deref(
                        &content_mapped_parse_cache_key_for_file(&nodes, dirty.file),
                    );
                } else {
                    parse_cache.deref(&parse_cache_key_for_file(&nodes, dirty.file));
                }
            }
        } else {
            let typings_location = if self
                .get_type_acquisition()
                .as_ref()
                .is_some_and(|ta| ta.enable.is_true())
            {
                host.session_options().typings_location.clone()
            } else {
                RootedDirectoryPath::default()
            };
            new_program_rc = new_program(ProgramOptions {
                config: Rc::new(ProgramConfig {
                    config: command_line,
                    use_source_of_project_reference: true,
                    typings_location,
                    ..Default::default()
                }),
                hosts: ProgramHosts {
                    host: host.compiler_host(),
                    tracing: None,
                },
                factories: ProgramFactories {
                    create_checker_pool: Some(create_checker_pool.clone()),
                    create_module_resolver: Some(create_module_resolver.clone()),
                },
            });
        }

        if !program_cloned
            && self
                .program
                .as_ref()
                .is_some_and(|p| p.has_same_file_names(&new_program_rc))
        {
            update_kind = ProgramUpdateKind::SameFileNames;
        }

        new_program_rc.bind_source_files();

        // Go's `defer cleanupModuleResolver()`.
        drop(create_module_resolver);
        if let Some(cleanup) = cleanup_module_resolver.borrow_mut().take() {
            cleanup();
        }

        CreateProgramResult {
            program: new_program_rc,
            update_kind,
            checker_pool: created_checker_pool
                .borrow_mut()
                .take()
                .expect("checker pool factory was not invoked"),
        }
    }
}

/// `CreateProgramResult`.
pub struct CreateProgramResult {
    /// `Program`.
    pub program: Rc<Program>,
    /// `UpdateKind`.
    pub update_kind: ProgramUpdateKind,
    /// `result.Program.GetCheckerPool().(*checkerPool)`.
    pub checker_pool: CheckerPool,
}

/// Go's assignment copies the `*Project` pointer; the `dirty` maps store
/// `Rc<Project>` so `Clone::clone` already shares. `Clone` is only used
/// internally by `Cloneable`.
impl Clone for Project {
    fn clone(&self) -> Self {
        let mut p = self.clone_project();
        p.program_update_kind = self.program_update_kind;
        p.checker_pool = None;
        p
    }
}

/// `Cloneable` for `Project` — Go's `(*Project).Clone()`.
impl Cloneable for Project {
    fn clone_value(&self) -> Self {
        self.clone_project()
    }
}

/// `NewProject`.
pub fn new_project(
    id: Id,
    kind: Kind,
    project_directory: RootedDirectoryPath,
    builder: &ProjectCollectionBuilder,
    logger: &LogTree,
) -> Project {
    logger.logf(format_args!(
        "Creating {}Project: {}, currentDirectory: {}",
        kind.as_str(),
        id,
        project_directory.as_string()
    ));
    let relative_pattern_support = tsc_lsproto::get_client_capabilities(&builder.ctx)
        .workspace
        .did_change_watched_files
        .relative_pattern_support;
    let case_sensitivity = builder.fs.fs.case_sensitivity();
    let glob_mapper = create_resolution_lookup_glob_mapper(
        builder.session_options.current_directory.clone(),
        builder.session_options.default_library_path.clone(),
        project_directory.clone(),
        case_sensitivity,
    );
    Project {
        kind,
        id: id.clone(),
        project_directory: project_directory.clone(),
        config_file_name: RootedFilePath::default(),
        config_file_path: PathKey::default(),
        dirty: true,
        dirty_file_path: PathKey::default(),
        host: None,
        command_line: None,
        command_line_with_typings_files: OnceLock::new(),
        program: None,
        program_update_kind: ProgramUpdateKind::None,
        program_last_update: 0,
        potential_project_references: None,
        program_files_watch: Some(new_watched_files(
            &format!("program files for {}", id),
            WatchKind(WatchKind::Create.0 | WatchKind::Change.0 | WatchKind::Delete.0),
            relative_pattern_support,
            None,
            move |input: &Option<Arc<SyncMap<PathKey, RootedFilePath>>>| {
                glob_mapper(input.as_deref())
            },
        )),
        typings_watch: if builder.session_options.typings_location.as_string().is_empty() {
            None
        } else {
            Some(new_watched_files(
                "typings installer files",
                WatchKind(WatchKind::Create.0 | WatchKind::Change.0 | WatchKind::Delete.0),
                relative_pattern_support,
                // `core.Identity` — the compute input is the patterns themselves.
                PatternsAndIgnored::default(),
                |p| p.clone(),
            ))
        },
        content_mapper_watch: Some(new_watched_files_for_paths(
            &format!("content mapper configuration files for {}", id),
            WatchKind(WatchKind::Create.0 | WatchKind::Change.0 | WatchKind::Delete.0),
            relative_pattern_support,
            builder.session_options.current_directory.clone(),
            case_sensitivity,
            Vec::new(),
        )),
        content_mapper_watched_files: None,
        checker_pool: None,
        module_resolver_factory: None,
        module_resolver_id: 0,
        installed_typings_info: None,
        typings_files: Vec::new(),
    }
}

/// `NewConfiguredProject`.
pub fn new_configured_project(
    config_file_name: RootedFilePath,
    config_file_path: PathKey,
    builder: &ProjectCollectionBuilder,
    logger: &LogTree,
) -> Project {
    let configured_project_id = configured_project_id_from_path_key(&config_file_path);
    let mut project = new_project(
        configured_project_id.as_id(),
        Kind::Configured,
        config_file_name.directory(),
        builder,
        logger,
    );
    project.config_file_name = config_file_name;
    project.config_file_path = config_file_path;
    project
}

/// `NewInferredProject`.
pub fn new_inferred_project(
    project_directory: RootedDirectoryPath,
    compiler_options: Option<Arc<CompilerOptions>>,
    root_file_names: Vec<RootedFilePath>,
    project_references: Vec<ProjectReference>,
    content_mappers: Vec<Arc<Mapper>>,
    builder: &ProjectCollectionBuilder,
    logger: &LogTree,
) -> Project {
    let mut project = new_project(
        InferredProjectId.as_id(),
        Kind::Inferred,
        project_directory.clone(),
        builder,
        logger,
    );
    let compiler_options = compiler_options.unwrap_or_else(|| {
        Arc::new(CompilerOptions {
            allow_js: TS_TRUE,
            module: tsc_core::options_generated::ModuleKind::ESNext,
            module_resolution: tsc_core::options_generated::ModuleResolutionKind::Bundler,
            target: tsc_core::options_generated::ScriptTarget::LATEST_STANDARD,
            jsx: tsc_core::options_generated::JsxEmit::ReactJSX,
            allow_importing_ts_extensions: TS_TRUE,
            strict_null_checks: TS_TRUE,
            strict_function_types: TS_TRUE,
            source_map: TS_TRUE,
            allow_non_ts_extensions: TS_TRUE,
            resolve_json_module: TS_TRUE,
            ..Default::default()
        })
    });
    project.command_line = Some(Arc::new(new_inferred_project_command_line(
        Some(compiler_options.as_ref()),
        root_file_names,
        project_references,
        content_mappers,
        &project_directory,
        builder.fs.fs.case_sensitivity(),
    )));
    project
}

/// `newSyntheticProject` — `compilerOptions` is nil-able (Go
/// `*core.CompilerOptions`).
pub fn new_synthetic_project(
    id: &SyntheticProjectId,
    project_directory: RootedDirectoryPath,
    compiler_options: Option<Arc<CompilerOptions>>,
    root_file_names: Vec<RootedFilePath>,
    project_references: Vec<ProjectReference>,
    content_mappers: Vec<Arc<Mapper>>,
    builder: &ProjectCollectionBuilder,
    logger: &LogTree,
) -> Project {
    let mut project = new_project(
        id.as_id(),
        Kind::Synthetic,
        project_directory.clone(),
        builder,
        logger,
    );
    project.command_line = Some(Arc::new(new_inferred_project_command_line(
        compiler_options.as_deref(),
        root_file_names,
        project_references,
        content_mappers,
        &project_directory,
        builder.fs.fs.case_sensitivity(),
    )));
    project
}

/// `newInferredProjectCommandLine` — `compilerOptions` is nil-able (Go
/// `*core.CompilerOptions`); `None` produces a nil `CompilerOptions` in the
/// command line, matching Go.
pub fn new_inferred_project_command_line(
    compiler_options: Option<&CompilerOptions>,
    root_file_names: Vec<RootedFilePath>,
    project_references: Vec<ProjectReference>,
    content_mappers: Vec<Arc<Mapper>>,
    project_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> ParsedCommandLine {
    let mut command_line = new_parsed_command_line_opt(
        compiler_options.cloned(),
        root_file_names,
        project_references,
        project_directory.clone(),
        case_sensitivity,
    );
    command_line.set_content_mappers(content_mappers);
    command_line
}
