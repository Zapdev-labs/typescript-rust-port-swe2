// Ported from tsc/internal/api/module_resolution.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go's `module.Resolver` returns a trailing error that no implementation
//   produces; the Rust trait drops it. The `callbackModuleResolver` IPC
//   failure becomes `resolve_module_name_from_directory` panicking? No —
//   see `resolve_module_name` below: the callback failure is returned as a
//   `DiagAndArgs`-free `Err` through the internal impl and surfaced as a
//   resolution failure diagnostic? Go's `resolveModuleName` returns
//   `error`; the only production caller path (`moduleResolverFactory`) is
//   invoked inside program builds where the resolver interface has no
//   error channel, so Go would propagate through `ResolveModuleName`'s
//   error return which `handleResolveModuleName` surfaces. For resolver
//   use inside program builds the Rust trait drops the error — the
//   callback failure is reported via `handle_resolve_module_name` only.
// - `s.conn` may be absent when a callback resolver is used; Go panics on
//   the nil-interface call. `module_resolver_factory` rejects that state
//   with a client error before constructing the factory instead.
// - `Resolver` has no error channel, so `CallbackModuleResolver` records
//   callback failures in `last_error`; `handle_resolve_module_name` reads
//   it after the call to surface Go's `error` return. In program builds
//   the recorded error is unread — same limitation as every other
//   resolver error in this port (see tsc-module's PORT note).

use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex};

use rustc_hash::FxHashMap;

use tsc_core::compileroptions::{
    RESOLUTION_MODE_COMMON_JS, RESOLUTION_MODE_ESM, RESOLUTION_MODE_NONE, ResolutionMode,
};
use tsc_core::context::Context;
use tsc_core::options_generated::ModuleKind;
use tsc_ipc as ipc;
use tsc_locale as locale;
use tsc_module as module;
use tsc_project as project;
use tsc_tspath as tspath;
use tsc_vfs as vfs;

use crate::proto::{
    CreateModuleResolverParams, CreateProgramOptions, ERR_CLIENT_ERROR,
    MODULE_RESOLUTION_FALLBACK_RESOLVE, MODULE_RESOLUTION_FALLBACK_UNRESOLVED,
    ModuleResolutionSpec, ModuleResolverId, ReleaseModuleResolverParams, ResolvedModule,
    ResolveModuleNameCallbackParams, ResolveModuleNameParams, ResolveModuleNameResult, SnapshotId,
    StaticModuleResolution, new_package_id,
};
use crate::session::{ModuleResolverRegistration, ProgramResolutionContext, Session};

/// `ResolutionHost` over a plain `vfs.FS` + current directory — Go passes
// `sd.snapshot` / `s` directly as the host; both only contribute
// `FS()`/`GetCurrentDirectory()`.
struct ResolutionHostAdapter {
    fs: Arc<dyn vfs::Vfs>,
    current_directory: tspath::RootedDirectoryPath,
}

impl module::ResolutionHost for ResolutionHostAdapter {
    fn fs(&self) -> &Arc<dyn vfs::Vfs> {
        &self.fs
    }
    fn get_current_directory(&self) -> tspath::RootedDirectoryPath {
        self.current_directory.clone()
    }
}

/// `moduleResolverFactory`.
struct ModuleResolverFactoryImpl {
    registration: Arc<ModuleResolverRegistration>,
    session: Arc<Session>,
    /// `conn` is `Some` whenever a callback is configured —
    /// `module_resolver_factory` rejects that combination otherwise.
    conn: Option<Arc<dyn ipc::Conn>>,
    current_directory: tspath::RootedDirectoryPath,
}

impl project::snapshot::ModuleResolverFactory for ModuleResolverFactoryImpl {
    /// `NewResolver`.
    fn new_resolver(
        &self,
        ctx: &Context,
        options: module::ResolverOptions,
    ) -> (Arc<dyn module::Resolver>, Box<dyn FnOnce() + Send>) {
        let mut options = options;
        options.compiler_options = self.registration.compiler_options.clone();
        let mut fallback: Arc<dyn module::Resolver> =
            Arc::new(module::DefaultResolver::new(options.clone()));
        if self.registration.resolve_module_name_callback.is_empty() {
            if let Some(resolutions) = &self.registration.resolutions {
                fallback = Arc::new(module::new_static_resolver(
                    fallback,
                    resolutions.as_ref().clone(),
                ));
            }
            return (fallback, Box::new(|| {}));
        }
        let context_id = self.session.register_program_resolution_context(
            fallback.clone(),
            options,
            self.registration.clone(),
        );
        let mut resolver: Arc<dyn module::Resolver> = Arc::new(CallbackModuleResolver {
            registration: self.registration.clone(),
            conn: self
                .conn
                .clone()
                .expect("module_resolver_factory guarantees conn when a callback is set"),
            ctx: ctx.clone(),
            current_directory: self.current_directory.clone(),
            case_sensitivity: self.session.case_sensitivity(),
            snapshot: SnapshotId::default(),
            program_resolution_context_id: context_id,
            fallback_resolver: fallback,
            last_error: Mutex::new(None),
        });
        if let Some(resolutions) = &self.registration.resolutions {
            resolver = Arc::new(module::new_static_resolver(
                resolver,
                resolutions.as_ref().clone(),
            ));
        }
        let session = self.session.clone();
        (resolver, Box::new(move || {
            session.release_program_resolution_context(context_id);
        }))
    }
}

/// `callbackModuleResolver`.
struct CallbackModuleResolver {
    registration: Arc<ModuleResolverRegistration>,
    conn: Arc<dyn ipc::Conn>,
    ctx: Context,
    current_directory: tspath::RootedDirectoryPath,
    case_sensitivity: tspath::CaseSensitivity,
    snapshot: SnapshotId,
    program_resolution_context_id: u64,
    fallback_resolver: Arc<dyn module::Resolver>,
    /// Go's `error` return, parked for `handle_resolve_module_name` (the
    /// `Resolver` trait itself has no error channel).
    last_error: Mutex<Option<String>>,
}

impl CallbackModuleResolver {
    /// `resolveModuleName` — the shared implementation. `Err` carries the
    /// Go `error` return; `handleResolveModuleName` surfaces it, while the
    /// `Resolver` trait (which has no error channel — see file header)
    /// degrades it to an unresolved result.
    fn resolve_module_name_impl(
        &self,
        module_name: &str,
        containing_directory: &tspath::RootedDirectoryPath,
        resolution_mode: ResolutionMode,
    ) -> Result<Option<module::ResolvedModule>, String> {
        let mut params = ResolveModuleNameCallbackParams {
            module_name: module_name.to_string(),
            containing_directory: containing_directory.as_string().to_string(),
            ..Default::default()
        };
        if self.snapshot != 0 {
            params.snapshot = Some(self.snapshot);
        }
        if self.program_resolution_context_id != 0 {
            params.in_progress_snapshot = Some(self.program_resolution_context_id);
        }
        params.resolution_mode = Some(resolution_mode);
        let callback_result = self
            .conn
            .call(
                &self.ctx,
                &self.registration.resolve_module_name_callback,
                Some(ipc::marshal_params(&params).map_err(|e| {
                    format!("resolveModuleName callback failed: {e}")
                })?),
            )
            .map_err(|e| format!("resolveModuleName callback failed: {e}"))?;

        let Some(raw) = callback_result else {
            return Ok(None);
        };
        if raw.get() == "null" {
            return Ok(None);
        }
        let static_resolution: StaticModuleResolution =
            serde_json::from_str(raw.get()).map_err(|e| {
                format!("invalid resolveModuleName callback result: {e}")
            })?;
        Ok(static_module_resolution_to_resolved_module(
            &static_resolution,
            &self.current_directory,
            self.case_sensitivity,
        ))
    }

    /// Runs `resolve_module_name_impl`, parking an `Err` in `last_error`
    /// so the direct `resolveModuleName` API call can surface it.
    fn resolve_module_name_recording_error(
        &self,
        module_name: &str,
        containing_directory: &tspath::RootedDirectoryPath,
        resolution_mode: ResolutionMode,
    ) -> (Option<module::ResolvedModule>, Vec<module::DiagAndArgs>) {
        match self.resolve_module_name_impl(module_name, containing_directory, resolution_mode) {
            Ok(result) => (result, Vec::new()),
            Err(e) => {
                *self.last_error.lock().unwrap() = Some(e);
                (None, Vec::new())
            }
        }
    }
}

impl module::Resolver for CallbackModuleResolver {
    /// `BaseDirectory`.
    fn base_directory(&self) -> tspath::RootedDirectoryPath {
        self.fallback_resolver.base_directory()
    }

    /// `ResolveModuleName`.
    fn resolve_module_name(
        &self,
        module_name: &str,
        containing_file: &tspath::RootedFilePath,
        resolution_mode: ResolutionMode,
        _redirected_reference: Option<&dyn module::ResolvedProjectReference>,
    ) -> (Option<module::ResolvedModule>, Vec<module::DiagAndArgs>) {
        self.resolve_module_name_recording_error(
            module_name,
            &containing_file.directory(),
            resolution_mode,
        )
    }

    /// `ResolveModuleNameFromDirectory`.
    fn resolve_module_name_from_directory(
        &self,
        module_name: &str,
        containing_directory: &tspath::RootedDirectoryPath,
        resolution_mode: ResolutionMode,
    ) -> (Option<module::ResolvedModule>, Vec<module::DiagAndArgs>) {
        self.resolve_module_name_recording_error(module_name, containing_directory, resolution_mode)
    }

    /// `ResolveTypeReferenceDirective` delegates to the fallback resolver.
    fn resolve_type_reference_directive(
        &self,
        type_reference_directive_name: &str,
        containing_file: &tspath::RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn module::ResolvedProjectReference>,
    ) -> (module::ResolvedTypeReferenceDirective, Vec<module::DiagAndArgs>) {
        self.fallback_resolver.resolve_type_reference_directive(
            type_reference_directive_name,
            containing_file,
            resolution_mode,
            redirected_reference,
        )
    }

    /// `GetResolutionData`.
    fn get_resolution_data(&self) -> &module::ResolutionData {
        self.fallback_resolver.get_resolution_data()
    }
}

/// `compileModuleResolutionSpec`.
fn compile_module_resolution_spec(
    spec: Option<&ModuleResolutionSpec>,
    current_directory: &tspath::RootedDirectoryPath,
    case_sensitivity: tspath::CaseSensitivity,
) -> Result<Option<module::StaticResolutions>, String> {
    let Some(spec) = spec else {
        return Ok(None);
    };
    let fallback_to_resolution = if spec.fallback == MODULE_RESOLUTION_FALLBACK_RESOLVE {
        true
    } else if spec.fallback == MODULE_RESOLUTION_FALLBACK_UNRESOLVED {
        false
    } else {
        return Err(format!(
            "{ERR_CLIENT_ERROR}: invalid module resolution fallback {:?}",
            spec.fallback.as_str()
        ));
    };

    let mut entries = Vec::with_capacity(spec.entries.len());
    for (i, entry) in spec.entries.iter().enumerate() {
        if entry.module_name.is_empty() {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: module resolution entry {i} has an empty moduleName"
            ));
        }
        let Some(result) = &entry.result else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: module resolution entry {i} has no result"
            ));
        };

        let mut static_entry = module::StaticResolutionEntry {
            module_name: entry.module_name.clone(),
            containing_directory: Default::default(),
            resolution_mode: None,
            result: None,
        };
        if let Some(containing_directory) = &entry.containing_directory {
            static_entry.containing_directory = tspath::to_rooted_directory_path(
                containing_directory
                    .to_file_name(current_directory)
                    .as_string(),
                current_directory,
            );
        }
        if let Some(mode) = entry.resolution_mode {
            if mode != ModuleKind::None
                && mode != ModuleKind::CommonJS
                && mode != ModuleKind::ESNext
            {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: module resolution entry {i} has invalid resolutionMode {mode}"
                ));
            }
            static_entry.resolution_mode = Some(mode);
        }
        static_entry.result = static_module_resolution_to_resolved_module(
            result,
            current_directory,
            case_sensitivity,
        );
        entries.push(static_entry);
    }

    let resolutions = module::new_static_resolutions(
        entries,
        fallback_to_resolution,
        current_directory.clone(),
        case_sensitivity,
    )
    .map_err(|e| format!("{ERR_CLIENT_ERROR}: {e}"))?;
    Ok(Some(resolutions))
}

/// `staticModuleResolutionToResolvedModule`.
fn static_module_resolution_to_resolved_module(
    static_resolution: &StaticModuleResolution,
    current_directory: &tspath::RootedDirectoryPath,
    case_sensitivity: tspath::CaseSensitivity,
) -> Option<module::ResolvedModule> {
    let resolved_file_name = static_resolution
        .resolved_file_name
        .as_ref()?
        .to_file_name(current_directory);
    let mut result = module::ResolvedModule {
        resolved_file_name: resolved_file_name.clone(),
        is_custom_resolution: true,
        ..Default::default()
    };
    if let Some(original_path) = &static_resolution.original_path {
        result.original_path = original_path.to_file_name(current_directory);
    }
    result.resolved_path = case_sensitivity.path_key(&result.resolved_file_name.as_path());
    if let Some(package_id) = &static_resolution.package_id {
        result.package_id = module::PackageId {
            name: package_id.name.clone(),
            sub_module_name: package_id.sub_module_name.clone(),
            version: package_id.version.clone(),
            peer_dependencies: package_id.peer_dependencies.clone(),
        };
    }
    let original_path = if result.original_path.as_string().is_empty() {
        result.resolved_file_name.clone()
    } else {
        result.original_path.clone()
    };
    result.extension = result.resolved_file_name.extension().to_string();
    result.is_external_library_import =
        original_path.as_string().contains("/node_modules/");
    Some(result)
}

/// `newResolvedModuleResponse`.
pub(crate) fn new_resolved_module_response(
    resolution: &module::ResolvedModule,
) -> Option<ResolvedModule> {
    if !resolution.is_resolved() {
        return None;
    }
    Some(ResolvedModule {
        resolved_file_name: resolution.resolved_file_name.as_string().to_string(),
        original_path: resolution.original_path.as_string().to_string(),
        extension: resolution.extension.clone(),
        resolved_using_ts_extension: resolution.resolved_using_ts_extension,
        resolved_using_extra_extensions: resolution.resolved_using_extra_extensions,
        package_id: new_package_id(&resolution.package_id),
        is_external_library_import: resolution.is_external_library_import,
        alternate_result: resolution.alternate_result.as_string().to_string(),
    })
}

/// `newResolvedTypeReferenceDirectiveResponse`.
pub(crate) fn new_resolved_type_reference_directive_response(
    resolution: Option<&module::ResolvedTypeReferenceDirective>,
) -> Option<crate::proto::ResolvedTypeReferenceDirective> {
    let resolution = resolution?;
    if !resolution.is_resolved() {
        return None;
    }
    Some(crate::proto::ResolvedTypeReferenceDirective {
        primary: resolution.primary,
        resolved_file_name: resolution.resolved_file_name.as_string().to_string(),
        original_path: resolution.original_path.as_string().to_string(),
        package_id: new_package_id(&resolution.package_id),
        is_external_library_import: resolution.is_external_library_import,
    })
}

/// `moduleResolutionTraceToStrings`.
fn module_resolution_trace_to_strings(trace: &[module::DiagAndArgs]) -> Vec<String> {
    trace
        .iter()
        .map(|entry| entry.message.localize(&locale::DEFAULT, &entry.args))
        .collect()
}

/// `moduleResolutionError`.
pub(crate) fn module_resolution_error(
    snapshot: &project::snapshot::Snapshot,
) -> Option<String> {
    for project in snapshot.project_collection.projects() {
        if let Some(program) = &project.program {
            if let Some(err) = program.module_resolution_error() {
                return Some(err.to_string());
            }
        }
    }
    None
}

impl Session {
    /// `s.moduleResolverFactory`.
    pub(crate) fn module_resolver_factory(
        self: &Arc<Self>,
        options: &CreateProgramOptions,
    ) -> Result<Option<Arc<dyn project::snapshot::ModuleResolverFactory>>, String> {
        if options.module_resolver == 0 {
            return Ok(None);
        }
        let data = self
            .module_resolvers
            .read()
            .unwrap()
            .get(&options.module_resolver)
            .cloned();
        let Some(data) = data else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: module resolver {} not found",
                options.module_resolver
            ));
        };
        let conn = self.conn.lock().unwrap().clone();
        if !data.resolve_module_name_callback.is_empty() && conn.is_none() {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: API connection is not initialized"
            ));
        }
        Ok(Some(Arc::new(ModuleResolverFactoryImpl {
            registration: data,
            session: self.clone(),
            conn,
            current_directory: self.get_current_directory(),
        })))
    }

    /// `s.registerProgramResolutionContext`.
    fn register_program_resolution_context(
        &self,
        resolver: Arc<dyn module::Resolver>,
        options: module::ResolverOptions,
        registration: Arc<ModuleResolverRegistration>,
    ) -> u64 {
        let id = self
            .next_program_resolution_context_id
            .fetch_add(1, Ordering::Relaxed)
            + 1;
        let mut resolvers = FxHashMap::default();
        resolvers.insert(registration.id, resolver);
        self.program_resolution_contexts
            .write()
            .unwrap()
            .insert(
                id,
                std::rc::Rc::new(ProgramResolutionContext {
                    options,
                    resolvers: Mutex::new(resolvers),
                }),
            );
        id
    }

    /// `s.releaseProgramResolutionContext`.
    fn release_program_resolution_context(&self, id: u64) {
        self.program_resolution_contexts
            .write()
            .unwrap()
            .remove(&id);
    }

    /// `s.handleCreateModuleResolver`.
    pub(crate) fn handle_create_module_resolver(
        &self,
        params: &CreateModuleResolverParams,
    ) -> Result<ModuleResolverId, String> {
        let provider = compile_module_resolution_spec(
            params.module_resolutions.as_ref(),
            &self.get_current_directory(),
            self.case_sensitivity(),
        )?;
        let id = ModuleResolverId(
            self.next_module_resolver_id.fetch_add(1, Ordering::Relaxed) + 1,
        );
        let data = Arc::new(ModuleResolverRegistration {
            id,
            compiler_options: Arc::new(params.compiler_options.clone()),
            resolutions: provider.map(Arc::new),
            resolve_module_name_callback: params.resolve_module_name_callback.clone(),
        });
        self.module_resolvers.write().unwrap().insert(id, data);
        Ok(id)
    }

    /// `s.handleReleaseModuleResolver`.
    pub(crate) fn handle_release_module_resolver(
        &self,
        params: &ReleaseModuleResolverParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let ok = self
            .module_resolvers
            .write()
            .unwrap()
            .remove(&params.resolver)
            .is_some();
        if !ok {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: module resolver {} not found",
                params.resolver
            ));
        }
        Ok(None)
    }

    /// `s.handleResolveModuleName`.
    pub(crate) fn handle_resolve_module_name(
        &self,
        ctx: &Context,
        params: &ResolveModuleNameParams,
    ) -> Result<ResolveModuleNameResult, String> {
        if params.module_name.is_empty() {
            return Err(format!("{ERR_CLIENT_ERROR}: moduleName is empty"));
        }
        let data = self
            .module_resolvers
            .read()
            .unwrap()
            .get(&params.resolver)
            .cloned();
        let Some(data) = data else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: module resolver {} not found",
                params.resolver
            ));
        };

        let mut mode = RESOLUTION_MODE_NONE;
        if let Some(resolution_mode) = params.resolution_mode {
            mode = resolution_mode;
            if mode != RESOLUTION_MODE_NONE
                && mode != RESOLUTION_MODE_COMMON_JS
                && mode != RESOLUTION_MODE_ESM
            {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: invalid resolutionMode {mode}"
                ));
            }
        }
        let containing_directory = tspath::to_rooted_directory_path(
            params
                .containing_directory
                .to_file_name(&self.get_current_directory())
                .as_string(),
            &self.get_current_directory(),
        );

        if params.snapshot != 0 && params.in_progress_snapshot != 0 {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: snapshot and inProgressSnapshot are mutually exclusive"
            ));
        }
        let mut resolver: Arc<dyn module::Resolver>;
        if params.in_progress_snapshot != 0 {
            let resolution_context = self
                .program_resolution_contexts
                .read()
                .unwrap()
                .get(&params.in_progress_snapshot)
                .cloned();
            let Some(resolution_context) = resolution_context else {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: in-progress snapshot {} not found",
                    params.in_progress_snapshot
                ));
            };
            resolver = resolution_context.resolver_for(&data);
        } else if params.snapshot != 0 {
            let sd = self.get_snapshot_data(params.snapshot)?;
            resolver = Arc::new(module::DefaultResolver::new(module::ResolverOptions {
                host: Arc::new(ResolutionHostAdapter {
                    fs: Arc::new(sd.snapshot.fs()),
                    current_directory: sd.snapshot.get_current_directory(),
                }),
                compiler_options: data.compiler_options.clone(),
                typings_location: Default::default(),
                project_name: String::new(),
                extra_extensions: sd.snapshot.content_mapper_extensions().to_vec(),
                package_json_cache: None,
            }));
        } else {
            resolver = Arc::new(module::DefaultResolver::new(module::ResolverOptions {
                host: Arc::new(ResolutionHostAdapter {
                    fs: self.fs(),
                    current_directory: self.get_current_directory(),
                }),
                compiler_options: data.compiler_options.clone(),
                typings_location: Default::default(),
                project_name: String::new(),
                extra_extensions: Vec::new(),
                package_json_cache: None,
            }));
        }
        let mut callback_resolver: Option<Arc<CallbackModuleResolver>> = None;
        if !data.resolve_module_name_callback.is_empty() {
            let Some(conn) = self.conn.lock().unwrap().clone() else {
                // Go would panic on the nil-interface call inside the
                // resolver; a client error is the faithful-but-safe
                // equivalent (see file header).
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: API connection is not initialized"
                ));
            };
            let callback = Arc::new(CallbackModuleResolver {
                registration: data.clone(),
                conn,
                ctx: ctx.clone(),
                current_directory: self.get_current_directory(),
                case_sensitivity: self.case_sensitivity(),
                snapshot: params.snapshot,
                program_resolution_context_id: params.in_progress_snapshot,
                fallback_resolver: resolver,
                last_error: Mutex::new(None),
            });
            resolver = callback.clone();
            callback_resolver = Some(callback);
        }
        if let Some(resolutions) = &data.resolutions {
            resolver = Arc::new(module::new_static_resolver(
                resolver,
                resolutions.as_ref().clone(),
            ));
        }
        let (result, trace) = resolver.resolve_module_name_from_directory(
            &params.module_name,
            &containing_directory,
            mode,
        );
        // `ResolveModuleNameFromDirectory`'s Go error return — parked on
        // the callback resolver because the Rust trait drops it.
        if let Some(callback) = &callback_resolver {
            if let Some(e) = callback.last_error.lock().unwrap().take() {
                return Err(e);
            }
        }
        Ok(ResolveModuleNameResult {
            resolved_module: result
                .as_ref()
                .and_then(new_resolved_module_response),
            trace: module_resolution_trace_to_strings(&trace),
            ..Default::default()
        })
    }
}

impl ProgramResolutionContext {
    /// `resolverFor` — returns (creating if needed) the fallback resolver
    /// for `registration` within this program-resolution context.
    fn resolver_for(
        &self,
        registration: &Arc<ModuleResolverRegistration>,
    ) -> Arc<dyn module::Resolver> {
        let mut resolvers = self.resolvers.lock().unwrap();
        if let Some(resolver) = resolvers.get(&registration.id) {
            return resolver.clone();
        }
        let mut options = self.options.clone();
        options.compiler_options = registration.compiler_options.clone();
        let resolver: Arc<dyn module::Resolver> =
            Arc::new(module::DefaultResolver::new(options));
        resolvers.insert(registration.id, resolver.clone());
        resolver
    }
}
