// Ported from tsc/internal/modulespecifiers/specifiers.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use rustc_hash::FxHashMap;
use tsc_ast::ast::Node;
use tsc_ast::ast_generated::{is_module_declaration, is_source_file};
use tsc_ast::ids::{NodeId, SymbolId};
use tsc_ast::symbol::{INTERNAL_SYMBOL_NAME_EXPORT_EQUALS, Symbol, SymbolArena};
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::utilities::{
    find_ancestor, get_source_file_of_node, is_external_module_augmentation,
    is_global_scope_augmentation, is_module_augmentation_external,
    is_module_with_string_literal_name,
};
use tsc_collections::OrderedMap;
use tsc_core::compileroptions::{
    RESOLUTION_MODE_COMMON_JS, RESOLUTION_MODE_ESM, RESOLUTION_MODE_NONE, ResolutionMode,
};
use tsc_core::options_generated::{CompilerOptions, ModuleResolutionKind};
use tsc_module as module;
use tsc_packagejson::{self as packagejson, JSONValueType, VersionPaths};
use tsc_stringutil as stringutil;
use tsc_tspath::{
    self as tspath, CaseSensitivity, ModuleSpecifier, RootedDirectoryPath, RootedFilePath,
};

use crate::compare::count_path_components;
use crate::preferences::{ModuleSpecifierPreferences, get_module_specifier_preferences};
use crate::types::{
    CheckerShape, MatchingMode, ModulePath, ModuleSpecifierEnding, ModuleSpecifierGenerationHost,
    ModuleSpecifierOptions, ModuleSpecifiersResult, RelativePreferenceKind, ResultKind,
    SourceFileForSpecifierGeneration, UserPreferences,
};
use crate::util::{
    compare_paths_by_redirect, get_js_extension_for_declaration_file_extension,
    get_js_extension_for_file, get_js_extension_for_file_name, get_node_module_path_parts,
    get_paths_relative_to_root_dirs, get_relative_path_if_in_same_volume, is_excluded_by_regex,
    is_path_relative_to_parent, package_json_paths_are_equal, path_is_bare_specifier,
    prefers_ts_extension, replace_first_star, resolve_path_pattern_if_in_same_volume,
    try_get_any_file_from_path, try_get_real_file_name_for_non_js_declaration_file_name,
};

/// `func GetModuleSpecifiers(...)`.
pub fn get_module_specifiers<S, H, C>(
    module_symbol: SymbolId,
    checker: &C,
    compiler_options: &CompilerOptions,
    importing_source_file: &S,
    host: &H,
    user_preferences: &UserPreferences,
    options: &ModuleSpecifierOptions,
    for_auto_imports: bool,
    symbols: &SymbolArena,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifiersResult
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
    C: CheckerShape,
{
    get_module_specifiers_with_info(
        module_symbol,
        checker,
        compiler_options,
        importing_source_file,
        host,
        user_preferences,
        options,
        for_auto_imports,
        symbols,
        nodes,
        resolve,
    )
}

/// `func GetModuleSpecifiersWithInfo(...)`.
pub fn get_module_specifiers_with_info<S, H, C>(
    module_symbol: SymbolId,
    checker: &C,
    compiler_options: &CompilerOptions,
    importing_source_file: &S,
    host: &H,
    user_preferences: &UserPreferences,
    options: &ModuleSpecifierOptions,
    for_auto_imports: bool,
    symbols: &SymbolArena,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifiersResult
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
    C: CheckerShape,
{
    let ambient =
        try_get_module_name_from_ambient_module(module_symbol, checker, symbols, nodes, resolve);
    if !ambient.name.is_empty() {
        if for_auto_imports
            && is_excluded_by_regex(
                ambient.name.as_string(),
                &user_preferences.auto_import_specifier_exclude_regexes,
            )
        {
            return ModuleSpecifiersResult {
                kind: ResultKind::Ambient,
                ambient_module_symbol: ambient.symbol,
                ..Default::default()
            };
        }
        return ModuleSpecifiersResult {
            specifiers: vec![ambient.name],
            kind: ResultKind::Ambient,
            ambient_module_symbol: ambient.symbol,
        };
    }

    let module_source_file =
        source_file_of_module(&symbols[module_symbol.index()], nodes, resolve);
    let Some(module_source_file) = module_source_file else {
        return ModuleSpecifiersResult::default();
    };

    // Use original source file name when file is from project reference output
    let module_file_name = host.get_source_of_project_reference_if_output_included(
        crate::types::arena_of_id(nodes, resolve, module_source_file)[module_source_file]
            .as_source_file(),
    );

    let (specifiers, kind) = get_module_specifiers_for_file_with_info(
        importing_source_file,
        &module_file_name,
        compiler_options,
        host,
        user_preferences,
        options,
        for_auto_imports,
        nodes,
        resolve,
    );
    ModuleSpecifiersResult {
        specifiers,
        kind,
        ..Default::default()
    }
}

/// `func GetModuleSpecifiersForFileWithInfo(...)`.
#[allow(clippy::too_many_arguments)]
pub fn get_module_specifiers_for_file_with_info<S, H>(
    importing_source_file: &S,
    module_file_name: &RootedFilePath,
    compiler_options: &CompilerOptions,
    host: &H,
    user_preferences: &UserPreferences,
    options: &ModuleSpecifierOptions,
    for_auto_imports: bool,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> (Vec<ModuleSpecifier>, ResultKind)
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let module_paths = get_all_module_paths_worker(
        &get_info(
            &host.get_source_of_project_reference_if_output_included(importing_source_file),
            host,
        ),
        module_file_name,
        host,
        compiler_options,
        options,
    );

    compute_module_specifiers(
        &module_paths,
        compiler_options,
        importing_source_file,
        host,
        user_preferences,
        options,
        for_auto_imports,
        nodes,
        resolve,
    )
}

/// `type Info struct`.
pub(crate) struct Info {
    pub case_sensitivity: CaseSensitivity,
    pub importing_source_file_name: RootedFilePath,
    pub source_directory: RootedDirectoryPath,
}

/// `type ambientModuleInfo struct`.
#[derive(Default)]
struct AmbientModuleInfo {
    name: ModuleSpecifier,
    symbol: Option<SymbolId>,
}

/// `getSourceFileOfModule` — like `ast::get_source_file_of_module`, but each
/// declaration is read in its own file's arena via `resolve` (Go reads the
/// shared heap through raw pointers; a single `nodes` slice only covers one
/// file's arena here).
fn source_file_of_module(
    module: &Symbol,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> Option<NodeId> {
    let declaration = module.value_declaration.or_else(|| {
        module.declarations.iter().copied().find(|&d| {
            let dn = crate::types::arena_of_id(nodes, resolve, d);
            !is_external_module_augmentation(&dn[d], &dn)
                && !is_global_scope_augmentation(&dn[d])
        })
    });
    let declaration = declaration?;
    let dn = crate::types::arena_of_id(nodes, resolve, declaration);
    get_source_file_of_node(Some(declaration), &dn)
}

fn try_get_module_name_from_ambient_module<C: CheckerShape>(
    module_symbol: SymbolId,
    checker: &C,
    symbols: &SymbolArena,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> AmbientModuleInfo {
    for &decl in &symbols[module_symbol.index()].declarations {
        let dn = crate::types::arena_of_id(nodes, resolve, decl);
        if is_module_with_string_literal_name(&dn[decl], &dn)
            && (!is_module_augmentation_external(&dn[decl], &dn)
                || !tspath::is_external_module_name_relative(
                    &dn[dn[decl].name().expect("module name")].text(&dn),
                ))
        {
            return AmbientModuleInfo {
                name: tspath::to_module_specifier(
                    &dn[dn[decl].name().expect("module name")].text(&dn),
                ),
                symbol: Some(module_symbol),
            };
        }
    }

    // the module could be a namespace, which is export through "export=" from an ambient module.
    /*
     * declare module "m" {
     *     namespace ns {
     *         class c {}
     *     }
     *     export = ns;
     * }
     */
    // `import {c} from "m";` is valid, in which case, `moduleSymbol` is "ns", but the module name should be "m"
    for &d in &symbols[module_symbol.index()].declarations {
        let dn = crate::types::arena_of_id(nodes, resolve, d);
        if !is_module_declaration(&dn[d]) {
            continue;
        }

        let possible_container = find_ancestor(Some(d), &dn, &mut |n, nodes| {
            is_module_with_string_literal_name(n, nodes)
        });
        let Some(possible_container) = possible_container else {
            continue;
        };
        let Some(parent) = dn[possible_container].parent else {
            continue;
        };
        if !is_source_file(&dn[parent]) {
            continue;
        }

        let Some(container_symbol) = dn[possible_container].symbol() else {
            continue;
        };
        let Some(sym) = symbols[container_symbol.index()]
            .exports
            .get(INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
            .copied()
        else {
            continue;
        };
        let Some(export_assignment_decl) = symbols[sym.index()].value_declaration else {
            continue;
        };
        let export_assignment_arena =
            crate::types::arena_of_id(nodes, resolve, export_assignment_decl);
        if export_assignment_arena[export_assignment_decl].kind != tsc_ast::Kind::ExportAssignment {
            continue;
        }
        // PORT: `Expression()` is always present on a valid export assignment;
        // Go would dereference a nil node here.
        let export_assignment_expr = export_assignment_arena[export_assignment_decl]
            .expression()
            .expect("export assignment expression");
        let Some(export_symbol) = checker.get_symbol_at_location(export_assignment_expr) else {
            continue;
        };
        let mut export_symbol = export_symbol;
        if symbols[export_symbol.index()]
            .flags
            .intersects(SymbolFlags::ALIAS)
        {
            export_symbol = checker.get_aliased_symbol(export_symbol);
        }
        // TODO: Possible strada bug - isn't this insufficient in the presence of merge symbols?
        // PORT: `SymbolId` is a file-local index; the checker implementation is
        // responsible for making symbol identity meaningful across arenas.
        if Some(export_symbol) == dn[d].symbol() {
            return AmbientModuleInfo {
                name: tspath::to_module_specifier(
                    &dn[dn[possible_container].name().expect("module name")].text(&dn),
                ),
                symbol: Some(container_symbol),
            };
        }
    }
    AmbientModuleInfo::default()
}

/// `func getInfo(importingSourceFileName, host) Info`.
pub(crate) fn get_info<H: ModuleSpecifierGenerationHost>(
    importing_source_file_name: &RootedFilePath,
    host: &H,
) -> Info {
    Info {
        importing_source_file_name: importing_source_file_name.clone(),
        source_directory: importing_source_file_name.directory(),
        case_sensitivity: host.case_sensitivity(),
    }
}

/// `func getAllModulePaths(...)`.
pub(crate) fn get_all_module_paths<H: ModuleSpecifierGenerationHost>(
    info: &Info,
    imported_file_name: &RootedFilePath,
    host: &H,
    compiler_options: &CompilerOptions,
    _preferences: &UserPreferences,
    options: &ModuleSpecifierOptions,
) -> Vec<ModulePath> {
    // !!! use new cache model
    // importingFilePath := info.CaseSensitivity.PathKey(info.ImportingSourceFileName.AsPath())
    // importedFilePath := info.CaseSensitivity.PathKey(importedFileName.AsPath())
    // cache := host.getModuleSpecifierCache();
    // if (cache != nil) {
    //     cached := cache.get(importingFilePath, importedFilePath, preferences, options);
    //     if (cached.modulePaths) {return cached.modulePaths;}
    // }
    let module_paths =
        get_all_module_paths_worker(info, imported_file_name, host, compiler_options, options);
    // if (cache != nil) {
    //     cache.setModulePaths(importingFilePath, importedFilePath, preferences, options, modulePaths);
    // }
    module_paths
}

/// `func getAllModulePathsWorker(...)`.
pub(crate) fn get_all_module_paths_worker<H: ModuleSpecifierGenerationHost>(
    info: &Info,
    imported_file_name: &RootedFilePath,
    host: &H,
    _compiler_options: &CompilerOptions,
    _options: &ModuleSpecifierOptions,
) -> Vec<ModulePath> {
    let mut all_file_names: FxHashMap<RootedFilePath, ModulePath> = FxHashMap::default();
    let paths = get_each_file_name_of_module(
        &info.importing_source_file_name,
        imported_file_name,
        host,
        true,
    );
    let paths_len = paths.len();
    for p in paths {
        all_file_names.insert(p.file_name.clone(), p);
    }

    let case_sensitivity = info.case_sensitivity;
    let compare_paths =
        |a: &ModulePath, b: &ModulePath| compare_paths_by_redirect(a, b, case_sensitivity).cmp(&0);

    // Sort by paths closest to importing file Name directory
    let mut sorted_paths = Vec::with_capacity(paths_len);
    let mut directory = info.source_directory.clone();
    while !all_file_names.is_empty() {
        let mut paths_in_directory: Vec<ModulePath> = Vec::new();
        all_file_names.retain(|file_name, p| {
            if case_sensitivity.starts_with_directory(file_name, &directory) {
                paths_in_directory.push(p.clone());
                false
            } else {
                true
            }
        });
        if !paths_in_directory.is_empty() {
            paths_in_directory.sort_by(compare_paths);
            sorted_paths.extend(paths_in_directory);
        }
        let new_directory = directory.as_path().directory();
        if new_directory == directory {
            break;
        }
        directory = new_directory;
    }
    if !all_file_names.is_empty() {
        let mut remaining_paths: Vec<ModulePath> = all_file_names.into_values().collect();
        remaining_paths.sort_by(compare_paths);
        sorted_paths.extend(remaining_paths);
    }
    sorted_paths
}

/// containsIgnoredPath checks if a path contains patterns that should be ignored.
/// This is a local helper that duplicates tspath.ContainsIgnoredPath for performance.
pub(crate) fn contains_ignored_path(file_name: &RootedFilePath) -> bool {
    file_name.as_string().contains("/node_modules/.")
        || file_name.as_string().contains("/.git")
        || file_name.as_string().contains(".#")
}

pub(crate) fn module_specifier_contains_node_modules(specifier: &ModuleSpecifier) -> bool {
    specifier.contains("/node_modules/")
}

/// GetEachFileNameOfModule returns all possible file paths for a module, including symlink alternatives.
/// This function handles symlink resolution and provides multiple path options for module resolution.
///
/// `func GetEachFileNameOfModule(...)`.
pub fn get_each_file_name_of_module<H: ModuleSpecifierGenerationHost>(
    importing_file_name: &RootedFilePath,
    imported_file_name: &RootedFilePath,
    host: &H,
    prefer_symlinks: bool,
) -> Vec<ModulePath> {
    let case_sensitivity = host.case_sensitivity();
    let imported_path = case_sensitivity.path_key(&imported_file_name.as_path());
    let mut reference_redirect = RootedFilePath::default();
    if let Some(output_and_reference) = host.get_project_reference_from_source(&imported_path) {
        if !output_and_reference.output_dts.is_empty() {
            reference_redirect = output_and_reference.output_dts.clone();
        }
    }

    let redirects = host.get_redirect_targets(&imported_path);
    let mut imported_file_names: Vec<RootedFilePath> = Vec::with_capacity(2 + redirects.len());
    if !reference_redirect.is_empty() {
        imported_file_names.push(reference_redirect.clone());
    }
    imported_file_names.push(imported_file_name.clone());
    imported_file_names.extend(redirects.iter().cloned());
    let targets = imported_file_names;
    let mut should_filter_ignored_paths = !targets.iter().all(contains_ignored_path);

    let mut results: Vec<ModulePath> = Vec::with_capacity(2);
    if !prefer_symlinks {
        for p in &targets {
            if !(should_filter_ignored_paths && contains_ignored_path(p)) {
                results.push(ModulePath {
                    file_name: p.clone(),
                    is_in_node_modules: p.contains_lowercase_directory_sequence("/node_modules/"),
                    is_redirect: reference_redirect == *p,
                });
            }
        }
    }

    if let Some(symlink_cache) = host.get_symlink_cache() {
        tspath::for_each_ancestor_directory_path_stopping_at_global_cache(
            &host.get_global_typings_cache_location(),
            &imported_file_name.directory(),
            |real_path_directory| -> (bool, bool) {
                let Some(symlink_set) = symlink_cache
                    .directories_by_realpath()
                    .load(&case_sensitivity.path_key(&real_path_directory.as_path()))
                else {
                    return (false, false);
                }; // Continue to ancestor directory

                // Don't want to a package to globally import from itself (importNameCodeFix_symlink_own_package.ts)
                if case_sensitivity.contains_file_path(real_path_directory, importing_file_name) {
                    return (false, true); // Stop search, each ancestor directory will also hit this condition
                }

                for target in &targets {
                    let Some(relative) = case_sensitivity
                        .relative_file_path_from_directory(real_path_directory, target)
                    else {
                        continue;
                    };
                    symlink_set.range(|symlink_directory| {
                        let option = symlink_directory.resolve_relative_file(&relative);
                        results.push(ModulePath {
                            file_name: option.clone(),
                            is_in_node_modules: option
                                .contains_lowercase_directory_sequence("/node_modules/"),
                            is_redirect: *target == reference_redirect,
                        });
                        should_filter_ignored_paths = true; // We found a non-ignored path in symlinks, so we can reject ignored-path realpaths
                        true
                    });
                }

                (false, false)
            },
        );
    }

    if prefer_symlinks {
        for p in &targets {
            if !(should_filter_ignored_paths && contains_ignored_path(p)) {
                results.push(ModulePath {
                    file_name: p.clone(),
                    is_in_node_modules: p.contains_lowercase_directory_sequence("/node_modules/"),
                    is_redirect: reference_redirect == *p,
                });
            }
        }
    }

    results
}

/// `func computeModuleSpecifiers(...)`.
#[allow(clippy::too_many_arguments)]
fn compute_module_specifiers<S, H>(
    module_paths: &[ModulePath],
    compiler_options: &CompilerOptions,
    importing_source_file: &S,
    host: &H,
    user_preferences: &UserPreferences,
    options: &ModuleSpecifierOptions,
    for_auto_import: bool,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> (Vec<ModuleSpecifier>, ResultKind)
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let info = get_info(importing_source_file.file_name(), host);
    let preferences = get_module_specifier_preferences(
        user_preferences,
        host,
        compiler_options,
        importing_source_file,
        "",
    );
    let case_sensitivity = info.case_sensitivity;

    let mut existing_specifier = ModuleSpecifier::default();
    'module_paths: for module_path in module_paths {
        let target_path = case_sensitivity.path_key(&module_path.file_name.as_path());
        let mut existing_import: Option<NodeId> = None;
        for &import_specifier in importing_source_file.imports() {
            let resolved_module = host
                .get_resolved_module_from_module_specifier(importing_source_file, import_specifier);
            if resolved_module.is_some_and(|m| m.is_resolved() && m.resolved_path == target_path) {
                existing_import = Some(import_specifier);
                break;
            }
        }
        if let Some(existing_import) = existing_import {
            let existing_buf = crate::types::arena_of_id(nodes, resolve, existing_import);
            if preferences.relative_preference == RelativePreferenceKind::NonRelative
                && tspath::path_is_relative(
                    &existing_buf[existing_import].text(&existing_buf),
                )
            {
                // If the preference is for non-relative and the module specifier is relative, ignore it
                continue;
            }
            let existing_mode =
                host.get_mode_for_usage_location(importing_source_file, existing_import);
            let mut target_mode = options.override_import_mode;
            if target_mode == RESOLUTION_MODE_NONE {
                target_mode = host.get_default_resolution_mode_for_file(importing_source_file);
            }
            if existing_mode != target_mode
                && existing_mode != RESOLUTION_MODE_NONE
                && target_mode != RESOLUTION_MODE_NONE
            {
                // If the candidate import mode doesn't match the mode we're generating for, don't consider it
                continue;
            }
            existing_specifier =
                tspath::to_module_specifier(&existing_buf[existing_import].text(&existing_buf));
            break 'module_paths;
        }
    }

    if !existing_specifier.is_empty() {
        return (vec![existing_specifier], ResultKind::None);
    }

    let imported_file_is_in_node_modules = module_paths.iter().any(|p| p.is_in_node_modules);

    // Module specifier priority:
    //   1. "Bare package specifiers" (e.g. "@foo/bar") resulting from a path through node_modules to a package.json's "types" entry
    //   2. Specifiers generated using "paths" from tsconfig
    //   3. Non-relative specfiers resulting from a path through node_modules (e.g. "@foo/bar/path/to/file")
    //   4. Relative paths
    let mut paths_specifiers: Vec<ModuleSpecifier> = Vec::new();
    let mut redirect_paths_specifiers: Vec<ModuleSpecifier> = Vec::new();
    let mut node_modules_specifiers: Vec<ModuleSpecifier> = Vec::new();
    let mut relative_specifiers: Vec<ModuleSpecifier> = Vec::new();

    for module_path in module_paths {
        let mut specifier = ModuleSpecifier::default();
        if module_path.is_in_node_modules {
            specifier = try_get_module_name_as_node_module(
                module_path,
                &info,
                importing_source_file,
                host,
                compiler_options,
                user_preferences,
                false, // packageNameOnly
                options.override_import_mode,
                nodes,
                resolve,
            );
        }
        if !specifier.is_empty()
            && !(for_auto_import
                && is_excluded_by_regex(specifier.as_string(), preferences.exclude_regexes))
        {
            node_modules_specifiers.push(specifier.clone());
            if module_path.is_redirect {
                // If we got a specifier for a redirect, it was a bare package specifier (e.g. "@foo/bar",
                // not "@foo/bar/path/to/file"). No other specifier will be this good, so stop looking.
                return (node_modules_specifiers, ResultKind::NodeModules);
            }
        }

        let mut import_mode = options.override_import_mode;
        if import_mode == RESOLUTION_MODE_NONE {
            import_mode = host.get_default_resolution_mode_for_file(importing_source_file);
        }
        let local = get_local_module_specifier(
            &module_path.file_name,
            &info,
            compiler_options,
            host,
            import_mode,
            &preferences,
            /*pathsOnly*/ module_path.is_redirect || !specifier.is_empty(),
            nodes,
            resolve,
        );
        if local.is_empty()
            || for_auto_import
                && is_excluded_by_regex(local.as_string(), preferences.exclude_regexes)
        {
            continue;
        }
        if module_path.is_redirect {
            redirect_paths_specifiers.push(local);
        } else if path_is_bare_specifier(&local) {
            if module_specifier_contains_node_modules(&local) {
                // We could be in this branch due to inappropriate use of `baseUrl`, not intentional `paths`
                // usage. It's impossible to reason about where to prioritize baseUrl-generated module
                // specifiers, but if they contain `/node_modules/`, they're going to trigger a portability
                // error, so *at least* don't prioritize those.
                relative_specifiers.push(local);
            } else {
                paths_specifiers.push(local);
            }
        } else if for_auto_import
            || !imported_file_is_in_node_modules
            || module_path.is_in_node_modules
        {
            // Why this extra conditional, not just an `else`? If some path to the file contained
            // 'node_modules', but we can't create a non-relative specifier (e.g. "@foo/bar/path/to/file"),
            // that means we had to go through a *sibling's* node_modules, not one we can access directly.
            // If some path to the file was in node_modules but another was not, this likely indicates that
            // we have a monorepo structure with symlinks. In this case, the non-nodeModules path is
            // probably the realpath, e.g. "../bar/path/to/file", but a relative path to another package
            // in a monorepo is probably not portable. So, the module specifier we actually go with will be
            // the relative path through node_modules, so that the declaration emitter can produce a
            // portability error. (See declarationEmitReexportedSymlinkReference3)
            relative_specifiers.push(local);
        }
    }

    if !paths_specifiers.is_empty() {
        return (paths_specifiers, ResultKind::Paths);
    }
    if !redirect_paths_specifiers.is_empty() {
        return (redirect_paths_specifiers, ResultKind::Redirect);
    }
    if !node_modules_specifiers.is_empty() {
        return (node_modules_specifiers, ResultKind::NodeModules);
    }
    (relative_specifiers, ResultKind::Relative)
}

/// `func getLocalModuleSpecifier(...)`.
#[allow(clippy::too_many_arguments)]
fn get_local_module_specifier<S, H>(
    module_file_name: &RootedFilePath,
    info: &Info,
    compiler_options: &CompilerOptions,
    host: &H,
    import_mode: ResolutionMode,
    preferences: &ModuleSpecifierPreferences<'_, S, H>,
    paths_only: bool,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifier
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let paths = compiler_options.paths.as_ref();
    let root_dirs = compiler_options.get_effective_root_dirs();

    if paths_only && paths.is_none() {
        return ModuleSpecifier::default();
    }

    let source_directory = &info.source_directory;

    let allowed_endings =
        preferences.get_allowed_endings_in_preferred_order(import_mode, nodes, resolve);
    let mut relative_path = ModuleSpecifier::default();
    if let Some(root_dirs) = &root_dirs {
        if !root_dirs.is_empty() {
            relative_path = try_get_module_name_from_root_dirs(
                root_dirs,
                module_file_name,
                source_directory,
                &allowed_endings,
                compiler_options,
                host,
            );
        }
    }
    if relative_path.is_empty() {
        let relative_path_from_source = host
            .case_sensitivity()
            .relative_path_from_directory(source_directory, module_file_name);
        let path = match &relative_path_from_source {
            Some(relative) => relative.as_module_specifier().as_string().to_string(),
            None => module_file_name.as_string().to_string(),
        };
        relative_path = process_ending(
            &tspath::to_module_specifier(&path),
            module_file_name,
            &allowed_endings,
            compiler_options,
            Some(host),
        );
    }

    if (paths.is_none() && !compiler_options.get_resolve_package_json_imports())
        || preferences.relative_preference == RelativePreferenceKind::Relative
    {
        if paths_only {
            return ModuleSpecifier::default();
        }
        return relative_path;
    }

    let mut base_directory = host.base_directory();
    let paths_base_path = compiler_options.get_paths_base_path(&base_directory);
    if !paths_base_path.is_empty() {
        base_directory = paths_base_path;
    }
    let relative_to_base_url = get_relative_path_if_in_same_volume(
        module_file_name,
        &base_directory,
        host.case_sensitivity(),
    );
    if relative_to_base_url.is_empty() {
        if paths_only {
            return ModuleSpecifier::default();
        }
        return relative_path;
    }

    let mut from_package_json_imports = ModuleSpecifier::default();
    if !paths_only {
        from_package_json_imports = try_get_module_name_from_package_json_imports(
            module_file_name,
            source_directory,
            compiler_options,
            host,
            import_mode,
            prefers_ts_extension(&allowed_endings),
        );
    }

    let mut from_paths = String::new();
    if (paths_only || from_package_json_imports.is_empty())
        && let Some(paths) = paths
    {
        from_paths = try_get_module_name_from_paths(
            relative_to_base_url.as_string(),
            module_file_name,
            paths,
            &allowed_endings,
            &base_directory,
            host,
            compiler_options,
        );
    }

    if paths_only {
        return tspath::to_module_specifier(&from_paths);
    }

    let maybe_non_relative = if !from_package_json_imports.is_empty() {
        from_package_json_imports.as_string().to_string()
    } else {
        from_paths
    };
    if maybe_non_relative.is_empty() {
        return relative_path;
    }

    let relative_is_excluded =
        is_excluded_by_regex(relative_path.as_string(), preferences.exclude_regexes);
    let non_relative_is_excluded =
        is_excluded_by_regex(&maybe_non_relative, preferences.exclude_regexes);
    if !relative_is_excluded && non_relative_is_excluded {
        return relative_path;
    }
    if relative_is_excluded && !non_relative_is_excluded {
        return tspath::to_module_specifier(&maybe_non_relative);
    }

    if preferences.relative_preference == RelativePreferenceKind::NonRelative
        && !tspath::path_is_relative(&maybe_non_relative)
    {
        return tspath::to_module_specifier(&maybe_non_relative);
    }

    if preferences.relative_preference == RelativePreferenceKind::ExternalNonRelative
        && !tspath::path_is_relative(&maybe_non_relative)
    {
        let project_directory = if !compiler_options.config_file_path.is_empty() {
            host.case_sensitivity()
                .path_key(&compiler_options.config_file_path.directory().as_path())
        } else {
            host.case_sensitivity()
                .path_key(&host.base_directory().as_path())
        };
        let case_sensitivity = host.case_sensitivity();
        let canonical_source_directory = case_sensitivity.path_key(&source_directory.as_path());
        let module_path = case_sensitivity.path_key(&module_file_name.as_path());

        let source_is_internal = project_directory.contains_path(&canonical_source_directory);
        let target_is_internal = project_directory.contains_path(&module_path);
        if source_is_internal && !target_is_internal || !source_is_internal && target_is_internal {
            // 1. The import path crosses the boundary of the tsconfig.json-containing directory.
            //
            //      src/
            //        tsconfig.json
            //        index.ts -------
            //      lib/              | (path crosses tsconfig.json)
            //        imported.ts <---
            //
            return tspath::to_module_specifier(&maybe_non_relative);
        }

        let nearest_target_package_json =
            host.get_nearest_ancestor_directory_with_package_json(&module_file_name.directory());
        let nearest_source_package_json =
            host.get_nearest_ancestor_directory_with_package_json(source_directory);

        if !package_json_paths_are_equal(
            &nearest_target_package_json,
            &nearest_source_package_json,
            host.case_sensitivity(),
        ) {
            // 2. The importing and imported files are part of different packages.
            //
            //      packages/a/
            //        package.json
            //        index.ts --------
            //      packages/b/        | (path crosses package.json)
            //        package.json     |
            //        component.ts <---
            //
            return tspath::to_module_specifier(&maybe_non_relative);
        }

        return relative_path;
    }

    // Prefer a relative import over a baseUrl import if it has fewer components.
    if is_path_relative_to_parent(&tspath::to_relative_path(&maybe_non_relative))
        || count_path_components(relative_path.as_string())
            < count_path_components(&maybe_non_relative)
    {
        return relative_path;
    }
    tspath::to_module_specifier(&maybe_non_relative)
}

/// `func processEnding(...)`.
pub(crate) fn process_ending<H: ModuleSpecifierGenerationHost>(
    specifier: &ModuleSpecifier,
    source_file_name: &RootedFilePath,
    allowed_endings: &[ModuleSpecifierEnding],
    options: &CompilerOptions,
    host: Option<&H>,
) -> ModuleSpecifier {
    let file_name = specifier.as_string();
    if tspath::file_extension_is_one_of(
        file_name,
        &[
            tspath::EXTENSION_JSON,
            tspath::EXTENSION_MJS,
            tspath::EXTENSION_CJS,
        ],
    ) {
        return specifier.clone();
    }

    let no_extension = tspath::remove_file_extension(file_name);
    if file_name == no_extension {
        return specifier.clone();
    }

    let js_priority = allowed_endings
        .iter()
        .position(|&e| e == ModuleSpecifierEnding::JsExtension)
        .map(|p| p as i32)
        .unwrap_or(-1);
    let ts_priority = allowed_endings
        .iter()
        .position(|&e| e == ModuleSpecifierEnding::TsExtension)
        .map(|p| p as i32)
        .unwrap_or(-1);
    if tspath::file_extension_is_one_of(file_name, &[tspath::EXTENSION_MTS, tspath::EXTENSION_CTS])
        && ts_priority != -1
        && ts_priority < js_priority
    {
        return specifier.clone();
    }
    if tspath::file_extension_is_one_of(
        file_name,
        &[tspath::EXTENSION_DMTS, tspath::EXTENSION_DCTS],
    ) {
        let input_ext = tspath::get_declaration_file_extension(file_name);
        let ext = get_js_extension_for_declaration_file_extension(&input_ext);
        return tspath::to_module_specifier(&format!(
            "{}{}",
            tspath::remove_extension(file_name, &input_ext),
            ext
        ));
    }
    if tspath::file_extension_is_one_of(file_name, &[tspath::EXTENSION_MTS, tspath::EXTENSION_CTS])
    {
        return tspath::to_module_specifier(&format!(
            "{}{}",
            no_extension,
            get_js_extension_for_file(file_name, options)
        ));
    }
    if !tspath::file_extension_is_one_of(file_name, &[tspath::EXTENSION_DTS])
        && tspath::file_extension_is_one_of(file_name, &[tspath::EXTENSION_TS])
        && file_name.contains(".d.")
    {
        // `foo.d.json.ts` and the like - remap back to `foo.json`
        let result = try_get_real_file_name_for_non_js_declaration_file_name(file_name);
        if !result.is_empty() {
            return tspath::to_module_specifier(&result);
        }
    }

    match allowed_endings[0] {
        ModuleSpecifierEnding::Minimal => {
            let without_index = no_extension.strip_suffix("/index").unwrap_or(no_extension);
            if host.is_some()
                && without_index != no_extension
                && try_get_any_file_from_path(
                    host.unwrap(),
                    &tspath::rooted_file_path_from_path(source_file_name.directory().as_path()),
                )
            {
                // Can't remove index if there's a file by the same name as the directory.
                // Probably more callers should pass `host` so we can determine this?
                return tspath::to_module_specifier(no_extension);
            }
            tspath::to_module_specifier(without_index)
        }
        ModuleSpecifierEnding::Index => tspath::to_module_specifier(no_extension),
        ModuleSpecifierEnding::JsExtension => tspath::to_module_specifier(&format!(
            "{}{}",
            no_extension,
            get_js_extension_for_file(file_name, options)
        )),
        ModuleSpecifierEnding::TsExtension => {
            // For now, we don't know if this import is going to be type-only, which means we don't
            // know if a .d.ts extension is valid, so use no extension or a .js extension
            if tspath::is_declaration_file_name(file_name) {
                let mut extensionless_priority = -1i32;
                for (i, e) in allowed_endings.iter().enumerate() {
                    if *e == ModuleSpecifierEnding::Minimal || *e == ModuleSpecifierEnding::Index {
                        extensionless_priority = i as i32;
                        break;
                    }
                }
                if extensionless_priority != -1 && extensionless_priority < js_priority {
                    return tspath::to_module_specifier(no_extension);
                }
                return tspath::to_module_specifier(&format!(
                    "{}{}",
                    no_extension,
                    get_js_extension_for_file(file_name, options)
                ));
            }
            specifier.clone()
        }
    }
}

/// `func tryGetModuleNameFromRootDirs(...)`.
#[allow(clippy::too_many_arguments)]
fn try_get_module_name_from_root_dirs<H: ModuleSpecifierGenerationHost>(
    root_dirs: &[RootedDirectoryPath],
    module_file_name: &RootedFilePath,
    source_directory: &RootedDirectoryPath,
    allowed_endings: &[ModuleSpecifierEnding],
    compiler_options: &CompilerOptions,
    host: &H,
) -> ModuleSpecifier {
    let normalized_target_paths =
        get_paths_relative_to_root_dirs(module_file_name, root_dirs, host.case_sensitivity());
    if normalized_target_paths.is_empty() {
        return ModuleSpecifier::default();
    }

    let normalized_source_paths = get_paths_relative_to_root_dirs(
        &tspath::rooted_file_path_from_path(source_directory.as_path()),
        root_dirs,
        host.case_sensitivity(),
    );
    let mut shortest = ModuleSpecifier::default();
    let mut shortest_sep_count = 0;
    for source_path in &normalized_source_paths {
        for target_path in &normalized_target_paths {
            let candidate = host
                .case_sensitivity()
                .relative_path_from_relative_directory(source_path, target_path)
                .as_module_specifier();
            let candidate_sep_count = candidate.as_string().matches('/').count();
            if shortest.is_empty() || candidate_sep_count < shortest_sep_count {
                shortest = candidate;
                shortest_sep_count = candidate_sep_count;
            }
        }
    }

    if shortest.is_empty() {
        return ModuleSpecifier::default();
    }
    process_ending(
        &shortest,
        module_file_name,
        allowed_endings,
        compiler_options,
        Some(host),
    )
}

/// `type pkgJsonDirAttemptResult struct`.
#[derive(Default)]
struct PkgJsonDirAttemptResult {
    module_file_to_try: RootedFilePath,
    package_root_directory: RootedDirectoryPath,
    blocked_by_exports: bool,
    verbatim_from_exports: ModuleSpecifier,
}

/// `func tryGetModuleNameAsNodeModule(...)`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_get_module_name_as_node_module<S, H>(
    path_obj: &ModulePath,
    info: &Info,
    importing_source_file: &S,
    host: &H,
    options: &CompilerOptions,
    user_preferences: &UserPreferences,
    package_name_only: bool,
    override_mode: ResolutionMode,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifier
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let Some(parts) = get_node_module_path_parts(&path_obj.file_name) else {
        return ModuleSpecifier::default();
    };

    // Simplify the full file path to something that can be resolved by Node.
    let preferences = get_module_specifier_preferences(
        user_preferences,
        host,
        options,
        importing_source_file,
        "",
    );
    let allowed_endings = preferences.get_allowed_endings_in_preferred_order(
        RESOLUTION_MODE_NONE,
        nodes,
        resolve,
    );

    let case_sensitivity = host.case_sensitivity();
    let mut module_specifier = path_obj.file_name.as_string().to_string();
    let mut is_package_root_path = false;
    if !package_name_only {
        if parts.is_direct_node_modules_file {
            module_specifier = process_ending(
                &path_obj.file_name.as_module_specifier(),
                &path_obj.file_name,
                &allowed_endings,
                options,
                Some(host),
            )
            .as_string()
            .to_string();
        } else {
            let mut module_file_name = RootedFilePath::default();
            let mut package_root_directory = parts.package_root_directory.clone();
            let relative_components: Vec<&str> =
                parts.package_relative_path.as_string().split('/').collect();
            let mut i = 0usize;
            loop {
                let Some(package_path) = package_root_directory
                    .as_path()
                    .relative_to(&parts.top_level_node_modules_directory)
                else {
                    return ModuleSpecifier::default();
                };
                // If the module could be imported by a directory name, use that directory's name
                let pkg_json_results = try_directory_with_package_json(
                    &package_root_directory,
                    &parts.package_root_directory,
                    package_path.as_string(),
                    path_obj,
                    importing_source_file,
                    host,
                    override_mode,
                    options,
                    &allowed_endings,
                );
                let module_file_to_try = &pkg_json_results.module_file_to_try;
                if pkg_json_results.blocked_by_exports {
                    return ModuleSpecifier::default(); // File is under this package.json, but is not publicly exported - there's no way to name it via `node_modules` resolution
                }
                if !pkg_json_results.verbatim_from_exports.is_empty() {
                    return pkg_json_results.verbatim_from_exports;
                }
                //}
                if !pkg_json_results.package_root_directory.is_empty() {
                    module_specifier = pkg_json_results
                        .package_root_directory
                        .as_string()
                        .to_string();
                    is_package_root_path = true;
                    break;
                }
                if module_file_name.is_empty() {
                    module_file_name = module_file_to_try.clone();
                }
                if i >= relative_components.len() - 1 {
                    module_specifier = process_ending(
                        &module_file_name.as_module_specifier(),
                        &module_file_name,
                        &allowed_endings,
                        options,
                        Some(host),
                    )
                    .as_string()
                    .to_string();
                    break;
                }
                package_root_directory =
                    package_root_directory.resolve_directory(relative_components[i]);
                i += 1;
            }
        }
    }

    if path_obj.is_redirect && !is_package_root_path {
        return ModuleSpecifier::default();
    }

    let global_typings_cache_location = host.get_global_typings_cache_location();
    // Get a path that's relative to node_modules or the importing file's path
    // if node_modules folder is in this folder or any of its parent folders, no need to keep it.
    if !case_sensitivity.contains_path(
        &parts.top_level_node_modules_search_root,
        &info.source_directory.as_path(),
    ) || !global_typings_cache_location.is_empty()
        && case_sensitivity.contains_path(
            &parts.top_level_node_modules_search_root,
            &global_typings_cache_location.as_path(),
        )
    {
        return ModuleSpecifier::default();
    }

    // If the module was found in @types, get the actual Node package name
    let node_modules_prefix = tspath::ensure_trailing_directory_separator(
        parts.top_level_node_modules_directory.as_string(),
    );
    if !module_specifier.starts_with(node_modules_prefix.as_ref()) {
        return ModuleSpecifier::default();
    }
    let node_modules_directory_name = &module_specifier[node_modules_prefix.len()..];
    tspath::to_module_specifier(&module::get_package_name_from_types_package_name(
        node_modules_directory_name,
    ))
}

/// `func tryDirectoryWithPackageJson(...)`.
#[allow(clippy::too_many_arguments)]
fn try_directory_with_package_json<S, H>(
    package_root_directory: &RootedDirectoryPath,
    package_base_directory: &RootedDirectoryPath,
    package_name: &str,
    path_obj: &ModulePath,
    importing_source_file: &S,
    host: &H,
    override_mode: ResolutionMode,
    options: &CompilerOptions,
    allowed_endings: &[ModuleSpecifierEnding],
) -> PkgJsonDirAttemptResult
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let package_json_path = package_root_directory.resolve_file("package.json");
    let mut module_file_to_try = path_obj.file_name.clone();
    let mut maybe_blocked_by_types_versions = false;
    let package_json = host.get_package_json_info(&package_json_path);
    let Some(package_json) = package_json else {
        // No package.json exists; an index.js will still resolve as the package name
        let Some(relative) = module_file_to_try.relative_to(package_base_directory) else {
            panic!("module file was not contained by package root");
        };
        let file_name = relative.as_string();
        if file_name == "index.d.ts"
            || file_name == "index.js"
            || file_name == "index.ts"
            || file_name == "index.tsx"
        {
            return PkgJsonDirAttemptResult {
                module_file_to_try,
                package_root_directory: package_root_directory.clone(),
                ..Default::default()
            };
        } else {
            return PkgJsonDirAttemptResult {
                module_file_to_try,
                ..Default::default()
            };
        }
    };

    let mut import_mode = override_mode;
    if import_mode == RESOLUTION_MODE_NONE {
        import_mode = host.get_default_resolution_mode_for_file(importing_source_file);
    }

    let package_json_content = package_json.get_contents();
    if options.get_resolve_package_json_exports() {
        // The package name that we found in node_modules could be different from the package
        // name in the package.json content via url/filepath dependency specifiers. We need to
        // use the actual directory name, so don't look at `packageJsonContent.name` here.
        let package_name = module::get_package_name_from_types_package_name(package_name);

        // Determine resolution mode for package.json exports condition matching.
        // TypeScript's tryDirectoryWithPackageJson uses the importing file's mode (moduleSpecifiers.ts:1257),
        // but this causes incorrect exports resolution. We fix this by checking the target file's extension
        // using the logic from getImpliedNodeFormatForEmitWorker (program.ts:4827-4838).
        // .cjs/.cts/.d.cts → CommonJS → "require" condition
        // .mjs/.mts/.d.mts → ESM → "import" condition
        if path_obj.file_name.extension_is_one_of(&[
            tspath::EXTENSION_CJS,
            tspath::EXTENSION_CTS,
            tspath::EXTENSION_DCTS,
        ]) {
            import_mode = RESOLUTION_MODE_COMMON_JS;
        } else if path_obj.file_name.extension_is_one_of(&[
            tspath::EXTENSION_MJS,
            tspath::EXTENSION_MTS,
            tspath::EXTENSION_DMTS,
        ]) {
            import_mode = RESOLUTION_MODE_ESM;
        }

        let conditions = module::get_conditions(options, import_mode);

        let mut from_exports = ModuleSpecifier::default();
        if let Some(content) = &package_json_content {
            if content.exports.type_ != JSONValueType::NotPresent {
                from_exports = try_get_module_name_from_exports(
                    options,
                    host,
                    &path_obj.file_name,
                    package_root_directory,
                    &package_name,
                    &content.exports,
                    &conditions,
                );
            }
        }
        if !from_exports.is_empty() {
            return PkgJsonDirAttemptResult {
                verbatim_from_exports: from_exports,
                ..Default::default()
            };
        }
        if let Some(content) = &package_json_content {
            if content.exports.type_ != JSONValueType::NotPresent {
                return PkgJsonDirAttemptResult {
                    module_file_to_try,
                    blocked_by_exports: true,
                    ..Default::default()
                };
            }
        }
    }

    let mut version_paths = VersionPaths::default();
    if let Some(content) = &package_json_content {
        if content.types_versions.type_ == JSONValueType::Object {
            version_paths = content.get_version_paths(None);
        }
    }
    if version_paths.get_paths().is_some() {
        let Some(sub_module_name) = module_file_to_try.relative_to(package_root_directory) else {
            panic!("module file was not contained by package root");
        };
        let from_paths = try_get_module_name_from_paths(
            sub_module_name.as_string(),
            &module_file_to_try,
            version_paths.get_paths().unwrap(),
            allowed_endings,
            package_root_directory,
            host,
            options,
        );
        if from_paths.is_empty() {
            maybe_blocked_by_types_versions = true;
        } else {
            module_file_to_try = package_root_directory.resolve_file(&from_paths);
        }
    }
    // If the file is the main module, it can be imported by the package name
    let mut main_file_relative = "index.js".to_string();
    if let Some(content) = &package_json_content {
        if content.typings.valid {
            main_file_relative = content.typings.value.clone();
        } else if content.types.valid {
            main_file_relative = content.types.value.clone();
        } else if content.main.valid {
            main_file_relative = content.main.value.clone();
        }
    }

    // PORT: `!= core.Pattern{}` compares against the zero value; Pattern has
    // no PartialEq, so compare the fields. The match runs only when
    // `maybeBlockedByTypesVersions` is set, as in Go's `&&` short-circuit.
    if !main_file_relative.is_empty()
        && !(maybe_blocked_by_types_versions && {
            let parsed = module::try_parse_patterns(version_paths.get_paths());
            let matched = module::match_pattern_or_exact(&parsed, &main_file_relative);
            !(matched.text.is_empty() && matched.star_index == 0)
        })
    {
        // The 'main' file is also subject to mapping through typesVersions, and we couldn't come up with a path
        // explicitly through typesVersions, so if it matches a key in typesVersions now, it's not reachable.
        // (The only way this can happen is if some file in a package that's not resolvable from outside the
        // package got pulled into the program anyway, e.g. transitively through a file that *is* reachable. It
        // happens very easily in fourslash tests though, since every test file listed gets included. See
        // importNameCodeFix_typesVersions.ts for an example.)
        let case_sensitivity = host.case_sensitivity();
        let mut package_type = "";
        if let Some(content) = &package_json_content {
            package_type = &content.type_.value;
        }
        if is_package_main_file(
            &module_file_to_try,
            package_root_directory,
            &main_file_relative,
            package_type,
            case_sensitivity,
        ) {
            return PkgJsonDirAttemptResult {
                package_root_directory: package_root_directory.clone(),
                module_file_to_try,
                ..Default::default()
            };
        }
    }

    PkgJsonDirAttemptResult {
        module_file_to_try,
        ..Default::default()
    }
}

/// `func isPackageMainFile(...)`.
pub(crate) fn is_package_main_file(
    module_file_name: &RootedFilePath,
    package_root_directory: &RootedDirectoryPath,
    main_file_relative: &str,
    package_type: &str,
    case_sensitivity: CaseSensitivity,
) -> bool {
    let main_is_directory = tspath::has_trailing_directory_separator(main_file_relative);
    let main_export_file = package_root_directory.resolve_file(main_file_relative);

    if !main_is_directory
        && case_sensitivity.compare_file_name_stems(
            &main_export_file.remove_file_extension(),
            &module_file_name.remove_file_extension(),
        ) == 0
    {
        // An arbitrary removal of file extension for this comparison is almost certainly wrong.
        return true;
    }
    let main_export_directory = tspath::rooted_directory_path_from_path(main_export_file.as_path());
    package_type != "module"
        && !module_file_name
            .extension_is_one_of(tspath::EXTENSIONS_NOT_SUPPORTING_EXTENSIONLESS_RESOLUTION)
        && case_sensitivity.compare_paths(
            &module_file_name.directory().as_path(),
            &main_export_directory.as_path(),
        ) == 0
        && tspath::remove_file_extension(module_file_name.base_name()) == "index"
}

/// `func tryGetModuleNameFromExports(...)`.
fn try_get_module_name_from_exports<H: ModuleSpecifierGenerationHost>(
    options: &CompilerOptions,
    host: &H,
    target_file_name: &RootedFilePath,
    package_directory: &RootedDirectoryPath,
    package_name: &str,
    exports: &packagejson::ExportsOrImports,
    conditions: &[String],
) -> ModuleSpecifier {
    if exports.is_subpaths() {
        // sub-mappings
        // 3 cases:
        // * directory mappings (legacyish, key ends with / (technically allows index/extension resolution under cjs mode))
        // * pattern mappings (contains a *)
        // * exact mappings (no *, does not end with /)
        for (k, subk) in exports.as_object().entries() {
            let sub_package_name = tspath::resolve_path_without_trailing_directory_separator(
                package_name,
                &[k.as_str()],
            );
            let mut mode = MatchingMode::Exact;
            if k.ends_with('/') {
                mode = MatchingMode::Directory;
            } else if k.contains('*') {
                mode = MatchingMode::Pattern;
            }
            let result = try_get_module_name_from_exports_or_imports(
                options,
                host,
                target_file_name,
                package_directory,
                &sub_package_name,
                subk,
                conditions,
                mode,
                /*isImports*/ false,
                /*preferTsExtension*/ false,
            );
            if !result.is_empty() {
                return tspath::to_module_specifier(&result);
            }
        }
    }
    tspath::to_module_specifier(&try_get_module_name_from_exports_or_imports(
        options,
        host,
        target_file_name,
        package_directory,
        package_name,
        exports,
        conditions,
        MatchingMode::Exact,
        /*isImports*/ false,
        /*preferTsExtension*/ false,
    ))
}

/// `func tryGetModuleNameFromPackageJsonImports(...)`.
fn try_get_module_name_from_package_json_imports<H: ModuleSpecifierGenerationHost>(
    module_file_name: &RootedFilePath,
    source_directory: &RootedDirectoryPath,
    options: &CompilerOptions,
    host: &H,
    import_mode: ResolutionMode,
    prefer_ts_extension: bool,
) -> ModuleSpecifier {
    if !options.get_resolve_package_json_imports() {
        return ModuleSpecifier::default();
    }

    let ancestor_directory_with_package_json =
        host.get_nearest_ancestor_directory_with_package_json(source_directory);
    if ancestor_directory_with_package_json.is_empty() {
        return ModuleSpecifier::default();
    }
    let package_json_path = ancestor_directory_with_package_json.resolve_file("package.json");

    let Some(info) = host.get_package_json_info(&package_json_path) else {
        return ModuleSpecifier::default();
    };

    // PORT: Go dereferences `info.GetContents().Fields` unconditionally —
    // a nil contents would panic there too.
    let contents = info.get_contents().expect("GetContents returned nil");
    let imports = &contents.imports;
    match imports.type_ {
        JSONValueType::NotPresent | JSONValueType::Array | JSONValueType::String => {
            return ModuleSpecifier::default(); // not present or invalid for imports
        }
        JSONValueType::Object => {
            let conditions = module::get_conditions(options, import_mode);
            let top = imports.as_object();
            for (k, value) in top.entries() {
                if k.as_str() == "#" || k.as_str() == "#/" || !k.starts_with('#') {
                    continue; // invalid imports entry
                }
                if k.starts_with("#/")
                    && options.get_module_resolution_kind() != ModuleResolutionKind::NodeNext
                    && options.get_module_resolution_kind() != ModuleResolutionKind::Bundler
                {
                    continue; // "#/" imports keys are only valid in nodenext/bundler
                }
                let mut mode = MatchingMode::Exact;
                if k.ends_with('/') {
                    mode = MatchingMode::Directory;
                } else if k.contains('*') {
                    mode = MatchingMode::Pattern;
                }
                let result = try_get_module_name_from_exports_or_imports(
                    options,
                    host,
                    module_file_name,
                    &ancestor_directory_with_package_json,
                    k,
                    value,
                    &conditions,
                    mode,
                    true,
                    prefer_ts_extension,
                );
                if !result.is_empty() {
                    return tspath::to_module_specifier(&result);
                }
            }
        }
        _ => {}
    }

    ModuleSpecifier::default()
}

/// `type specPair struct`.
struct SpecPair {
    ending: ModuleSpecifierEnding,
    value: ModuleSpecifier,
}

/// Values of a `paths`/`typesVersions` map entry — `Vec<String>` in
/// `packagejson::VersionPaths`, `Option<Vec<String>>` in `CompilerOptions::paths`.
///
// PORT: `compilerOptions.Paths` is `*OrderedMap[string, []string]` in Go but
// `Option<Vec<String>>`-valued in Rust (JSON null); a `None` value iterates
// zero patterns, exactly like Go's nil slice.
trait PathMappingValues {
    fn path_values(&self) -> &[String];
}

impl PathMappingValues for Vec<String> {
    fn path_values(&self) -> &[String] {
        self
    }
}

impl PathMappingValues for Option<Vec<String>> {
    fn path_values(&self) -> &[String] {
        self.as_deref().unwrap_or(&[])
    }
}

/// `func tryGetModuleNameFromPaths(...)`.
#[allow(clippy::too_many_arguments)]
fn try_get_module_name_from_paths<V, H>(
    relative_to_base_url: &str,
    file_name: &RootedFilePath,
    paths: &OrderedMap<String, V>,
    allowed_endings: &[ModuleSpecifierEnding],
    base_directory: &RootedDirectoryPath,
    host: &H,
    compiler_options: &CompilerOptions,
) -> String
where
    V: PathMappingValues,
    H: ModuleSpecifierGenerationHost,
{
    let case_sensitivity = host.case_sensitivity();
    for (key, values) in paths.entries() {
        for pattern_text in values.path_values() {
            let normalized = tspath::normalize_path(pattern_text);
            let mut pattern = resolve_path_pattern_if_in_same_volume(
                &normalized,
                base_directory,
                case_sensitivity,
            );
            if pattern.is_empty() {
                pattern = normalized.to_string();
            }
            let cut = pattern.split_once('*');

            // In module resolution, if `pattern` itself has an extension, a file with that extension is looked up directly,
            // meaning a '.ts' or '.d.ts' extension is allowed to resolve. This is distinct from the case where a '*' substitution
            // causes a module specifier to have an extension, i.e. the extension comes from the module specifier in a JS/TS file
            // and matches the '*'. For example:
            //
            // Module Specifier      | Path Mapping (key: [pattern]) | Interpolation       | Resolution Action
            // ---------------------->------------------------------->--------------------->---------------------------------------------------------------
            // import "@app/foo"    -> "@app/*": ["./src/app/*.ts"] -> "./src/app/foo.ts" -> tryFile("./src/app/foo.ts") || [continue resolution algorithm]
            // import "@app/foo.ts" -> "@app/*": ["./src/app/*"]    -> "./src/app/foo.ts" -> [continue resolution algorithm]
            //
            // (https://github.com/microsoft/TypeScript/blob/ad4ded80e1d58f0bf36ac16bea71bc10d9f09895/src/compiler/moduleNameResolver.ts#L2509-L2516)
            //
            // The interpolation produced by both scenarios is identical, but only in the former, where the extension is encoded in
            // the path mapping rather than in the module specifier, will we prioritize a file lookup on the interpolation result.
            // (In fact, currently, the latter scenario will necessarily fail since no resolution mode recognizes '.ts' as a valid
            // extension for a module specifier.)
            //
            // Here, this means we need to be careful about whether we generate a match from the target filename (typically with a
            // .ts extension) or the possible relative module specifiers representing that file:
            //
            // Filename            | Relative Module Specifier Candidates         | Path Mapping                 | Filename Result    | Module Specifier Results
            // --------------------<----------------------------------------------<------------------------------<-------------------||----------------------------
            // dist/haha.d.ts      <- dist/haha, dist/haha.js                     <- "@app/*": ["./dist/*.d.ts"] <- @app/haha        || (none)
            // dist/haha.d.ts      <- dist/haha, dist/haha.js                     <- "@app/*": ["./dist/*"]      <- (none)           || @app/haha, @app/haha.js
            // dist/foo/index.d.ts <- dist/foo, dist/foo/index, dist/foo/index.js <- "@app/*": ["./dist/*.d.ts"] <- @app/foo/index   || (none)
            // dist/foo/index.d.ts <- dist/foo, dist/foo/index, dist/foo/index.js <- "@app/*": ["./dist/*"]      <- (none)           || @app/foo, @app/foo/index, @app/foo/index.js
            // dist/wow.js.js      <- dist/wow.js, dist/wow.js.js                 <- "@app/*": ["./dist/*.js"]   <- @app/wow.js      || @app/wow, @app/wow.js
            //
            // The "Filename Result" can be generated only if `pattern` has an extension. Care must be taken that the list of
            // relative module specifiers to run the interpolation (a) is actually valid for the module resolution mode, (b) takes
            // into account the existence of other files (e.g. 'dist/wow.js' cannot refer to 'dist/wow.js.js' if 'dist/wow.js'
            // exists) and (c) that they are ordered by preference. The last row shows that the filename result and module
            // specifier results are not mutually exclusive. Note that the filename result is a higher priority in module
            // resolution, but as long criteria (b) above is met, I don't think its result needs to be the highest priority result
            // in module specifier generation. I have included it last, as it's difficult to tell exactly where it should be
            // sorted among the others for a particular value of `importModuleSpecifierEnding`.

            let mut candidates: Vec<SpecPair> = Vec::new();
            for &ending in allowed_endings {
                let result = process_ending(
                    &tspath::to_module_specifier(relative_to_base_url),
                    file_name,
                    &[ending],
                    compiler_options,
                    Some(host),
                );
                candidates.push(SpecPair {
                    ending,
                    value: result,
                });
            }
            if !tspath::try_get_extension_from_path(&pattern).is_empty() {
                candidates.push(SpecPair {
                    ending: ModuleSpecifierEnding::JsExtension,
                    value: tspath::to_module_specifier(relative_to_base_url),
                });
            }

            if let Some((prefix, suffix)) = cut {
                for c in &candidates {
                    let value = c.value.as_string();
                    if value.len() >= prefix.len() + suffix.len()
                        && stringutil::has_prefix(
                            value.as_bytes(),
                            prefix.as_bytes(),
                            case_sensitivity.is_case_sensitive(),
                        ) // TODO: possible strada bug: these are not case-switched in strada
                        && stringutil::has_suffix(
                            value.as_bytes(),
                            suffix.as_bytes(),
                            case_sensitivity.is_case_sensitive(),
                        )
                        && validate_ending(c, relative_to_base_url, file_name, compiler_options, host)
                    {
                        let matched_star = &value[prefix.len()..value.len() - suffix.len()];
                        if !tspath::path_is_relative(matched_star) {
                            return replace_first_star(key, matched_star);
                        }
                    }
                }
            } else if candidates.iter().any(|c| {
                c.ending != ModuleSpecifierEnding::Minimal && pattern == c.value.as_string()
            }) || candidates.iter().any(|c| {
                c.ending == ModuleSpecifierEnding::Minimal
                    && pattern == c.value.as_string()
                    && validate_ending(c, relative_to_base_url, file_name, compiler_options, host)
            }) {
                return key.clone();
            }
        }
    }
    String::new()
}

/// `func validateEnding(...)`.
fn validate_ending<H: ModuleSpecifierGenerationHost>(
    c: &SpecPair,
    relative_to_base_url: &str,
    file_name: &RootedFilePath,
    compiler_options: &CompilerOptions,
    host: &H,
) -> bool {
    // Optimization: `removeExtensionAndIndexPostFix` can query the file system (a good bit) if `ending` is `Minimal`, the basename
    // is 'index', and a `host` is provided. To avoid that until it's unavoidable, we ran the function with no `host` above. Only
    // here, after we've checked that the minimal ending is indeed a match (via the length and prefix/suffix checks / `some` calls),
    // do we check that the host-validated result is consistent with the answer we got before. If it's not, it falls back to the
    // `ModuleSpecifierEnding.Index` result, which should already be in the list of candidates if `Minimal` was. (Note: the assumption here is
    // that every module resolution mode that supports dropping extensions also supports dropping `/index`. Like literally
    // everything else in this file, this logic needs to be updated if that's not true in some future module resolution mode.)
    c.ending != ModuleSpecifierEnding::Minimal
        || c.value
            == process_ending(
                &tspath::to_module_specifier(relative_to_base_url),
                file_name,
                &[c.ending],
                compiler_options,
                Some(host),
            )
}

/// `func tryGetModuleNameFromExportsOrImports(...)`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_get_module_name_from_exports_or_imports<H: ModuleSpecifierGenerationHost>(
    options: &CompilerOptions,
    host: &H,
    target_file_name: &RootedFilePath,
    package_directory: &RootedDirectoryPath,
    package_name: &str,
    exports: &packagejson::ExportsOrImports,
    conditions: &[String],
    mode: MatchingMode,
    is_imports: bool,
    prefer_ts_extension: bool,
) -> String {
    let package_specifier = tspath::to_module_specifier(package_name);
    match exports.type_ {
        JSONValueType::NotPresent => String::new(),
        JSONValueType::String => {
            let str_value = exports.as_string();

            // possible strada bug? Always uses compilerOptions of the host project, not those applicable to the targeted package.json!
            let mut output_file = RootedFilePath::default();
            let mut declaration_file = RootedFilePath::default();
            if is_imports {
                output_file = tsc_outputpaths::get_output_js_file_name_worker(
                    target_file_name,
                    options,
                    host,
                );
                declaration_file = tsc_outputpaths::get_output_declaration_file_name_worker(
                    target_file_name,
                    options,
                    host,
                );
            }

            let mut extension_swapped_target = RootedFilePath::default();
            if target_file_name.has_ts_file_extension() {
                extension_swapped_target = target_file_name.remove_file_extension().append_suffix(
                    module::try_get_js_extension_for_file_name(target_file_name, options),
                );
            }
            let can_try_ts_extension =
                prefer_ts_extension && target_file_name.has_implementation_ts_file_extension();

            let case_sensitivity = host.case_sensitivity();

            match mode {
                MatchingMode::Exact => {
                    if tspath::has_trailing_directory_separator(str_value) {
                        return String::new();
                    }
                    let resolved_target = package_directory.resolve_file(str_value);
                    if !extension_swapped_target.is_empty()
                        && case_sensitivity
                            .compare_file_paths(&extension_swapped_target, &resolved_target)
                            == 0
                        || case_sensitivity.compare_file_paths(target_file_name, &resolved_target)
                            == 0
                        || !output_file.is_empty()
                            && case_sensitivity.compare_file_paths(&output_file, &resolved_target)
                                == 0
                        || !declaration_file.is_empty()
                            && case_sensitivity
                                .compare_file_paths(&declaration_file, &resolved_target)
                                == 0
                    {
                        return package_name.to_string();
                    }
                }
                MatchingMode::Directory => {
                    let resolved_target = package_directory
                        .resolve_directory(tspath::remove_trailing_directory_separator(str_value));
                    if can_try_ts_extension
                        && case_sensitivity.contains_path(
                            &tspath::rooted_directory_path_from_path(target_file_name.as_path()),
                            &resolved_target.as_path(),
                        )
                    {
                        // PORT: Go ignores the `ok` result; a failed relativize
                        // yields an empty fragment rather than skipping.
                        let fragment = case_sensitivity
                            .relative_path_from_directory(&resolved_target, target_file_name)
                            .unwrap_or_default();
                        return package_specifier
                            .resolve(&[str_value, fragment.as_string()])
                            .as_string()
                            .to_string();
                    }
                    if !extension_swapped_target.is_empty()
                        && case_sensitivity
                            .contains_file_path(&resolved_target, &extension_swapped_target)
                    {
                        let fragment = case_sensitivity
                            .relative_path_from_directory(
                                &resolved_target,
                                &extension_swapped_target,
                            )
                            .unwrap_or_default();
                        return package_specifier
                            .resolve(&[str_value, fragment.as_string()])
                            .as_string()
                            .to_string();
                    }
                    if !can_try_ts_extension
                        && case_sensitivity.contains_file_path(&resolved_target, target_file_name)
                    {
                        let fragment = case_sensitivity
                            .relative_path_from_directory(&resolved_target, target_file_name)
                            .unwrap_or_default();
                        return package_specifier
                            .resolve(&[str_value, fragment.as_string()])
                            .as_string()
                            .to_string();
                    }
                    if !output_file.is_empty()
                        && case_sensitivity.contains_file_path(&resolved_target, &output_file)
                    {
                        let fragment = case_sensitivity
                            .relative_path_from_directory(&resolved_target, &output_file)
                            .unwrap_or_default();
                        return package_specifier
                            .combine_relative(&fragment)
                            .as_string()
                            .to_string();
                    }
                    if !declaration_file.is_empty()
                        && case_sensitivity.contains_file_path(&resolved_target, &declaration_file)
                    {
                        let fragment = case_sensitivity
                            .relative_path_from_directory(&resolved_target, &declaration_file)
                            .unwrap_or_default();
                        let js_extension =
                            get_js_extension_for_file_name(&declaration_file, options);
                        let fragment_with_js_extension = fragment.change_extension(&js_extension);
                        return package_specifier
                            .combine_relative(&fragment_with_js_extension)
                            .as_string()
                            .to_string();
                    }
                }
                MatchingMode::Pattern => {
                    let path_or_pattern =
                        tspath::resolve_path(package_directory.as_string(), &[str_value]);
                    let (leading_slice, trailing_slice, _) = match path_or_pattern.split_once('*') {
                        Some((a, b)) => (a, b, true),
                        None => (path_or_pattern.as_str(), "", false),
                    };
                    let case_sensitivity = host.case_sensitivity();
                    let target_file_path = target_file_name.as_string();
                    if can_try_ts_extension
                        && stringutil::has_prefix_and_suffix_without_overlap(
                            target_file_path.as_bytes(),
                            leading_slice.as_bytes(),
                            trailing_slice.as_bytes(),
                            case_sensitivity.is_case_sensitive(),
                        )
                    {
                        let star_replacement = &target_file_path
                            [leading_slice.len()..target_file_path.len() - trailing_slice.len()];
                        return replace_first_star(package_name, star_replacement);
                    }
                    let extension_swapped_target_string = extension_swapped_target.as_string();
                    if !extension_swapped_target_string.is_empty()
                        && stringutil::has_prefix_and_suffix_without_overlap(
                            extension_swapped_target_string.as_bytes(),
                            leading_slice.as_bytes(),
                            trailing_slice.as_bytes(),
                            case_sensitivity.is_case_sensitive(),
                        )
                    {
                        let star_replacement = &extension_swapped_target_string[leading_slice.len()
                            ..extension_swapped_target_string.len() - trailing_slice.len()];
                        return replace_first_star(package_name, star_replacement);
                    }
                    if !can_try_ts_extension
                        && stringutil::has_prefix_and_suffix_without_overlap(
                            target_file_path.as_bytes(),
                            leading_slice.as_bytes(),
                            trailing_slice.as_bytes(),
                            case_sensitivity.is_case_sensitive(),
                        )
                    {
                        let star_replacement = &target_file_path
                            [leading_slice.len()..target_file_path.len() - trailing_slice.len()];
                        return replace_first_star(package_name, star_replacement);
                    }
                    let output_file_string = output_file.as_string();
                    if !output_file_string.is_empty()
                        && stringutil::has_prefix_and_suffix_without_overlap(
                            output_file_string.as_bytes(),
                            leading_slice.as_bytes(),
                            trailing_slice.as_bytes(),
                            case_sensitivity.is_case_sensitive(),
                        )
                    {
                        let star_replacement = &output_file_string
                            [leading_slice.len()..output_file_string.len() - trailing_slice.len()];
                        return replace_first_star(package_name, star_replacement);
                    }
                    let declaration_file_string = declaration_file.as_string();
                    if !declaration_file_string.is_empty()
                        && stringutil::has_prefix_and_suffix_without_overlap(
                            declaration_file_string.as_bytes(),
                            leading_slice.as_bytes(),
                            trailing_slice.as_bytes(),
                            case_sensitivity.is_case_sensitive(),
                        )
                    {
                        let star_replacement = &declaration_file_string[leading_slice.len()
                            ..declaration_file_string.len() - trailing_slice.len()];
                        let substituted = replace_first_star(package_name, star_replacement);
                        let js_extension =
                            module::try_get_js_extension_for_file_name(&declaration_file, options);
                        if !js_extension.is_empty() {
                            return tspath::change_full_extension(&substituted, js_extension)
                                .into_owned();
                        }
                    }
                }
            }
            String::new()
        }
        JSONValueType::Array => {
            let arr = exports.as_array();
            for e in arr {
                let result = try_get_module_name_from_exports_or_imports(
                    options,
                    host,
                    target_file_name,
                    package_directory,
                    package_name,
                    e,
                    conditions,
                    mode,
                    is_imports,
                    prefer_ts_extension,
                );
                if !result.is_empty() {
                    return result;
                }
            }
            String::new()
        }
        JSONValueType::Object => {
            // conditional mapping
            let obj = exports.as_object();
            for (key, value) in obj.entries() {
                if key == "default"
                    || conditions.contains(key)
                    || conditions.iter().any(|c| c == "types")
                        && module::is_applicable_versioned_types_key(key)
                {
                    let result = try_get_module_name_from_exports_or_imports(
                        options,
                        host,
                        target_file_name,
                        package_directory,
                        package_name,
                        value,
                        conditions,
                        mode,
                        is_imports,
                        prefer_ts_extension,
                    );
                    if !result.is_empty() {
                        return result;
                    }
                }
            }
            String::new()
        }
        JSONValueType::Null => String::new(),
        _ => String::new(),
    }
}

// `importingSourceFile` and `importingSourceFileName`? Why not just use `importingSourceFile.path`?
// Because when this is called by the declaration emitter, `importingSourceFile` is the implementation
// file, but `importingSourceFileName` and `toFileName` refer to declaration files (the former to the
// one currently being produced; the latter to the one being imported). We need an implementation file
// just to get its `impliedNodeFormat` and to detect certain preferences from existing import module
// specifiers.

/// `func GetModuleSpecifier(...)`.
#[allow(clippy::too_many_arguments)]
pub fn get_module_specifier<H>(
    compiler_options: &CompilerOptions,
    host: &H,
    importing_source_file: &tsc_ast::ast_generated::SourceFile,
    importing_source_file_name: &RootedFilePath,
    old_import_specifier: &ModuleSpecifier,
    to_file_name: &RootedFilePath,
    options: &ModuleSpecifierOptions,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifier
where
    H: ModuleSpecifierGenerationHost,
{
    get_module_specifier_with_preferences(
        compiler_options,
        host,
        importing_source_file,
        importing_source_file_name,
        old_import_specifier,
        to_file_name,
        &UserPreferences::default(),
        options,
        nodes,
        resolve,
    )
}

/// `func UpdateModuleSpecifier(...)`.
#[allow(clippy::too_many_arguments)]
pub fn update_module_specifier<H>(
    compiler_options: &CompilerOptions,
    host: &H,
    importing_source_file: &tsc_ast::ast_generated::SourceFile,
    importing_source_file_name: &RootedFilePath,
    old_import_specifier: &ModuleSpecifier,
    to_file_name: &RootedFilePath,
    user_preferences: &UserPreferences,
    options: &ModuleSpecifierOptions,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifier
where
    H: ModuleSpecifierGenerationHost,
{
    get_module_specifier_with_preferences(
        compiler_options,
        host,
        importing_source_file,
        importing_source_file_name,
        old_import_specifier,
        to_file_name,
        user_preferences,
        options,
        nodes,
        resolve,
    )
}

/// `func getModuleSpecifierWithPreferences(...)`.
#[allow(clippy::too_many_arguments)]
fn get_module_specifier_with_preferences<S, H>(
    compiler_options: &CompilerOptions,
    host: &H,
    importing_source_file: &S,
    importing_source_file_name: &RootedFilePath,
    old_import_specifier: &ModuleSpecifier,
    to_file_name: &RootedFilePath,
    user_preferences: &UserPreferences,
    options: &ModuleSpecifierOptions,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifier
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let info = get_info(importing_source_file_name, host);
    let module_paths = get_all_module_paths(
        &info,
        to_file_name,
        host,
        compiler_options,
        user_preferences,
        options,
    );
    let preferences = get_module_specifier_preferences(
        user_preferences,
        host,
        compiler_options,
        importing_source_file,
        old_import_specifier.as_string(),
    );

    let mut resolution_mode = options.override_import_mode;
    if resolution_mode == RESOLUTION_MODE_NONE {
        resolution_mode = host.get_default_resolution_mode_for_file(importing_source_file);
    }

    for module_path in &module_paths {
        let first_defined = try_get_module_name_as_node_module(
            module_path,
            &info,
            importing_source_file,
            host,
            compiler_options,
            user_preferences,
            false, // packageNameOnly
            options.override_import_mode,
            nodes,
            resolve,
        );
        if !first_defined.is_empty() {
            return first_defined;
        }
    }

    get_local_module_specifier(
        to_file_name,
        &info,
        compiler_options,
        host,
        resolution_mode,
        &preferences,
        false,
        nodes,
        resolve,
    )
}
