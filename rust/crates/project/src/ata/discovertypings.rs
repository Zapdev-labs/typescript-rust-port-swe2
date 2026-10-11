// Ported from tsc/internal/project/ata/discovertypings.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use rustc_hash::FxHashMap;
use tsc_collections::SyncMap;
use tsc_core::nodemodules::non_relative_module_name_for_typing_cache;
use tsc_core::version::version_major_minor;
use tsc_json as json;
use tsc_packagejson::{self as packagejson, DependencyFields};
use tsc_project_logging::Logger;
use tsc_semver as semver;
use tsc_tspath::{
    self as tspath, RootedDirectoryPath, RootedFilePath, RootedPath, EXTENSION_JSX,
    EXTENSION_JSON,
};
use tsc_vfs::vfsmatch;
use tsc_vfs::Vfs;

use super::ata::{CachedTyping, TypingsInfo};
use super::typesmap::SAFE_FILE_NAME_TO_TYPE_NAME;

/// PORT: Go used `""` as the "inferred but not yet located" sentinel value in
/// `inferredTypings`; `None` carries that state here.
type InferredTypings = FxHashMap<String, Option<RootedFilePath>>;

/// `func isTypingUpToDate(cachedTyping *CachedTyping, availableTypingVersions map[string]string) bool`
pub(crate) fn is_typing_up_to_date(
    cached_typing: &CachedTyping,
    available_typing_versions: &FxHashMap<String, String>,
) -> bool {
    let use_version = available_typing_versions
        .get(&format!("ts{}", version_major_minor()))
        .unwrap_or_else(|| {
            available_typing_versions
                .get("latest")
                .expect("types registry entry must have a 'latest' version")
        });
    let available_version = semver::must_parse(use_version);
    semver::Version::compare(Some(&available_version), Some(&cached_typing.version)) <= 0
}

/// `func DiscoverTypings(...) (cachedTypingPaths, newTypingNames, filesToWatch)`
#[allow(clippy::too_many_arguments)]
pub fn discover_typings(
    fs: &Arc<dyn Vfs>,
    logger: &dyn Logger,
    typings_info: &TypingsInfo,
    file_names: &[RootedFilePath],
    project_root_path: &RootedDirectoryPath,
    package_name_to_typing_location: &SyncMap<String, Arc<CachedTyping>>,
    types_registry: &FxHashMap<String, FxHashMap<String, String>>,
) -> (Vec<RootedFilePath>, Vec<String>, Vec<RootedPath>) {
    let mut cached_typing_paths: Vec<RootedFilePath> = Vec::new();
    let mut new_typing_names: Vec<String> = Vec::new();
    let mut files_to_watch: Vec<RootedPath> = Vec::new();

    // A typing name to typing file path mapping
    let mut inferred_typings: InferredTypings = FxHashMap::default();

    // Only infer typings for .js and .jsx files
    let file_names: Vec<&RootedFilePath> = file_names
        .iter()
        .filter(|file_name| file_name.has_js_file_extension())
        .collect();

    if let Some(include) = &typings_info.type_acquisition.include {
        add_inferred_typings(
            logger,
            &mut inferred_typings,
            include.iter().map(String::as_str),
            "Explicitly included types",
        );
    }
    let exclude = typings_info.type_acquisition.exclude.clone().unwrap_or_default();

    // Directories to search for package.json, bower.json and other typing information
    if typings_info.compiler_options.types.is_none() {
        let mut possible_search_dirs: FxHashMap<RootedDirectoryPath, bool> = FxHashMap::default();
        for file_name in &file_names {
            possible_search_dirs.insert(file_name.directory(), true);
        }
        possible_search_dirs.insert(project_root_path.clone(), true);
        for search_dir in possible_search_dirs.keys() {
            add_typing_names_and_get_files_to_watch(
                fs,
                logger,
                &mut inferred_typings,
                &mut files_to_watch,
                search_dir,
                "bower.json",
                "bower_components",
            );
            add_typing_names_and_get_files_to_watch(
                fs,
                logger,
                &mut inferred_typings,
                &mut files_to_watch,
                search_dir,
                "package.json",
                "node_modules",
            );
        }
    }

    if !typings_info
        .type_acquisition
        .disable_filename_based_type_acquisition
        .is_true()
    {
        get_typing_names_from_source_file_names(logger, &mut inferred_typings, &file_names);
    }

    // add typings for unresolved imports
    let mut modules: Vec<String> = Vec::new();
    if let Some(unresolved_imports) = &typings_info.unresolved_imports {
        modules.reserve(unresolved_imports.len());
        for module in unresolved_imports.keys() {
            modules.push(non_relative_module_name_for_typing_cache(module).to_string());
        }
        modules.sort();
        modules.dedup();
    }
    add_inferred_typings(
        logger,
        &mut inferred_typings,
        modules.iter().map(String::as_str),
        "Inferred typings from unresolved imports",
    );

    // Remove typings that the user has added to the exclude list
    for exclude_typing_name in &exclude {
        inferred_typings.remove(exclude_typing_name);
        logger.log(format_args!(
            "ATA:: Typing for {exclude_typing_name} is in exclude list, will be ignored."
        ));
    }

    // Add the cached typing locations for inferred typings that are already installed
    package_name_to_typing_location.range(|name, typing| {
        if let Some(registry_entry) = types_registry.get(&name) {
            if !matches!(inferred_typings.get(&name), Some(Some(_)))
                && is_typing_up_to_date(&typing, registry_entry)
            {
                inferred_typings.insert(name, Some(typing.typings_location.clone()));
            }
        }
        true
    });

    for (typing, inferred) in inferred_typings {
        if let Some(inferred) = inferred {
            cached_typing_paths.push(inferred);
        } else {
            new_typing_names.push(typing);
        }
    }
    logger.log(format_args!(
        "ATA:: Finished typings discovery: cachedTypingsPaths: {:?} newTypingNames: {:?}, filesToWatch {:?}",
        cached_typing_paths, new_typing_names, files_to_watch
    ));
    (cached_typing_paths, new_typing_names, files_to_watch)
}

/// `func addInferredTyping(...)`
fn add_inferred_typing(inferred_typings: &mut InferredTypings, typing_name: &str) {
    inferred_typings.entry(typing_name.to_string()).or_insert(None);
}

/// `func addInferredTypings(...)`
fn add_inferred_typings<'a>(
    logger: &dyn Logger,
    inferred_typings: &mut InferredTypings,
    typing_names: impl Iterator<Item = &'a str>,
    message: &str,
) {
    let typing_names: Vec<&str> = typing_names.collect();
    logger.log(format_args!("ATA:: {message}: {typing_names:?}"));
    for typing_name in typing_names {
        add_inferred_typing(inferred_typings, typing_name);
    }
}

/// `func getTypingNamesFromSourceFileNames(...)`
///
/// Infer typing names from given file names. For example, the file name
/// "jquery-min.2.3.4.js" should be inferred to the 'jquery' typing name; and
/// "angular-route.1.2.3.js" should be inferred to the 'angular-route' typing
/// name.
fn get_typing_names_from_source_file_names(
    logger: &dyn Logger,
    inferred_typings: &mut InferredTypings,
    file_names: &[&RootedFilePath],
) {
    let mut has_jsx_file = false;
    let mut from_file_names: Vec<&'static str> = Vec::new();
    for file_name in file_names {
        has_jsx_file = has_jsx_file || file_name.extension_is(EXTENSION_JSX);
        let lower_name = tspath::to_file_name_lower_case(file_name.base_name());
        let inferred_typing_name = tspath::remove_file_extension(&lower_name);
        let cleaned_typing_name = remove_min_and_version_numbers(inferred_typing_name);
        if let Some(type_name) = SAFE_FILE_NAME_TO_TYPE_NAME.get(cleaned_typing_name) {
            from_file_names.push(type_name);
        }
    }
    if !from_file_names.is_empty() {
        add_inferred_typings(
            logger,
            inferred_typings,
            from_file_names.into_iter(),
            "Inferred typings from file names",
        );
    }
    if has_jsx_file {
        logger.log(format_args!(
            "ATA:: Inferred 'react' typings due to presence of '.jsx' extension"
        ));
        add_inferred_typing(inferred_typings, "react");
    }
}

/// `func addTypingNamesAndGetFilesToWatch(...) []tspath.RootedPath`
///
/// Adds inferred typings from manifest/module pairs (think package.json +
/// node_modules).
fn add_typing_names_and_get_files_to_watch(
    fs: &Arc<dyn Vfs>,
    logger: &dyn Logger,
    inferred_typings: &mut InferredTypings,
    files_to_watch: &mut Vec<RootedPath>,
    project_root_path: &RootedDirectoryPath,
    manifest_name: &str,
    modules_dir_name: &str,
) {
    // First, we check the manifests themselves. They're not
    // _required_, but they allow us to do some filtering when dealing
    // with big flat dep directories.
    let manifest_path = project_root_path.resolve_file(manifest_name);
    let mut manifest_typing_names: Vec<String> = Vec::new();
    if let Some(manifest_contents) = fs.read_file(&manifest_path) {
        files_to_watch.push(manifest_path.as_path());
        if let Ok(manifest) = json::unmarshal::<DependencyFields>(manifest_contents.as_bytes(), &[]) {
            for deps in [
                &manifest.dependencies,
                &manifest.dev_dependencies,
                &manifest.optional_dependencies,
                &manifest.peer_dependencies,
            ] {
                if let Some(deps) = deps.get_value() {
                    manifest_typing_names.extend(deps.keys().cloned());
                }
            }
            add_inferred_typings(
                logger,
                inferred_typings,
                manifest_typing_names.iter().map(String::as_str),
                &format!("Typing names in '{}' dependencies", manifest_path.as_string()),
            );
        }
    }

    // Now we scan the directories for typing information in
    // already-installed dependencies (if present). Note that this
    // step happens regardless of whether a manifest was present,
    // which is certainly a valid configuration, if an unusual one.
    let packages_folder_path = project_root_path.resolve_directory(modules_dir_name);
    files_to_watch.push(packages_folder_path.as_path());
    if !fs.directory_exists(&packages_folder_path) {
        return;
    }

    // There's two cases we have to take into account here:
    // 1. If manifest is undefined, then we're not using a manifest.
    //    That means that we should scan _all_ dependencies at the top
    //    level of the modulesDir.
    // 2. If manifest is defined, then we can do some special
    //    filtering to reduce the amount of scanning we need to do.
    //
    // Previous versions of this algorithm checked for a `_requiredBy`
    // field in the package.json, but that field is only present in
    // `npm@>=3 <7`.

    // Package names that do **not** provide their own typings, so
    // we'll look them up.
    let mut package_names: Vec<String> = Vec::new();

    let mut dependency_manifest_names: Vec<RootedFilePath> = Vec::new();
    if !manifest_typing_names.is_empty() {
        // This is #2 described above (manifest present → filtered scan).
        for typing_name in &manifest_typing_names {
            dependency_manifest_names.push(
                packages_folder_path
                    .resolve_file(&tspath::combine_paths(typing_name, &[manifest_name])),
            );
        }
    } else {
        // And #1. Depth = 3 because scoped packages look like `node_modules/@foo/bar/package.json`
        let depth = 3;
        for manifest_path in vfsmatch::read_directory::<&str>(
            fs,
            &packages_folder_path,
            &[EXTENSION_JSON],
            &[],
            &[],
            depth,
        ) {
            if manifest_path.base_name() != manifest_name {
                continue;
            }

            // It's ok to treat
            // `node_modules/@foo/bar/package.json` as a manifest,
            // but not `node_modules/jquery/nested/package.json`.
            // We only assume depth 3 is ok for formally scoped
            // packages. So that needs this dance here.

            let path_components = manifest_path.components();
            let len_path_components = path_components.len();
            let is_scoped = path_components[len_path_components - 3].starts_with('@');

            if (is_scoped
                && tspath::to_file_name_lower_case(&path_components[len_path_components - 4])
                    == modules_dir_name) // `node_modules/@foo/bar`
                || (!is_scoped
                    && tspath::to_file_name_lower_case(&path_components[len_path_components - 3])
                        == modules_dir_name)
            // `node_modules/foo`
            {
                dependency_manifest_names.push(manifest_path);
            }
        }
    }

    logger.log(format_args!(
        "ATA:: Searching for typing names in {}; all files: {:?}",
        packages_folder_path.as_string(), dependency_manifest_names
    ));

    // Once we have the names of things to look up, we iterate over
    // and either collect their included typings, or add them to the
    // list of typings we need to look up separately.
    for manifest_path in dependency_manifest_names {
        let Some(manifest_contents) = fs.read_file(&manifest_path) else {
            continue;
        };
        let Ok(manifest) = packagejson::parse(manifest_contents.as_bytes()) else {
            continue;
        };
        // If the package has its own d.ts typings, those will take precedence. Otherwise the
        // package name will be used to download d.ts files from DefinitelyTyped
        if manifest.name.value.is_empty() {
            continue;
        }
        let mut own_types = &manifest.types.value;
        if own_types.is_empty() {
            own_types = &manifest.typings.value;
        }
        if !own_types.is_empty() {
            let absolute_path = manifest_path.directory().resolve_file(own_types);
            if fs.file_exists(&absolute_path) {
                logger.log(format_args!(
                    "ATA::     Package '{}' provides its own types.",
                    manifest.name.value
                ));
                inferred_typings
                    .insert(manifest.name.value.clone(), Some(absolute_path));
            } else {
                logger.log(format_args!(
                    "ATA::     Package '{}' provides its own types but they are missing.",
                    manifest.name.value
                ));
            }
        } else {
            package_names.push(manifest.name.value.clone());
        }
    }
    add_inferred_typings(
        logger,
        inferred_typings,
        package_names.iter().map(String::as_str),
        "    Found package names",
    );
}

/// `func removeMinAndVersionNumbers(fileName string) string`
///
/// Takes a string like "jquery-min.4.2.3" and returns "jquery"
fn remove_min_and_version_numbers(file_name: &str) -> &str {
    // We used to use the regex /[.-]((min)|(\d+(\.\d+)*))$/ and would just .replace it twice.
    // Unfortunately, that regex has O(n^2) performance because v8 doesn't match from the end of the string.
    // Instead, we now essentially scan the filename (backwards) ourselves.
    let bytes = file_name.as_bytes();
    let mut end = bytes.len();
    let mut pos = end;
    while pos > 0 {
        let ch = bytes[pos - 1];
        if ch.is_ascii_digit() {
            // Match a \d+ segment
            while pos > 0 {
                pos -= 1;
                if pos == 0 || !bytes[pos - 1].is_ascii_digit() {
                    break;
                }
            }
        } else if pos > 4 && (ch == b'n' || ch == b'N') {
            // Looking for "min" or "MIN"
            // Already matched the 'n'
            pos -= 1;
            if bytes[pos - 1] != b'i' && bytes[pos - 1] != b'I' {
                break;
            }
            pos -= 1;
            if bytes[pos - 1] != b'm' && bytes[pos - 1] != b'M' {
                break;
            }
            pos -= 1;
        } else {
            // This character is not part of either suffix pattern
            break;
        }

        if pos == 0 {
            break;
        }
        let sep = bytes[pos - 1];
        if sep != b'-' && sep != b'.' {
            break;
        }
        pos -= 1;
        end = pos;
    }
    &file_name[0..end]
}
