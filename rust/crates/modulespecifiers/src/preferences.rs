// Ported from tsc/internal/modulespecifiers/preferences.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_core::compileroptions::{
    RESOLUTION_MODE_COMMON_JS, RESOLUTION_MODE_ESM, RESOLUTION_MODE_NONE, ResolutionMode,
};
use tsc_core::options_generated::{CompilerOptions, ModuleResolutionKind};
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::types::{
    ImportModuleSpecifierEndingPreference, ImportModuleSpecifierPreference, ModuleSpecifierEnding,
    ModuleSpecifierGenerationHost, RelativePreferenceKind, SourceFileForSpecifierGeneration,
    UserPreferences,
};

// Program errors validate that `noEmit` or `emitDeclarationOnly` is also set,
// so this function doesn't check them to avoid propagating errors.
//
// PORT: same body as `CompilerOptions::allow_importing_ts_extensions_from`
// (`GetAllowImportingTsExtensions() || fromFileName.IsDeclarationFile()`).
fn should_allow_importing_ts_extension(
    compiler_options: &CompilerOptions,
    from_file_name: &RootedFilePath,
) -> bool {
    compiler_options.allow_importing_ts_extensions_from(from_file_name)
}

fn uses_extensions_on_imports<S: SourceFileForSpecifierGeneration>(
    file: &S,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> bool {
    for &import_ref in file.imports() {
        // Import specifier ids live in `file`'s own arena, which is not
        // necessarily `nodes` — route through `arena_of_id` (Go reads them
        // through raw pointers on the shared heap).
        let buf = crate::types::arena_of_id(nodes, resolve, import_ref);
        let text = buf[import_ref].text(&buf);
        if tspath::path_is_relative(&text)
            && !tspath::file_extension_is_one_of(
                &text,
                tspath::EXTENSIONS_NOT_SUPPORTING_EXTENSIONLESS_RESOLUTION,
            )
        {
            return tspath::has_ts_file_extension(&text) || tspath::has_js_file_extension(&text);
        }
    }
    false
}

fn infer_preference<S: SourceFileForSpecifierGeneration>(
    resolution_mode: ResolutionMode,
    source_file: Option<&S>,
    module_resolution_is_node_next: bool,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifierEnding {
    let mut uses_js_extensions = false;
    let specifiers: &[NodeId] = match source_file {
        Some(file) if !file.imports().is_empty() => file.imports(),
        Some(file) if file.is_js() => {
            // !!! TODO: JS support
            // specifiers = core.Map(getRequiresAtTopOfFile(sourceFile), func(d *ast.Node) *ast.Node { return d.arguments[0] })
            &[]
        }
        _ => &[],
    };

    for &specifier in specifiers {
        let buf = crate::types::arena_of_id(nodes, resolve, specifier);
        let path = buf[specifier].text(&buf);
        if tspath::path_is_relative(&path) {
            // !!! TODO: proper resolutionMode support
            if module_resolution_is_node_next && resolution_mode == RESOLUTION_MODE_COMMON_JS
            /* && getModeForUsageLocation(sourceFile!, specifier, compilerOptions) === ModuleKind.ESNext */
            {
                // We're trying to decide a preference for a CommonJS module specifier, but looking at an ESM import.
                continue;
            }
            if tspath::file_extension_is_one_of(
                &path,
                tspath::EXTENSIONS_NOT_SUPPORTING_EXTENSIONLESS_RESOLUTION,
            ) {
                // These extensions are not optional, so do not indicate a preference.
                continue;
            }
            if tspath::has_ts_file_extension(&path) {
                return ModuleSpecifierEnding::TsExtension;
            }
            if tspath::has_js_file_extension(&path) {
                uses_js_extensions = true;
            }
        }
    }

    if uses_js_extensions {
        return ModuleSpecifierEnding::JsExtension;
    }
    ModuleSpecifierEnding::Minimal
}

fn get_module_specifier_ending_preference<S: SourceFileForSpecifierGeneration>(
    pref: ImportModuleSpecifierEndingPreference,
    resolution_mode: ResolutionMode,
    compiler_options: &CompilerOptions,
    source_file: Option<&S>,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifierEnding {
    let module_resolution = compiler_options.get_module_resolution_kind();
    let module_resolution_is_node_next = ModuleResolutionKind::Node16 <= module_resolution
        && module_resolution <= ModuleResolutionKind::NodeNext;

    if pref == ImportModuleSpecifierEndingPreference::JS
        || resolution_mode == RESOLUTION_MODE_ESM && module_resolution_is_node_next
    {
        // Extensions are explicitly requested or required. Now choose between .js and .ts.
        if !should_allow_importing_ts_extension(compiler_options, &RootedFilePath::default()) {
            return ModuleSpecifierEnding::JsExtension;
        }
        // `allowImportingTsExtensions` is a strong signal, so use .ts unless the file
        // already uses .js extensions and no .ts extensions.
        if infer_preference(
            resolution_mode,
            source_file,
            module_resolution_is_node_next,
            nodes,
            resolve,
        ) != ModuleSpecifierEnding::JsExtension
        {
            return ModuleSpecifierEnding::TsExtension;
        }
        return ModuleSpecifierEnding::JsExtension;
    }

    if pref == ImportModuleSpecifierEndingPreference::MINIMAL {
        return ModuleSpecifierEnding::Minimal;
    }

    if pref == ImportModuleSpecifierEndingPreference::INDEX {
        return ModuleSpecifierEnding::Index;
    }

    // No preference was specified.
    // Look at imports and/or requires to guess whether .js, .ts, or extensionless imports are preferred.
    // N.B. that `Index` detection is not supported since it would require file system probing to do
    // accurately, and more importantly, literally nobody wants `Index` and its existence is a mystery.
    if !should_allow_importing_ts_extension(compiler_options, &RootedFilePath::default()) {
        // If .ts imports are not valid, we only need to see one .js import to go with that.
        if source_file.is_some_and(|f| uses_extensions_on_imports(f, nodes, resolve)) {
            return ModuleSpecifierEnding::JsExtension;
        }
        return ModuleSpecifierEnding::Minimal;
    }

    infer_preference(
        resolution_mode,
        source_file,
        module_resolution_is_node_next,
        nodes,
        resolve,
    )
}

fn get_preferred_ending<S, H>(
    prefs: &UserPreferences,
    host: &H,
    compiler_options: &CompilerOptions,
    importing_source_file: &S,
    old_import_specifier: &str,
    mut resolution_mode: ResolutionMode,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifierEnding
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    if !old_import_specifier.is_empty() {
        if tspath::has_js_file_extension(old_import_specifier) {
            return ModuleSpecifierEnding::JsExtension;
        }
        if old_import_specifier.ends_with("/index") {
            return ModuleSpecifierEnding::Index;
        }
    }
    if resolution_mode == RESOLUTION_MODE_NONE {
        resolution_mode = host.get_default_resolution_mode_for_file(importing_source_file);
    }
    get_module_specifier_ending_preference(
        prefs.import_module_specifier_ending,
        resolution_mode,
        compiler_options,
        Some(importing_source_file),
        nodes,
        resolve,
    )
}

/// `type ModuleSpecifierPreferences struct`.
///
// PORT: Go stores a closure (`getAllowedEndingsInPreferredOrder`) capturing
// prefs/host/options/importingSourceFile/oldImportSpecifier. A Rust closure
// cannot be stored without boxing and lifetime parameters, so the struct
// keeps the captures as fields and the method re-dispatches to the free
// function — the observable behavior is identical.
pub(crate) struct ModuleSpecifierPreferences<'a, S, H> {
    pub(crate) relative_preference: RelativePreferenceKind,
    pub(crate) exclude_regexes: &'a [String],
    prefs: &'a UserPreferences,
    host: &'a H,
    compiler_options: &'a CompilerOptions,
    importing_source_file: &'a S,
    old_import_specifier: &'a str,
}

impl<S, H> ModuleSpecifierPreferences<'_, S, H>
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    pub(crate) fn get_allowed_endings_in_preferred_order(
        &self,
        syntax_implied_node_format: ResolutionMode,
        nodes: &[Node],
        resolve: crate::types::NodeResolver,
    ) -> Vec<ModuleSpecifierEnding> {
        get_allowed_endings_in_preferred_order(
            self.prefs,
            self.host,
            self.compiler_options,
            self.importing_source_file,
            self.old_import_specifier,
            syntax_implied_node_format,
            nodes,
            resolve,
        )
    }
}

/// `func GetAllowedEndingsInPreferredOrder(...)`.
pub fn get_allowed_endings_in_preferred_order<S, H>(
    prefs: &UserPreferences,
    host: &H,
    compiler_options: &CompilerOptions,
    importing_source_file: &S,
    old_import_specifier: &str,
    syntax_implied_node_format: ResolutionMode,
    nodes: &[Node],
    resolve: crate::types::NodeResolver,
) -> Vec<ModuleSpecifierEnding>
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let mut preferred_ending = get_preferred_ending(
        prefs,
        host,
        compiler_options,
        importing_source_file,
        old_import_specifier,
        RESOLUTION_MODE_NONE,
        nodes,
        resolve,
    );
    let resolution_mode = host.get_default_resolution_mode_for_file(importing_source_file);
    if resolution_mode != syntax_implied_node_format {
        preferred_ending = get_preferred_ending(
            prefs,
            host,
            compiler_options,
            importing_source_file,
            old_import_specifier,
            syntax_implied_node_format,
            nodes,
            resolve,
        );
    }
    let module_resolution = compiler_options.get_module_resolution_kind();
    let module_resolution_is_node_next = ModuleResolutionKind::Node16 <= module_resolution
        && module_resolution <= ModuleResolutionKind::NodeNext;
    let allow_importing_ts_extension =
        should_allow_importing_ts_extension(compiler_options, importing_source_file.file_name());
    // TypeScript uses `(syntaxImpliedNodeFormat ?? impliedNodeFormat)` here - fall back to the
    // file's default resolution mode when no syntax-implied mode is given.
    let mut effective_syntax_mode = syntax_implied_node_format;
    if effective_syntax_mode == RESOLUTION_MODE_NONE {
        effective_syntax_mode = resolution_mode;
    }
    if effective_syntax_mode == RESOLUTION_MODE_ESM && module_resolution_is_node_next {
        if allow_importing_ts_extension {
            return vec![
                ModuleSpecifierEnding::TsExtension,
                ModuleSpecifierEnding::JsExtension,
            ];
        }
        return vec![ModuleSpecifierEnding::JsExtension];
    }
    match preferred_ending {
        ModuleSpecifierEnding::JsExtension => {
            if allow_importing_ts_extension {
                return vec![
                    ModuleSpecifierEnding::JsExtension,
                    ModuleSpecifierEnding::TsExtension,
                    ModuleSpecifierEnding::Minimal,
                    ModuleSpecifierEnding::Index,
                ];
            }
            vec![
                ModuleSpecifierEnding::JsExtension,
                ModuleSpecifierEnding::Minimal,
                ModuleSpecifierEnding::Index,
            ]
        }
        ModuleSpecifierEnding::TsExtension => {
            vec![
                ModuleSpecifierEnding::TsExtension,
                ModuleSpecifierEnding::Minimal,
                ModuleSpecifierEnding::JsExtension,
                ModuleSpecifierEnding::Index,
            ]
        }
        ModuleSpecifierEnding::Index => {
            if allow_importing_ts_extension {
                return vec![
                    ModuleSpecifierEnding::Index,
                    ModuleSpecifierEnding::Minimal,
                    ModuleSpecifierEnding::TsExtension,
                    ModuleSpecifierEnding::JsExtension,
                ];
            }
            vec![
                ModuleSpecifierEnding::Index,
                ModuleSpecifierEnding::Minimal,
                ModuleSpecifierEnding::JsExtension,
            ]
        }
        ModuleSpecifierEnding::Minimal => {
            if allow_importing_ts_extension {
                return vec![
                    ModuleSpecifierEnding::Minimal,
                    ModuleSpecifierEnding::Index,
                    ModuleSpecifierEnding::TsExtension,
                    ModuleSpecifierEnding::JsExtension,
                ];
            }
            vec![
                ModuleSpecifierEnding::Minimal,
                ModuleSpecifierEnding::Index,
                ModuleSpecifierEnding::JsExtension,
            ]
        }
    }
}

pub(crate) fn get_module_specifier_preferences<'a, S, H>(
    prefs: &'a UserPreferences,
    host: &'a H,
    compiler_options: &'a CompilerOptions,
    importing_source_file: &'a S,
    old_import_specifier: &'a str,
) -> ModuleSpecifierPreferences<'a, S, H>
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let excludes = &prefs.auto_import_specifier_exclude_regexes[..];
    let mut relative_preference = RelativePreferenceKind::Shortest;
    if !old_import_specifier.is_empty() {
        if tspath::is_external_module_name_relative(old_import_specifier) {
            relative_preference = RelativePreferenceKind::Relative;
        } else {
            relative_preference = RelativePreferenceKind::NonRelative;
        }
    } else {
        match prefs.import_module_specifier_preference {
            ImportModuleSpecifierPreference::RELATIVE => {
                relative_preference = RelativePreferenceKind::Relative;
            }
            ImportModuleSpecifierPreference::NON_RELATIVE => {
                relative_preference = RelativePreferenceKind::NonRelative;
            }
            ImportModuleSpecifierPreference::PROJECT_RELATIVE => {
                relative_preference = RelativePreferenceKind::ExternalNonRelative;
            }
            // all others are shortest
            _ => {}
        }
    }

    ModuleSpecifierPreferences {
        exclude_regexes: excludes,
        relative_preference,
        prefs,
        host,
        compiler_options,
        importing_source_file,
        old_import_specifier,
    }
}
