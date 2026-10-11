// Ported from tsc/internal/ls/autoimport/specifiers.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_modulespecifiers::ResultKind;
use tsc_modulespecifiers::util::{is_excluded_by_regex, process_entrypoint_ending};
use tsc_tspath::ModuleSpecifier;

use crate::autoimport::export::Export;
use crate::autoimport::view::View;

impl View<'_> {
    /// `View.GetModuleSpecifier` — `(specifier, kind)`; `specifier` empty +
    /// `ResultKindNone` mirrors Go's `"", ResultKindNone` returns.
    ///
    /// PORT: `user_preferences` is the full `lsutil.UserPreferences` (as in
    /// Go); the `tsc_modulespecifiers` subset is derived via
    /// `module_specifier_preferences()` where the API requires it.
    pub(crate) fn get_module_specifier(
        &self,
        export: &Export,
        user_preferences: &tsc_lsutil::UserPreferences,
    ) -> (ModuleSpecifier, ResultKind) {
        let module_specifier_preferences = user_preferences.module_specifier_preferences();
        let exclude_regexes = &user_preferences.auto_import_specifier_exclude_regexes;

        if !export.unresolved_module_specifier.as_string().is_empty() {
            let mut specifier = export.unresolved_module_specifier.clone();
            if specifier.is_relative() {
                let importing_dir = {
                    let nodes = self.program.nodes(self.from_file.file_index());
                    nodes[self.from_file]
                        .as_source_file()
                        .file_name()
                        .directory()
                };
                let Some(relative_path) = self
                    .program
                    .case_sensitivity()
                    .relative_path_from_directory(&importing_dir, &export.module_file_name)
                else {
                    return (ModuleSpecifier::default(), ResultKind::None);
                };
                specifier = relative_path.as_module_specifier();
            }
            if is_excluded_by_regex(specifier.as_string(), exclude_regexes) {
                return (ModuleSpecifier::default(), ResultKind::None);
            }
            return (specifier, ResultKind::Relative);
        }

        if let Some(specifier) = export.export_id.module_id.as_module_specifier() {
            if is_excluded_by_regex(specifier.as_string(), exclude_regexes) {
                return (ModuleSpecifier::default(), ResultKind::None);
            }
            return (specifier.clone(), ResultKind::Ambient);
        }

        if !export.package_name.is_empty() {
            let entrypoints = self.registry.entrypoints.get(&export.path);
            if let Some(entrypoints) = entrypoints {
                for entrypoint in entrypoints {
                    if tsc_collections::Set::is_subset_of(
                        entrypoint.include_conditions.as_ref(),
                        Some(&self.conditions),
                    ) && !tsc_collections::Set::intersects(
                        Some(&self.conditions),
                        entrypoint.exclude_conditions.as_ref(),
                    ) {
                        let specifier = {
                            let nodes = self.program.nodes(self.from_file.file_index());
                            process_entrypoint_ending(
                                entrypoint,
                                &module_specifier_preferences,
                                &*self.program,
                                &self.program.options(),
                                nodes[self.from_file].as_source_file(),
                                &self.get_allowed_endings(),
                                &nodes,
                                &|_| None,
                            )
                        };
                        if !is_excluded_by_regex(specifier.as_string(), exclude_regexes) {
                            return (specifier, ResultKind::NodeModules);
                        }
                    }
                }
                return (ModuleSpecifier::default(), ResultKind::None);
            }
        }

        let cache = self
            .registry
            .specifier_cache
            .get(&self.importing_file_path)
            .cloned();
        let cache = cache.expect("specifier cache missing for importing file");
        if export.package_name.is_empty()
            && let Some(specifier) = cache.load(&export.path)
        {
            if specifier.as_string().is_empty() {
                return (ModuleSpecifier::default(), ResultKind::None);
            }
            return (specifier, ResultKind::Relative);
        }

        let (specifiers, kind) = {
            let nodes = self.program.nodes(self.from_file.file_index());
            tsc_modulespecifiers::get_module_specifiers_for_file_with_info(
                nodes[self.from_file].as_source_file(),
                &export.module_file_name,
                &self.program.options(),
                &*self.program,
                &module_specifier_preferences,
                &tsc_modulespecifiers::ModuleSpecifierOptions::default(),
                true, /*forAutoImports*/
                &nodes,
                &|_| None,
            )
        };
        // !!! unsure when this could return multiple specifiers combined with the
        //     new node_modules code. Possibly with local symlinks, which should be
        //     very rare.
        for specifier in specifiers {
            if specifier.as_string().contains("/node_modules/") {
                continue;
            }
            cache.store(export.path.clone(), specifier.clone());
            return (specifier, kind);
        }
        cache.store(export.path.clone(), ModuleSpecifier::default());
        (ModuleSpecifier::default(), ResultKind::None)
    }
}
