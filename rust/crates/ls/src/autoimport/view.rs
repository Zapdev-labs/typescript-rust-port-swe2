// Ported from tsc/internal/ls/autoimport/view.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(arena): `importingFile *ast.SourceFile` → `from_file: NodeId`; file
// data is read through `program.nodes(from_file.file_index())`.
//
// PORT(ownership): `registry *Registry` → `&'a Registry` (borrowed from the
// host; the registry is immutable once built).
//
// Lazy fields (`existingImports`, `shouldUseRequireForFixes`,
// `allowedEndings`) sit in `Cell`/`RefCell` because `View` methods are `&self`.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use tsc_ast::NodeId;
use tsc_checker::checker_core::Checker;
use tsc_collections::{MultiMap, Set};
use tsc_compiler::program::Program;
use tsc_core::tristate::Tristate;
use tsc_lsproto::Position;
use tsc_lsutil::UserPreferences;
use tsc_modulespecifiers::ModuleSpecifierEnding;
use tsc_tspath::PathKey;

use crate::autoimport::export::{Export, ExportID, ModuleID};
use crate::autoimport::fix::Fix;
use crate::autoimport::registry::{ProjectId, Registry, RegistryBucket};

/// `type View struct`.
pub struct View<'a> {
    /// `registry`.
    pub(crate) registry: &'a Registry,
    /// `importingFile`.
    pub(crate) from_file: NodeId,
    /// `importingFilePath`.
    pub(crate) importing_file_path: PathKey,
    /// `program`.
    pub(crate) program: Rc<Program>,
    /// `checker`.
    pub(crate) type_checker: Rc<RefCell<Checker>>,
    /// `preferences`.
    pub(crate) user_preferences: UserPreferences,
    /// `projectID`.
    pub(crate) project_id: ProjectId,

    /// `allowedEndings`.
    pub(crate) allowed_endings: RefCell<Option<Vec<ModuleSpecifierEnding>>>,
    /// `conditions`.
    pub(crate) conditions: Set<String>,
    /// `shouldUseUriStyleNodeCoreModules`.
    pub(crate) should_use_uri_style_node_core_modules: Tristate,
    /// `existingImports`.
    pub(crate) existing_imports: RefCell<Option<MultiMap<ModuleID, ExistingImport>>>,
    /// `shouldUseRequireForFixes`.
    pub(crate) should_use_require_for_fixes: Cell<Option<bool>>,
}

impl<'a> View<'a> {
    /// `NewView`.
    pub fn new(
        registry: &'a Registry,
        from_file: NodeId,
        project_id: ProjectId,
        program: Rc<Program>,
        type_checker: &Rc<RefCell<Checker>>,
        preferences: UserPreferences,
    ) -> Rc<View<'a>> {
        let mut importing_file_path = {
            let nodes = program.nodes(from_file.file_index());
            nodes[from_file].as_source_file().path_key().clone()
        };
        {
            let nodes = program.nodes(from_file.file_index());
            if let Some(canonical) = nodes[from_file].as_source_file().canonical_source_file() {
                let nodes2 = program.nodes(canonical.file_index());
                importing_file_path = nodes2[canonical].as_source_file().path_key().clone();
            }
        }
        let resolution_mode = {
            let nodes = program.nodes(from_file.file_index());
            program.get_default_resolution_mode_for_file(nodes[from_file].as_source_file())
        };
        let should_use_uri_style = {
            let nodes = program.nodes(from_file.file_index());
            // `UsesUriStyleNodeCoreModules` isn't implemented on `Program`
            // (it lives in `lsutil`); the `Tristate` impl forwards the flag.
            let uri_flag = program.uses_uri_style_node_core_modules();
            tsc_lsutil::should_use_uri_style_node_core_modules(&nodes, from_file, &uri_flag)
        };
        Rc::new(View {
            registry,
            from_file,
            importing_file_path,
            program: program.clone(),
            type_checker: type_checker.clone(),
            user_preferences: preferences,
            project_id,
            allowed_endings: RefCell::new(None),
            conditions: tsc_collections::new_set_from_items(tsc_module::get_conditions(
                &program.options(),
                resolution_mode,
            )),
            should_use_uri_style_node_core_modules: should_use_uri_style,
            existing_imports: RefCell::new(None),
            should_use_require_for_fixes: Cell::new(None),
        })
    }

    /// `getAllowedEndings`.
    pub(crate) fn get_allowed_endings(&self) -> Vec<ModuleSpecifierEnding> {
        if self.allowed_endings.borrow().is_none() {
            let nodes = self.program.nodes(self.from_file.file_index());
            let resolution_mode = self
                .program
                .get_default_resolution_mode_for_file(nodes[self.from_file].as_source_file());
            *self.allowed_endings.borrow_mut() = Some(
                tsc_modulespecifiers::preferences::get_allowed_endings_in_preferred_order(
                    &self.user_preferences.module_specifier_preferences(),
                    &*self.program,
                    &self.program.options(),
                    nodes[self.from_file].as_source_file(),
                    "",
                    resolution_mode,
                    &nodes,
                    &|_| None,
                ),
            );
        }
        self.allowed_endings.borrow().clone().unwrap()
    }

    /// `View.Search`.
    pub fn search(&self, query: &str, kind: QueryKind) -> Vec<Rc<Export>> {
        self.search_impl(|bucket| {
            let index = bucket
                .index
                .as_ref()
                .expect("registry bucket index not built")
                .borrow();
            match kind {
                QueryKind::WordPrefix => index.search_word_prefix(query),
                QueryKind::ExactMatch => index.find(query, true),
                QueryKind::CaseInsensitiveMatch => index.find(query, false),
            }
        })
    }

    /// `View.SearchByExportID`.
    pub fn search_by_export_id(&self, id: &ExportID) -> Vec<Rc<Export>> {
        self.search_impl(|bucket| {
            let index = bucket
                .index
                .as_ref()
                .expect("registry bucket index not built")
                .borrow();
            index
                .entries
                .iter()
                .filter(|e| e.export_id == *id)
                .cloned()
                .collect()
        })
    }

    /// `View.search`.
    fn search_impl(
        &self,
        search_fn: impl Fn(&RegistryBucket) -> Vec<Rc<Export>>,
    ) -> Vec<Rc<Export>> {
        let mut results: Vec<Rc<Export>> = Vec::new();
        let importing_path = {
            let nodes = self.program.nodes(self.from_file.file_index());
            nodes[self.from_file].as_source_file().path_key().clone()
        };

        if let Some(bucket) = self.registry.projects.get(&self.project_id) {
            for e in search_fn(bucket) {
                if let Some(module_path) = e.export_id.module_id.as_path_key()
                    && *module_path == importing_path
                {
                    // Don't auto-import from the importing file itself
                    continue;
                }
                results.push(e);
            }
        }

        // Compute the set of packages accessible to the importing file.
        // This includes packages from package.json dependencies (aggregated
        // from ancestor directories) plus packages that are directly imported
        // by the project's program files. If no package.json is found,
        // allowedPackages remains nil and all packages are allowed.
        let mut allowed_packages: Option<Set<String>> = None;
        importing_path
            .parent()
            .for_each_ancestor_directory(|dir_path| {
                if let Some(dir) = self.registry.directories.get(dir_path)
                    && let Some(pj) = &dir.package_json
                    && pj.exists()
                    && pj.contents.as_ref().is_some_and(|c| c.parseable)
                {
                    // Initialize to empty set if this is the first
                    // package.json we've seen
                    let pkgs = allowed_packages.get_or_insert_with(Set::new);
                    crate::autoimport::util::add_package_json_dependencies(
                        pj.contents.as_ref().unwrap(),
                        pkgs,
                    );
                }
                ((), false)
            });
        // If we found at least one package.json, also include packages
        // directly imported by the project
        if allowed_packages.is_some()
            && let Some(bucket) = self.registry.projects.get(&self.project_id)
        {
            allowed_packages = Set::unioned_with(
                allowed_packages.as_ref(),
                bucket.resolved_package_names.as_deref(),
            );
        }

        let mut exclude_packages: Set<String> = Set::new();
        importing_path
            .parent()
            .for_each_ancestor_directory(|dir_path| {
                if let Some(node_modules_bucket) = self.registry.node_modules.get(dir_path) {
                    for e in search_fn(node_modules_bucket) {
                        // Exclude packages found in lower node_modules
                        // (shadowing)
                        if exclude_packages.has(&e.package_name) {
                            continue;
                        }
                        // If allowedPackages is nil, no package.json was
                        // found, so include all packages. Otherwise, only
                        // include packages that are dependencies or directly
                        // imported.
                        if let Some(allowed) = &allowed_packages
                            && !allowed.has(&e.package_name)
                        {
                            continue;
                        }
                        results.push(e);
                    }

                    // As we go up the directory tree, exclude packages found
                    // in lower node_modules.
                    for pkg_name in node_modules_bucket.package_files.keys() {
                        exclude_packages.add(pkg_name.clone());
                    }
                }
                ((), false)
            });
        results
    }

    /// `GetCompletions` — `prefix` is the lower-cased token text at
    /// `position`.
    pub fn get_completions(
        &self,
        prefix: &str,
        position: &Position,
        for_jsx: bool,
        is_type_only_location: bool,
    ) -> Vec<FixAndExport> {
        let results = self.search(prefix, QueryKind::WordPrefix);

        #[derive(PartialEq, Eq, Hash)]
        struct ExportGroupKey {
            target: ExportID,
            name: String,
            ambient_module_or_package_name: String,
        }
        let mut grouped: HashMap<ExportGroupKey, Vec<Rc<Export>>> =
            HashMap::with_capacity(results.len());
        'outer: for e in results {
            let name = e.name().to_string();
            if !tsc_scanner::utilities::is_identifier_text(
                &name,
                tsc_core::languagevariant::LanguageVariant::Standard,
            ) {
                continue;
            }
            if for_jsx
                && !(name
                    .chars()
                    .next()
                    .is_some_and(crate::autoimport::util::is_upper)
                    || e.is_renameable())
            {
                continue;
            }
            let mut target = e.export_id.clone();
            if e.target != ExportID::default() {
                target = e.target.clone();
            }
            let mut key = ExportGroupKey {
                target,
                name,
                ambient_module_or_package_name: tsc_core::core::first_non_zero([
                    e.ambient_module_name().to_string(),
                    e.package_name.clone(),
                ]),
            };
            if e.package_name == "@types/node"
                || e.path
                    .contains_lowercase_directory_sequence("/node_modules/@types/node/")
            {
                if tsc_core::nodemodules::UNPREFIXED_NODE_CORE_MODULES
                    .contains(key.ambient_module_or_package_name.as_str())
                {
                    // Group URI-style and non-URI style node core modules
                    // together so the ranking logic is allowed to drop one
                    // if an explicit preference is detected.
                    key.ambient_module_or_package_name =
                        format!("node:{}", key.ambient_module_or_package_name);
                }
            }
            if let Some(existing) = grouped.get_mut(&key) {
                for (i, ex) in existing.iter().enumerate() {
                    if e.export_id == ex.export_id {
                        existing[i] = Rc::new(Export {
                            export_id: e.export_id.clone(),
                            module_file_name: e.module_file_name.clone(),
                            unresolved_module_specifier: e.unresolved_module_specifier.clone(),
                            package_name: e.package_name.clone(),
                            is_type_only: e.is_type_only || ex.is_type_only,
                            syntax: e.syntax.min(ex.syntax),
                            flags: e.flags | ex.flags,
                            script_element_kind: e.script_element_kind.min(ex.script_element_kind),
                            script_element_kind_modifiers: e.script_element_kind_modifiers
                                | ex.script_element_kind_modifiers,
                            local_name: e.local_name.clone(),
                            target: e.target.clone(),
                            path: e.path.clone(),
                            ..Default::default()
                        });
                        continue 'outer;
                    }
                }
            }
            grouped.entry(key).or_default().push(e);
        }

        let mut fixes: Vec<FixAndExport> = Vec::new();
        for exps in grouped.values() {
            let mut fixes_for_group: Vec<FixAndExport> = Vec::with_capacity(exps.len());
            for e in exps {
                for fix in self.get_fixes(e, for_jsx, is_type_only_location, Some(position.clone()))
                {
                    fixes_for_group.push(FixAndExport {
                        fix,
                        export: e.clone(),
                    });
                }
            }
            fixes.extend(tsc_core::core::min_all_func(&fixes_for_group, |a, b| {
                self.compare_fixes_for_ranking(&a.fix, &b.fix)
            }));
        }

        // The client will do additional sorting by SortText and Label, so we
        // don't need to consider the name in our sorting here; we only need
        // to produce a stable relative ordering between completions that the
        // client will consider equivalent.
        fixes.sort_by(|a, b| self.compare_fixes_for_sorting(&a.fix, &b.fix).cmp(&0));
        fixes
    }
}

/// `type QueryKind int`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum QueryKind {
    /// `QueryKindWordPrefix`.
    WordPrefix,
    /// `QueryKindExactMatch`.
    ExactMatch,
    /// `QueryKindCaseInsensitiveMatch`.
    CaseInsensitiveMatch,
}

/// `type existingImport struct` (fix.go) — lives here because `View` caches
/// it.
#[derive(Clone)]
pub(crate) struct ExistingImport {
    pub(crate) node: NodeId,
    pub(crate) module_specifier: String,
    pub(crate) index: usize,
}

/// `type FixAndExport struct` — an export together with the fix that imports
/// it.
#[derive(Clone)]
pub struct FixAndExport {
    /// `Fix`.
    pub fix: Fix,
    /// `Export`.
    pub export: Rc<Export>,
}
