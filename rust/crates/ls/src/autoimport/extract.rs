// Ported from tsc/internal/ls/autoimport/extract.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(atomics): `extractorStats` uses `Cell` — extraction is sequential in
// this port (see `CheckerPool` in util.rs).
//
// PORT(arena): `*ast.SourceFile`/declaration parameters become `NodeId`; all
// node inspection goes through per-file arenas reached with
// `checker.program_nodes`/`program_nodes_handle` since declarations of one
// symbol can span multiple files. Borrow discipline: never hold a
// `Ref`/`RefMut` of the checker `RefCell` across a call that re-borrows it —
// collect `NodeId`s/`SymbolId`s first, drop borrows, then recurse.
//
// Go's `exportExtractor` embeds `*symbolExtractor` and adds `moduleResolver`;
// here `SymbolExtractor` carries `module_resolver: Option<Rc<DefaultResolver>>`
// and the module-extraction entry points expect it to be `Some`.

use std::cell::{Cell, RefCell, RefMut};
use std::rc::Rc;

use tsc_ast::Kind;
use tsc_ast::ast::Node;
use tsc_ast::checkflags::CheckFlags;
use tsc_ast::symbol::{Symbol, SymbolTable};
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::{NodeId, SymbolId};
use tsc_binder::nameresolver::NameResolver;
use tsc_checker::checker_core::Checker;
use tsc_core::compileroptions::RESOLUTION_MODE_COMMON_JS;
use tsc_module::resolver::DefaultResolver;
use tsc_tspath::{CaseSensitivity, PathKey, RootedFilePath, RootedPath};

use crate::autoimport::export::{
    Export, ExportID, ExportSyntax, ModuleID, ambient_module_id, file_module_id,
};
use crate::autoimport::util::{
    RealpathFn, get_default_like_export_name_from_declaration, get_non_augmentation_declaration,
    get_source_file_of_node, try_get_module_id_and_file_name_of_module_symbol,
};

/// `type extractorStats struct`.
#[derive(Default)]
pub(crate) struct ExtractorStats {
    exports: Cell<i32>,
    used_checker: Cell<i32>,
}

impl ExtractorStats {
    pub(crate) fn exports(&self) -> i32 {
        self.exports.get()
    }
    pub(crate) fn used_checker(&self) -> i32 {
        self.used_checker.get()
    }
    /// `stats.exports.Add(...)` / `stats.usedChecker.Add(...)` combined.
    pub(crate) fn add_from(&self, other: &ExtractorStats) {
        self.exports.set(self.exports.get() + other.exports());
        self.used_checker
            .set(self.used_checker.get() + other.used_checker());
    }
    /// `Add` with raw counts (installExtractions' `stats.exports.Add(int32(..))`).
    pub(crate) fn add_from_counts(&self, exports: i32, used_checker: i32) {
        self.exports.set(self.exports.get() + exports);
        self.used_checker
            .set(self.used_checker.get() + used_checker);
    }
    fn increment_exports(&self) {
        self.exports.set(self.exports.get() + 1);
    }
    fn increment_used_checker(&self) {
        self.used_checker.set(self.used_checker.get() + 1);
    }
}

/// `type checkerLease struct` — tracks whether the checker has been used
/// (checker-dependent export extraction adds work).
pub(crate) struct CheckerLease {
    used: Cell<bool>,
    checker: Rc<RefCell<Checker>>,
}

impl CheckerLease {
    pub(crate) fn new(checker: Rc<RefCell<Checker>>) -> Self {
        Self {
            used: Cell::new(false),
            checker,
        }
    }
    /// `GetChecker` — marks the lease used.
    pub(crate) fn get_checker(&self) -> Rc<RefCell<Checker>> {
        self.used.set(true);
        self.checker.clone()
    }
    /// `TryChecker` — `Some` only if the checker was already used.
    pub(crate) fn try_checker(&self) -> Option<Rc<RefCell<Checker>>> {
        if self.used.get() {
            Some(self.checker.clone())
        } else {
            None
        }
    }
    /// Mutable borrow of the checker iff `TryChecker` would succeed.
    pub(crate) fn try_borrow(&self) -> Option<RefMut<'_, Checker>> {
        if self.used.get() {
            Some(self.checker.borrow_mut())
        } else {
            None
        }
    }
}

/// `type symbolExtractor struct` / `type exportExtractor struct`.
pub(crate) struct SymbolExtractor {
    pub(crate) package_name: String,
    pub(crate) stats: Rc<ExtractorStats>,
    pub(crate) checker: Rc<RefCell<Checker>>,
    pub(crate) case_sensitivity: CaseSensitivity,
    /// `realpath`, if set, is used to resolve symlinks for ModuleID generation.
    /// This ensures that symlinked packages use their realpath as ModuleID,
    /// deduplicating exports from files that appear via multiple symlink paths.
    pub(crate) realpath: Option<RealpathFn>,
    /// `exportExtractor.moduleResolver` — `None` for the base extractor.
    pub(crate) module_resolver: Option<Rc<DefaultResolver>>,
}

impl SymbolExtractor {
    /// `newSymbolExtractor`.
    pub(crate) fn new(
        package_name: String,
        checker: Rc<RefCell<Checker>>,
        case_sensitivity: CaseSensitivity,
        realpath: Option<RealpathFn>,
    ) -> Self {
        Self {
            package_name,
            stats: Rc::new(ExtractorStats::default()),
            checker,
            case_sensitivity,
            realpath,
            module_resolver: None,
        }
    }

    /// `registryBuilder.newExportExtractor`.
    pub(crate) fn new_export(
        package_name: String,
        checker: Rc<RefCell<Checker>>,
        case_sensitivity: CaseSensitivity,
        module_resolver: Rc<DefaultResolver>,
        realpath: Option<RealpathFn>,
    ) -> Self {
        Self {
            package_name,
            stats: Rc::new(ExtractorStats::default()),
            checker,
            case_sensitivity,
            realpath,
            module_resolver: Some(module_resolver),
        }
    }

    /// `exportExtractor.Stats`.
    pub(crate) fn stats(&self) -> &Rc<ExtractorStats> {
        &self.stats
    }

    /// `getModuleID` returns the ModuleID for a file, using realpath if available.
    fn get_module_id(&self, file_name: &RootedFilePath, path_key: &PathKey) -> ModuleID {
        if let Some(realpath) = &self.realpath {
            let realpath = realpath(file_name);
            return file_module_id(
                self.case_sensitivity
                    .path_key(&RootedPath::from(realpath.as_string().to_string())),
            );
        }
        file_module_id(path_key.clone())
    }

    /// `getModuleIDForSymbol` returns the ModuleID for a module symbol, using
    /// realpath normalization when available for source files.
    fn get_module_id_for_symbol(&self, symbol: SymbolId) -> Option<ModuleID> {
        let (module_id, file_name) =
            try_get_module_id_and_file_name_of_module_symbol(symbol, &self.checker)?;
        // If fileName is set, this is a source file that may need realpath
        // normalization.
        if !file_name.as_string().is_empty() && self.realpath.is_some() {
            let decl = {
                let c = self.checker.borrow();
                let sa = c.symbol_arena.borrow();
                get_non_augmentation_declaration(&sa[symbol.index()], &c)
            };
            if let Some(decl) = decl {
                let c = self.checker.borrow();
                let nodes = c.program_nodes(decl);
                if nodes[decl].kind == Kind::SourceFile {
                    let sf = nodes[decl].as_source_file();
                    return Some(self.get_module_id(sf.file_name(), sf.path_key()));
                }
            }
        }
        Some(module_id)
    }

    /// `exportExtractor.extractFromFile`.
    pub(crate) fn extract_from_file(&self, file: NodeId) -> Vec<Rc<Export>> {
        let (has_symbol, has_ambient, statements) = {
            let c = self.checker.borrow();
            let nodes = c.program_nodes(file);
            let sf = nodes[file].as_source_file();
            (
                nodes[file].symbol().is_some(),
                !sf.ambient_module_names.is_empty(),
                sf.statements
                    .as_ref()
                    .map(|l| l.nodes.clone())
                    .unwrap_or_default(),
            )
        };
        if has_symbol {
            return self.extract_from_module(file);
        }
        if has_ambient {
            let mut export_count = 0;
            let mut ambient_decls = Vec::new();
            {
                let c = self.checker.borrow();
                let nodes = c.program_nodes(file);
                for &statement in &statements {
                    if tsc_ast::is_module_with_string_literal_name(&nodes[statement], &nodes)
                        && is_non_pattern_ambient_module_declaration(&nodes, file, statement)
                    {
                        let decl_sym = nodes[statement].symbol().unwrap();
                        export_count += c.symbol_arena.borrow()[decl_sym.index()].exports.size();
                        ambient_decls.push((statement, nodes[statement].name().unwrap()));
                    }
                }
            }
            let mut exports = Vec::with_capacity(export_count);
            for (statement, name_id) in ambient_decls {
                let name = {
                    let c = self.checker.borrow();
                    let nodes = c.program_nodes(file);
                    nodes[name_id].text(&nodes).to_string()
                };
                self.extract_from_module_declaration(
                    statement,
                    file,
                    ambient_module_id(&name),
                    RootedFilePath::default(),
                    &mut exports,
                );
            }
            return exports;
        }
        Vec::new()
    }

    /// `exportExtractor.extractFromModule`.
    fn extract_from_module(&self, file: NodeId) -> Vec<Rc<Export>> {
        let (file_name, path_key, file_symbol, module_augmentations, augmentation_export_count) = {
            let c = self.checker.borrow();
            let nodes = c.program_nodes(file);
            let sf = nodes[file].as_source_file();
            let mut augmentations: Vec<NodeId> = Vec::new();
            for &name in &sf.module_augmentations {
                let decl = nodes[name]
                    .parent
                    .expect("module augmentation has no parent");
                if tsc_ast::is_global_scope_augmentation(&nodes[decl]) {
                    continue;
                }
                augmentations.push(decl);
            }
            let mut count = 0;
            for &decl in &augmentations {
                let sym = nodes[decl]
                    .symbol()
                    .expect("module declaration has no symbol");
                count += c.symbol_arena.borrow()[sym.index()].exports.size();
            }
            (
                sf.file_name().clone(),
                sf.path_key().clone(),
                nodes[file].symbol().expect("source file has no symbol"),
                augmentations,
                count,
            )
        };
        let module_id = self.get_module_id(&file_name, &path_key);
        let file_exports: Vec<(String, SymbolId)> = {
            let c = self.checker.borrow();
            c.symbol_arena.borrow()[file_symbol.index()]
                .exports
                .entries()
                .map(|(k, v)| (k.clone(), *v))
                .collect()
        };
        let mut exports = Vec::with_capacity(file_exports.len() + augmentation_export_count);
        for (name, symbol) in file_exports {
            self.extract_from_symbol(&name, symbol, &module_id, &file_name, file, &mut exports);
        }
        for &decl in &module_augmentations {
            let name = {
                let c = self.checker.borrow();
                let nodes = c.program_nodes(file);
                let name_id = nodes[decl].name().expect("module declaration has no name");
                nodes[name_id].text(&nodes).to_string()
            };
            let mut decl_module_id = ambient_module_id(&name);
            let mut module_file_name = RootedFilePath::default();
            let mut unresolved_module_specifier = Default::default();
            if tsc_tspath::is_external_module_name_relative(&name) {
                let (resolved, _) = self
                    .module_resolver
                    .as_ref()
                    .expect("module extraction requires a module resolver")
                    .resolve_module_name(&name, &file_name, RESOLUTION_MODE_COMMON_JS, None);
                if let Some(resolved) = resolved {
                    module_file_name = resolved.resolved_file_name.clone();
                    decl_module_id = file_module_id(
                        self.case_sensitivity
                            .path_key(&RootedPath::from(module_file_name.as_string().to_string())),
                    );
                } else {
                    module_file_name = file_name.directory().resolve_file(&name);
                    decl_module_id =
                        file_module_id(self.case_sensitivity.path_key(&module_file_name.as_path()));
                    unresolved_module_specifier = tsc_tspath::to_module_specifier(&name);
                }
            }
            let export_start = exports.len();
            self.extract_from_module_declaration(
                decl,
                file,
                decl_module_id,
                module_file_name,
                &mut exports,
            );
            // `Rc::get_mut`: exports created during extraction are uniquely owned.
            for export in &mut exports[export_start..] {
                Rc::get_mut(export)
                    .expect("export unexpectedly shared")
                    .unresolved_module_specifier = unresolved_module_specifier.clone();
            }
        }
        exports
    }

    /// `exportExtractor.extractFromModuleDeclaration`.
    fn extract_from_module_declaration(
        &self,
        decl: NodeId,
        file: NodeId,
        module_id: ModuleID,
        module_file_name: RootedFilePath,
        exports: &mut Vec<Rc<Export>>,
    ) {
        let sym = {
            let c = self.checker.borrow();
            let nodes = c.program_nodes(decl);
            nodes[decl]
                .symbol()
                .expect("module declaration has no symbol")
        };
        let exports_of: Vec<(String, SymbolId)> = {
            let c = self.checker.borrow();
            c.symbol_arena.borrow()[sym.index()]
                .exports
                .entries()
                .map(|(k, v)| (k.clone(), *v))
                .collect()
        };
        for (name, symbol) in exports_of {
            self.extract_from_symbol(&name, symbol, &module_id, &module_file_name, file, exports);
        }
    }

    /// `symbolExtractor.extractFromSymbol`.
    pub(crate) fn extract_from_symbol(
        &self,
        name: &str,
        symbol: SymbolId,
        module_id: &ModuleID,
        module_file_name: &RootedFilePath,
        file: NodeId,
        exports: &mut Vec<Rc<Export>>,
    ) {
        {
            let c = self.checker.borrow();
            let sa = c.symbol_arena.borrow();
            if should_ignore_symbol(&sa[symbol.index()]) {
                return;
            }
        }

        if name == tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_STAR {
            let checker_lease = CheckerLease::new(self.checker.clone());
            let (parent, parent_exports) = {
                let c = self.checker.borrow();
                let sa = c.symbol_arena.borrow();
                let parent = sa[symbol.index()]
                    .parent
                    .expect("export star has no parent");
                (
                    parent,
                    sa[parent.index()]
                        .exports
                        .entries()
                        .map(|(k, v)| (k.clone(), *v))
                        .collect::<Vec<_>>(),
                )
            };
            let mut all_exports = self
                .checker
                .borrow_mut()
                .get_exports_of_module_as_array(parent);
            // allExports includes named exports from the file that will be
            // processed separately; we want to add only the ones that come
            // from the star.
            for (name, named_export) in parent_exports {
                if name != tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_STAR {
                    let idx = all_exports
                        .iter()
                        .position(|s| *s == named_export)
                        .map(|i| i as isize)
                        .unwrap_or(-1);
                    let ignore = {
                        let c = self.checker.borrow();
                        let sa = c.symbol_arena.borrow();
                        should_ignore_symbol(&sa[named_export.index()])
                    };
                    if idx >= 0 || ignore {
                        // PORT(parity): Go's slices.Delete(allExports, idx, idx+1)
                        // panics when idx == -1; Vec::remove does too.
                        all_exports.remove(idx as usize);
                    }
                }
            }

            exports.reserve(all_exports.len());
            for reexported_symbol in all_exports {
                if let Some(mut export) = self
                    .create_export(
                        reexported_symbol,
                        module_id.clone(),
                        module_file_name.clone(),
                        ExportSyntax::Star,
                        file,
                        &checker_lease,
                    )
                    .0
                {
                    let reexported_parent = {
                        let c = self.checker.borrow();
                        c.symbol_arena.borrow()[reexported_symbol.index()].parent
                    };
                    let ch = checker_lease.get_checker();
                    // `GetMergedSymbol(nil)` → `nil`; `Option::map`.
                    let parent = reexported_parent.map(|p| ch.borrow_mut().get_merged_symbol(p));
                    let reexported_name = {
                        let c = self.checker.borrow();
                        c.symbol_arena.borrow()[reexported_symbol.index()]
                            .name
                            .clone()
                    };
                    if let Some(parent) = parent {
                        let is_external = {
                            let c = self.checker.borrow();
                            c.symbol_arena.borrow()[parent.index()].is_external_module()
                        };
                        if is_external
                            && let Some(target_module_id) = self.get_module_id_for_symbol(parent)
                        {
                            export.target = ExportID {
                                export_name: reexported_name,
                                module_id: target_module_id,
                            };
                        }
                    }
                    export.through = tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_STAR.to_string();
                    exports.push(Rc::new(export));
                }
            }
            return;
        }

        let syntax = {
            let c = self.checker.borrow();
            let sa = c.symbol_arena.borrow();
            get_syntax(&sa[symbol.index()], &c)
        };
        let checker_lease = CheckerLease::new(self.checker.clone());
        let (export, target) = self.create_export(
            symbol,
            module_id.clone(),
            module_file_name.clone(),
            syntax,
            file,
            &checker_lease,
        );
        let Some(export) = export else { return };
        exports.push(Rc::new(export));

        if let Some(target) = target {
            let target_is_namespace = {
                let c = self.checker.borrow();
                c.symbol_arena.borrow()[target.index()]
                    .flags
                    .intersects(SymbolFlags::NAMESPACE)
            };
            if syntax == ExportSyntax::Equals && target_is_namespace {
                let inner: Vec<(String, SymbolId)> = {
                    let c = self.checker.borrow();
                    c.symbol_arena.borrow()[target.index()]
                        .exports
                        .entries()
                        .map(|(k, v)| (k.clone(), *v))
                        .collect()
                };
                exports.reserve(inner.len());
                for (inner_name, named_export) in inner {
                    if inner_name != tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_STAR
                        && let Some(mut export) = self
                            .create_export(
                                named_export,
                                module_id.clone(),
                                module_file_name.clone(),
                                syntax,
                                file,
                                &checker_lease,
                            )
                            .0
                    {
                        export.through = name.to_string();
                        exports.push(Rc::new(export));
                    }
                }
            }
        } else if syntax == ExportSyntax::CommonJSModuleExports {
            let decls = {
                let c = self.checker.borrow();
                c.symbol_arena.borrow()[symbol.index()].declarations.clone()
            };
            let expression = {
                let c = self.checker.borrow();
                let nodes = c.program_nodes(decls[0]);
                nodes[decls[0]]
                    .as_binary_expression()
                    .right
                    .expect("module.exports assignment has no right side")
            };
            let is_object_literal = {
                let c = self.checker.borrow();
                let nodes = c.program_nodes(expression);
                nodes[expression].kind == Kind::ObjectLiteralExpression
            };
            if is_object_literal {
                // What is actually desirable here? I think it would be
                // reasonable to only treat these as exports if *every*
                // property is a shorthand property or identifier: identifier.
                // At least, it would be sketchy if there were any methods,
                // computed properties...
                let nodes_rc = self.checker.borrow().program_nodes_handle(expression);
                let mut nodes = nodes_rc.snapshot();
                let properties = nodes[expression]
                    .as_object_literal_expression()
                    .properties
                    .as_ref()
                    .map(|p| p.nodes.to_vec())
                    .unwrap_or_default();
                exports.reserve(properties.len());
                for prop in properties {
                    let prop_name = nodes[prop].name();
                    let eligible = tsc_ast::is_shorthand_property_assignment(&nodes[prop])
                        || (tsc_ast::is_property_assignment(&nodes[prop])
                            && prop_name.is_some_and(|n| nodes[n].kind == Kind::Identifier));
                    if eligible && let Some(prop_name) = prop_name {
                        let text = nodes[prop_name].text(&nodes).to_string();
                        let member = nodes[expression].symbol().and_then(|s| {
                            self.checker.borrow().symbol_arena.borrow()[s.index()]
                                .members
                                .get(text.as_str())
                                .copied()
                        });
                        if let Some(member) = member {
                            // `create_export` may `borrow_mut` this same arena
                            // (`GetSymbolModifiers`), so the shared borrow must
                            // not be live across the call.
                            drop(nodes);
                            if let Some(mut export) = self
                                .create_export(
                                    member,
                                    module_id.clone(),
                                    module_file_name.clone(),
                                    syntax,
                                    file,
                                    &checker_lease,
                                )
                                .0
                            {
                                export.through = name.to_string();
                                exports.push(Rc::new(export));
                            }
                            nodes = nodes_rc.snapshot();
                        }
                    }
                }
            }
        }
    }

    /// `symbolExtractor.createExport` — returns `(export, target)`.
    fn create_export(
        &self,
        symbol: SymbolId,
        module_id: ModuleID,
        module_file_name: RootedFilePath,
        syntax: ExportSyntax,
        file: NodeId,
        checker_lease: &CheckerLease,
    ) -> (Option<Export>, Option<SymbolId>) {
        let (symbol_name, symbol_flags, symbol_declarations, combined_flags, is_type_only_decls) = {
            let c = self.checker.borrow();
            let sa = c.symbol_arena.borrow();
            let sym = &sa[symbol.index()];
            if should_ignore_symbol(sym) {
                return (None, None);
            }
            // `symbol.CombinedLocalAndExportSymbolFlags()`.
            let mut combined = sym.flags;
            if let Some(export_symbol) = sym.export_symbol {
                combined |= sa[export_symbol.index()].flags;
            }
            let type_only: Vec<bool> = sym
                .declarations
                .iter()
                .map(|&d| {
                    let nodes = c.program_nodes(d);
                    tsc_ast::is_part_of_type_only_import_or_export_declaration(d, &nodes)
                })
                .collect();
            (
                sym.name.clone(),
                sym.flags,
                sym.declarations.clone(),
                combined,
                type_only,
            )
        };

        let file_path_key = {
            let c = self.checker.borrow();
            let nodes = c.program_nodes(file);
            nodes[file].as_source_file().path_key().clone()
        };

        let mut export = Export {
            export_id: ExportID {
                export_name: symbol_name.clone(),
                module_id: module_id.clone(),
            },
            module_file_name: module_file_name.clone(),
            syntax,
            flags: combined_flags,
            path: file_path_key,
            package_name: self.package_name.clone(),
            ..Default::default()
        };

        if syntax == ExportSyntax::Umd {
            export.export_id.export_name =
                tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS.to_string();
            export.local_name = symbol_name.clone();
        }

        let mut target_symbol: Option<SymbolId> = None;
        if symbol_flags.intersects(SymbolFlags::ALIAS) {
            target_symbol = self.try_resolve_symbol(symbol, syntax, checker_lease);
            if let Some(target) = target_symbol {
                let (target_decls, target_check_flags, target_flags, target_name, target_parent) = {
                    let c = self.checker.borrow();
                    let sa = c.symbol_arena.borrow();
                    let t = &sa[target.index()];
                    (
                        t.declarations.clone(),
                        t.check_flags,
                        t.flags,
                        t.name.clone(),
                        t.parent,
                    )
                };
                let mut decl: Option<NodeId> = None;
                if !target_decls.is_empty() {
                    decl = Some(target_decls[0]);
                } else if target_check_flags.intersects(CheckFlags::MAPPED) {
                    let ch = checker_lease.get_checker();
                    let mapped_decl = ch.borrow_mut().get_mapped_type_symbol_of_property(target);
                    if let Some(mapped_decl) = mapped_decl {
                        let mapped_decls = {
                            let c = self.checker.borrow();
                            c.symbol_arena.borrow()[mapped_decl.index()]
                                .declarations
                                .clone()
                        };
                        if !mapped_decls.is_empty() {
                            decl = Some(mapped_decls[0]);
                        }
                    }
                }
                if decl.is_none() {
                    // !!! consider GetImmediateAliasedSymbol to go as far as we can
                    decl = symbol_declarations.first().copied();
                }
                let Some(decl) = decl else {
                    panic!("no declaration for aliased symbol");
                };

                let mut parent = target_parent;
                if let Some(mut ch) = checker_lease.try_borrow() {
                    export.flags = ch.get_symbol_flags(target);
                    export.is_type_only = ch.get_type_only_alias_declaration(symbol).is_some();
                    parent = parent.map(|p| ch.get_merged_symbol(p));
                } else {
                    export.flags = target_flags;
                    export.is_type_only = is_type_only_decls.iter().any(|&b| b);
                }
                let (kind, modifiers) = self.symbol_kind_and_modifiers(checker_lease, target, decl);
                export.script_element_kind = kind;
                export.script_element_kind_modifiers = modifiers;
                let mut target_module_id = {
                    let c = self.checker.borrow();
                    let source_file = get_source_file_of_node(Some(decl), &c)
                        .expect("declaration has no source file");
                    let nodes = c.program_nodes(source_file);
                    file_module_id(nodes[source_file].as_source_file().path_key().clone())
                };
                if let Some(parent) = parent {
                    let is_external = {
                        let c = self.checker.borrow();
                        c.symbol_arena.borrow()[parent.index()].is_external_module()
                    };
                    if is_external && let Some(id) = self.get_module_id_for_symbol(parent) {
                        target_module_id = id;
                    }
                }
                export.target = ExportID {
                    export_name: target_name,
                    module_id: target_module_id,
                };
            }
        } else {
            let decl = symbol_declarations[0];
            let (kind, modifiers) = self.symbol_kind_and_modifiers(checker_lease, symbol, decl);
            export.script_element_kind = kind;
            export.script_element_kind_modifiers = modifiers;
        }

        if symbol_name == tsc_ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT
            || symbol_name == tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
        {
            let mut named_symbol = symbol;
            if let Some(s) = self.local_symbol_for_export_default(named_symbol) {
                named_symbol = s;
            }
            export.local_name = {
                let c = self.checker.borrow();
                let sa = c.symbol_arena.borrow();
                get_default_like_export_name_from_declaration(
                    &sa[named_symbol.index()],
                    &self.checker,
                )
            };
            if is_unusable_name(&export.local_name) {
                export.local_name = export.target.export_name.clone();
            }
            if is_unusable_name(&export.local_name)
                && let Some(target) = target_symbol
            {
                named_symbol = target;
                if let Some(s) = self.local_symbol_for_export_default(target) {
                    named_symbol = s;
                }
                let c = self.checker.borrow();
                let sa = c.symbol_arena.borrow();
                export.local_name = get_default_like_export_name_from_declaration(
                    &sa[named_symbol.index()],
                    &self.checker,
                );
            }
            if is_unusable_name(&export.local_name) {
                // Last resort: derive identifier from the file name. Use
                // FileName() (original casing) rather than ModuleID/Path()
                // which is lowercased on case-insensitive file systems,
                // losing PascalCase.
                let file_name_for_name = self.file_name_for_default_export_name(
                    target_symbol,
                    &module_file_name,
                    &module_id,
                );
                export.local_name =
                    tsc_lsutil::module_specifier_to_valid_identifier(&file_name_for_name, false);
            }
        }

        if is_unusable_name(&export.name()) {
            return (None, None);
        }

        self.stats.increment_exports();
        if checker_lease.try_checker().is_some() {
            self.stats.increment_used_checker();
        }

        (Some(export), target_symbol)
    }

    /// `lsutil.GetSymbolKind`/`GetSymbolModifiers` pair behind the
    /// `checkerLease.TryChecker()` gate.
    fn symbol_kind_and_modifiers(
        &self,
        checker_lease: &CheckerLease,
        symbol: SymbolId,
        decl: NodeId,
    ) -> (
        tsc_lsutil::ScriptElementKind,
        tsc_lsutil::ScriptElementKindModifier,
    ) {
        let nodes_rc = self.checker.borrow().program_nodes_handle(decl);
        let mut nodes_ref = nodes_rc.cow();
        let symbols_rc = self.checker.borrow().symbol_arena.clone();
        let mut try_ch = checker_lease.try_borrow();
        let kind = tsc_lsutil::get_symbol_kind(
            try_ch.as_deref_mut(),
            symbol,
            decl,
            &nodes_ref,
            &symbols_rc,
        );
        let modifiers = tsc_lsutil::get_symbol_modifiers(
            try_ch.as_deref_mut(),
            Some(symbol),
            &mut nodes_ref,
            &symbols_rc,
        );
        (kind, modifiers)
    }

    /// `binder.GetLocalSymbolForExportDefault` — arena-aware (declarations can
    /// span file arenas, so each is read in its own).
    fn local_symbol_for_export_default(&self, symbol: SymbolId) -> Option<SymbolId> {
        let c = self.checker.borrow();
        let decls = c.symbol_arena.borrow()[symbol.index()].declarations.clone();
        if decls.is_empty() {
            return None;
        }
        // `isExportDefaultSymbol`.
        {
            let nodes = c.program_nodes(decls[0]);
            if !tsc_ast::has_syntactic_modifier(
                &nodes[decls[0]],
                tsc_ast::modifierflags::ModifierFlags::DEFAULT,
            ) {
                return None;
            }
        }
        for &decl in &decls {
            let nodes = c.program_nodes(decl);
            if let Some(local_symbol) = nodes[decl].local_symbol() {
                return Some(local_symbol);
            }
        }
        None
    }

    /// `fileNameForDefaultExportName`.
    fn file_name_for_default_export_name(
        &self,
        target_symbol: Option<SymbolId>,
        module_file_name: &RootedFilePath,
        module_id: &ModuleID,
    ) -> String {
        if let Some(target) = target_symbol {
            let decls = {
                let c = self.checker.borrow();
                c.symbol_arena.borrow()[target.index()].declarations.clone()
            };
            if let Some(&decl) = decls.first() {
                let c = self.checker.borrow();
                if let Some(sf) = get_source_file_of_node(Some(decl), &c) {
                    let nodes = c.program_nodes(sf);
                    let fn_name = nodes[sf].as_source_file().file_name().clone();
                    if !fn_name.as_string().is_empty() {
                        return fn_name.as_string().to_string();
                    }
                }
            }
        }
        if !module_file_name.as_string().is_empty() {
            return module_file_name.as_string().to_string();
        }
        module_id.as_string().to_string()
    }

    /// `symbolExtractor.tryResolveSymbol`.
    fn try_resolve_symbol(
        &self,
        symbol: SymbolId,
        syntax: ExportSyntax,
        checker_lease: &CheckerLease,
    ) -> Option<SymbolId> {
        {
            let c = self.checker.borrow();
            let sa = c.symbol_arena.borrow();
            if !tsc_ast::is_non_local_alias(Some(&sa[symbol.index()]), SymbolFlags::NONE) {
                return Some(symbol);
            }
        }

        let mut loc: Option<NodeId> = None;
        let mut name = String::new();
        match syntax {
            ExportSyntax::Named => {
                let decl = {
                    let c = self.checker.borrow();
                    let sa = c.symbol_arena.borrow();
                    get_declaration_of_kind_any(
                        &sa[symbol.index()].declarations,
                        Kind::ExportSpecifier,
                        &c,
                    )
                };
                if let Some(decl) = decl {
                    let c = self.checker.borrow();
                    let nodes = c.program_nodes(decl);
                    let named_exports = nodes[decl].parent.unwrap();
                    let export_decl = nodes[named_exports].parent.unwrap();
                    if nodes[export_decl]
                        .as_export_declaration()
                        .module_specifier
                        .is_none()
                    {
                        // `core.FirstNonZero(decl.Name(), decl.PropertyName())`.
                        let n = nodes[decl].name().or_else(|| nodes[decl].property_name());
                        if let Some(n) = n
                            && nodes[n].kind == Kind::Identifier
                        {
                            loc = Some(n);
                            name = nodes[n].text(&nodes).to_string();
                        }
                    }
                }
            }
            // !!! check if module.exports = foo is marked as an alias
            ExportSyntax::Equals => {
                let is_export_equals = {
                    let c = self.checker.borrow();
                    c.symbol_arena.borrow()[symbol.index()].name
                        == tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                };
                if is_export_equals {
                    self.resolve_export_assignment_loc(symbol, &mut loc, &mut name);
                }
            }
            ExportSyntax::DefaultDeclaration => {
                self.resolve_export_assignment_loc(symbol, &mut loc, &mut name);
            }
            _ => {}
        }

        if let Some(loc_id) = loc {
            let nodes_rc = self.checker.borrow().program_nodes_handle(loc_id);
            let nodes = nodes_rc.snapshot();
            let symbols_rc = self.checker.borrow().symbol_arena.clone();
            let mut resolver = NameResolver {
                host: None,
                for_suggestion: false,
                compiler_options: Rc::new(
                    tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS.clone(),
                ),
                globals: Rc::new(RefCell::new(SymbolTable::default())),
                arguments_symbol: None,
                require_symbol: None,
                get_symbol_of_declaration_hook: None,
                error_hook: None,
                lookup_hook: None,
                symbol_referenced: None,
                set_requires_scope_change_cache: None,
                get_requires_scope_change_cache: None,
                on_property_with_invalid_initializer: None,
                on_failed_to_resolve_symbol: None,
                on_successfully_resolved_symbol: None,
            };
            if let Some(local) = resolver.resolve(
                Some(loc_id),
                &name,
                SymbolFlags::ALL,
                None,
                false,
                false,
                &nodes,
                &symbols_rc,
            ) {
                let is_non_local = {
                    let sa = symbols_rc.borrow();
                    tsc_ast::is_non_local_alias(Some(&sa[local.index()]), SymbolFlags::NONE)
                };
                if !is_non_local {
                    return Some(local);
                }
            }
        }

        let checker = checker_lease.get_checker();
        let mut ch = checker.borrow_mut();
        let resolved = ch.get_aliased_symbol(symbol);
        if !ch.is_unknown_symbol(resolved) {
            return resolved;
        }
        None
    }

    /// The `ExportAssignment` lookup shared by the `ExportSyntaxEquals`
    /// (`symbol.Name == "export="`) and `ExportSyntaxDefaultDeclaration` arms
    /// of `tryResolveSymbol`'s switch.
    fn resolve_export_assignment_loc(
        &self,
        symbol: SymbolId,
        loc: &mut Option<NodeId>,
        name: &mut String,
    ) {
        let decl = {
            let c = self.checker.borrow();
            let sa = c.symbol_arena.borrow();
            get_declaration_of_kind_any(
                &sa[symbol.index()].declarations,
                Kind::ExportAssignment,
                &c,
            )
        };
        if let Some(decl) = decl {
            let c = self.checker.borrow();
            let nodes = c.program_nodes(decl);
            if let Some(expr) = nodes[decl].expression()
                && nodes[expr].kind == Kind::Identifier
            {
                *loc = Some(expr);
                *name = nodes[expr].text(&nodes).to_string();
            }
        }
    }
}

/// `ast.GetDeclarationOfKind` — declarations can span file arenas in this
/// port, so each candidate is inspected in its own arena.
fn get_declaration_of_kind_any(declarations: &[NodeId], kind: Kind, c: &Checker) -> Option<NodeId> {
    declarations
        .iter()
        .copied()
        .find(|&d| c.program_nodes(d)[d].kind == kind)
}

/// `isNonPatternAmbientModuleDeclaration`.
fn is_non_pattern_ambient_module_declaration(nodes: &[Node], file: NodeId, decl: NodeId) -> bool {
    let decl_symbol = nodes[decl].symbol();
    for module in &nodes[file].as_source_file().pattern_ambient_modules {
        if module.symbol.is_some() && module.symbol == decl_symbol {
            return false;
        }
    }
    true
}

/// `shouldIgnoreSymbol`.
fn should_ignore_symbol(symbol: &Symbol) -> bool {
    symbol.flags.intersects(SymbolFlags::PROTOTYPE)
}

/// `getSyntax`.
fn get_syntax(symbol: &Symbol, c: &Checker) -> ExportSyntax {
    for &decl in &symbol.declarations {
        let nodes = c.program_nodes(decl);
        match nodes[decl].kind {
            Kind::ExportSpecifier => return ExportSyntax::Named,
            Kind::ExportAssignment => {
                return if nodes[decl].as_export_assignment().is_export_equals {
                    ExportSyntax::Equals
                } else {
                    ExportSyntax::DefaultDeclaration
                };
            }
            Kind::NamespaceExportDeclaration => return ExportSyntax::Umd,
            Kind::BinaryExpression => {
                match tsc_ast::get_assignment_declaration_kind(decl, &nodes) {
                    tsc_ast::JsDeclarationKind::ModuleExports => {
                        return ExportSyntax::CommonJSModuleExports;
                    }
                    tsc_ast::JsDeclarationKind::ExportsProperty => {
                        return ExportSyntax::CommonJSExportsProperty;
                    }
                    _ => {}
                }
            }
            _ => {
                if tsc_ast::get_combined_modifier_flags(decl, &nodes)
                    .intersects(tsc_ast::modifierflags::ModifierFlags::DEFAULT)
                {
                    return ExportSyntax::DefaultModifier;
                } else {
                    return ExportSyntax::Modifier;
                }
            }
        }
    }
    ExportSyntax::None
}

/// `isUnusableName`.
pub(crate) fn is_unusable_name(name: &str) -> bool {
    name.is_empty()
        || name == "_default"
        || name == tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_STAR
        || name == tsc_ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT
        || name == tsc_ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
}
