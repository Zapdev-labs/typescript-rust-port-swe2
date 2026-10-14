// Ported from tsc/internal/ls/autoimport/import_adder.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(arena): `*ast.SourceFile`/`*ast.Node` → `NodeId` plus the owning
// arena `Rc<ArenaCell>` recorded on the adder; `*ast.Symbol` →
// `SymbolId`. `map[*ast.ImportClauseOrBindingPattern]*addToExistingState` →
// `FxHashMap<NodeId, AddToExistingState>`.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{ArenaCell, Kind, NodeId, SymbolId, self as ast};
use tsc_checker::checker_core::Checker;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_lsconv::converters::Converters;
use tsc_lsproto as lsproto;
use tsc_lsutil::{self as lsutil, FormatCodeSettings, UserPreferences};
use tsc_nodebuilder as nodebuilder;

use crate::autoimport::export::symbol_to_export;
use crate::autoimport::fix::{
    Fix, NewImportBinding, add_import_type, add_namespace_qualifier, add_to_existing_import,
    get_add_to_existing_import_fix, get_new_imports, get_new_requires, insert_imports,
};
use crate::autoimport::view::View;
use crate::change;

/// `type ImportAdder interface`.
pub trait ImportAdder {
    /// `HasFixes`.
    fn has_fixes(&self) -> bool;
    /// `AddImportFromExportedSymbol`.
    fn add_import_from_exported_symbol(
        &mut self,
        exported_symbol: SymbolId,
        is_valid_type_only_use_site: bool,
    );
    /// `AddImportFix`.
    fn add_import_fix(&mut self, fix: Fix);
    /// `Edits`.
    fn edits(&mut self) -> Vec<lsproto::TextEdit>;
}

/// `addToExistingState` tracks modifications to an existing import clause or
/// binding pattern.
struct AddToExistingState {
    /// `importClauseOrBindingPattern`.
    #[allow(dead_code)]
    import_clause_or_binding_pattern: NodeId,
    default_import: Option<NewImportBinding>,
    named_imports: FxHashMap<String, NewImportBinding>,
}

/// `importsCollection` tracks new imports to be created for a given module
/// specifier.
#[derive(Default)]
struct ImportsCollection {
    default_import: Option<NewImportBinding>,
    named_imports: Option<FxHashMap<String, NewImportBinding>>,
    namespace_like_import: Option<NewImportBinding>,
    use_require: bool,
}

/// `newImportsKey`.
fn new_imports_key(module_specifier: &str, top_level_type_only: bool) -> String {
    if top_level_type_only {
        format!("1|{module_specifier}")
    } else {
        format!("0|{module_specifier}")
    }
}

/// `type importAdder struct`.
pub struct ImportAdderImpl<'a, 'v> {
    // Context
    /// `ctx`.
    ctx: Context,
    /// `checker`.
    checker: Rc<RefCell<Checker>>,
    /// `view`.
    view: &'a View<'v>,
    /// `formatOptions`.
    format_options: FormatCodeSettings,
    /// `converters`.
    converters: &'a Converters<'a>,
    /// `preferences`.
    preferences: &'a UserPreferences,
    /// `file` — `view.importingFile`'s arena handle for tracker operations.
    nodes: Rc<ArenaCell>,
    /// `file` — the importing source file.
    file: NodeId,

    // State
    /// `addToNamespace` — namespace fixes don't conflict, so just build a list.
    add_to_namespace: Vec<Fix>,
    /// `importType` — JSDoc type import fixes.
    import_type: Vec<Fix>,
    /// `addToExisting` — importClauseOrBindingPattern -> default or named bindings.
    add_to_existing: FxHashMap<NodeId, AddToExistingState>,
    /// `newImports` — module specifier + type only -> imports.
    new_imports: FxHashMap<String, ImportsCollection>,
    // !!! removeExisting, verbatimImports?
}

/// `NewImportAdder`.
pub fn new_import_adder<'a, 'v>(
    ctx: Context,
    program: &Rc<Program>,
    checker: &Rc<RefCell<Checker>>,
    file: NodeId,
    view: &'a View<'v>,
    format_options: FormatCodeSettings,
    converters: &'a Converters<'a>,
    preferences: &'a UserPreferences,
) -> ImportAdderImpl<'a, 'v> {
    ImportAdderImpl {
        ctx,
        checker: checker.clone(),
        view,
        format_options,
        converters,
        preferences,
        nodes: program.nodes_handle(file.file_index()),
        file,
        add_to_namespace: Vec::new(),
        import_type: Vec::new(),
        add_to_existing: FxHashMap::default(),
        new_imports: FxHashMap::default(),
    }
}

impl<'a, 'v> ImportAdderImpl<'a, 'v> {
    /// `importAdder.getAllExportsForSymbol`.
    fn get_all_exports_for_symbol(
        &self,
        symbol: SymbolId,
    ) -> Vec<Rc<crate::autoimport::export::Export>> {
        match symbol_to_export(symbol, &self.checker) {
            Some(export) => self.view.search_by_export_id(&export.export_id),
            None => Vec::new(),
        }
    }

    /// `importAdder.getNewImportEntry`.
    fn get_new_import_entry(
        &mut self,
        module_specifier: &str,
        import_kind: lsproto::ImportKind,
        use_require: bool,
        add_as_type_only: lsproto::AddAsTypeOnly,
    ) -> &mut ImportsCollection {
        // A default import that requires type-only makes the whole import
        // type-only. (We could add `default` as a named import, but that style
        // seems undesirable.) Under `--preserveValueImports` and
        // `--importsNotUsedAsValues=error`, if a module default-exports a type
        // but named-exports some values (weird), you would have to use a
        // type-only default import and non-type-only named imports. These
        // require two separate import declarations, so we build this into the
        // map key.
        let type_only_key = new_imports_key(module_specifier, true /*topLevelTypeOnly*/);
        let non_type_only_key = new_imports_key(module_specifier, false /*topLevelTypeOnly*/);

        if import_kind == lsproto::ImportKind::Default
            && add_as_type_only == lsproto::AddAsTypeOnly::Required
        {
            if self.new_imports.contains_key(&type_only_key) {
                return self.new_imports.get_mut(&type_only_key).unwrap();
            }
            self.new_imports.insert(
                type_only_key.clone(),
                ImportsCollection {
                    use_require,
                    ..Default::default()
                },
            );
            return self.new_imports.get_mut(&type_only_key).unwrap();
        }

        if add_as_type_only == lsproto::AddAsTypeOnly::Allowed
            && (self.new_imports.contains_key(&type_only_key)
                || self.new_imports.contains_key(&non_type_only_key))
        {
            if self.new_imports.contains_key(&type_only_key) {
                return self.new_imports.get_mut(&type_only_key).unwrap();
            }
            return self.new_imports.get_mut(&non_type_only_key).unwrap();
        }

        if !self.new_imports.contains_key(&non_type_only_key) {
            self.new_imports.insert(
                non_type_only_key.clone(),
                ImportsCollection {
                    use_require,
                    ..Default::default()
                },
            );
        }
        self.new_imports.get_mut(&non_type_only_key).unwrap()
    }

    /// `importAdder.getImportFixForSymbol`.
    fn get_import_fix_for_symbol(
        &self,
        view: &View,
        exports: &[Rc<crate::autoimport::export::Export>],
        is_valid_type_only_use_site: bool,
    ) -> Option<Fix> {
        let mut fixes: Vec<Fix> = exports
            .iter()
            .flat_map(|export| {
                view.get_fixes(
                    export,
                    false, /*forJSX*/
                    is_valid_type_only_use_site,
                    None, /*usagePosition*/
                )
            })
            .collect();
        fixes.sort_by(|a, b| view.compare_fixes_for_ranking(a, b).cmp(&0));
        fixes.into_iter().next()
    }
}

impl ImportAdder for ImportAdderImpl<'_, '_> {
    /// `importAdder.HasFixes`.
    fn has_fixes(&self) -> bool {
        !self.add_to_namespace.is_empty()
            || !self.import_type.is_empty()
            || !self.add_to_existing.is_empty()
            || !self.new_imports.is_empty()
    }

    /// `importAdder.AddImportFromExportedSymbol`.
    // !!! referenceImport
    fn add_import_from_exported_symbol(
        &mut self,
        exported_symbol: SymbolId,
        is_valid_type_only_use_site: bool,
    ) {
        let symbol = {
            let mut c = self.checker.borrow_mut();
            match c.skip_alias(exported_symbol) {
                Some(skipped) => c.get_merged_symbol(skipped),
                None => exported_symbol,
            }
        };
        let export_infos = self.get_all_exports_for_symbol(symbol);
        if export_infos.is_empty() {
            // If no exportInfo is found, this means export could not be resolved
            // when we have filtered for autoImportFileExcludePatterns, so we
            // should not generate an import.
            return;
        }
        let fix =
            self.get_import_fix_for_symbol(self.view, &export_infos, is_valid_type_only_use_site);
        if let Some(fix) = fix {
            // !!! referenceImport -> propertyName
            self.add_import_fix(fix);
        }
    }

    /// `importAdder.Edits`.
    // !!! organize imports?
    fn edits(&mut self) -> Vec<lsproto::TextEdit> {
        let mut tracker = change::new_tracker(
            self.ctx.clone(),
            &self.view.program.options(),
            self.format_options.clone(),
            self.converters,
        );
        let quote_preference = {
            let nodes = self.nodes.snapshot();
            lsutil::get_quote_preference(&nodes, self.file, self.preferences)
        };
        for fix in &self.add_to_namespace {
            add_namespace_qualifier(
                fix,
                &mut tracker,
                &self.nodes,
                self.file,
                &tsc_locale::from_context(&self.ctx),
            );
        }
        for fix in &self.import_type {
            add_import_type(
                fix,
                &self.nodes,
                self.file,
                self.preferences,
                &mut tracker,
                &tsc_locale::from_context(&self.ctx),
            );
        }
        for (clause_or_pattern, entry) in &self.add_to_existing {
            let named_imports: Vec<&NewImportBinding> = sorted_named_imports(&entry.named_imports);
            add_to_existing_import(
                &mut tracker,
                &self.nodes,
                self.file,
                *clause_or_pattern,
                entry.default_import.as_ref(),
                named_imports,
                self.preferences,
            );
        }

        let mut new_declarations: Vec<NodeId> = Vec::new();
        for (key, new_import) in &self.new_imports {
            let module_specifier = &key[2..]; // From `${0 | 1}|${moduleSpecifier}` format
            let declarations = if new_import.use_require {
                get_new_requires(
                    &mut tracker,
                    &self.nodes,
                    self.file,
                    module_specifier,
                    quote_preference.clone(),
                    new_import.default_import.as_ref(),
                    &sorted_named_imports_owned(&new_import.named_imports),
                    new_import.namespace_like_import.as_ref(),
                    &self.view.program.options(),
                )
            } else {
                get_new_imports(
                    &mut tracker,
                    &self.nodes,
                    self.file,
                    module_specifier,
                    quote_preference.clone(),
                    new_import.default_import.as_ref(),
                    &sorted_named_imports_owned(&new_import.named_imports),
                    new_import.namespace_like_import.as_ref(),
                    &self.view.program.options(),
                    self.preferences,
                )
            };
            new_declarations.extend(declarations);
        }

        if !new_declarations.is_empty() {
            insert_imports(
                &mut tracker,
                &self.nodes,
                self.file,
                new_declarations,
                true, /*blankLineBetween*/
                self.preferences,
            );
        }

        // Unmappable files are dropped by `get_changes`, so a content-mapped
        // importing file that cannot be faithfully rewritten yields no edits
        // rather than a corrupting one.
        let (mut changes, _) = tracker.get_changes();
        let file_name = {
            let nodes = self.nodes.snapshot();
            nodes[self.file]
                .as_source_file()
                .original_file_name(&nodes)
                .clone()
        };
        changes.remove(&file_name).unwrap_or_default()
    }

    /// `importAdder.AddImportFix` adds a fix to the import adder,
    /// accumulating it with other fixes so that multiple imports from the
    /// same module are coalesced into a single import statement.
    fn add_import_fix(&mut self, fix: Fix) {
        let symbol_name = fix.auto_import_fix.name.clone();
        let compiler_options = self.view.program.options();

        match fix.auto_import_fix.kind {
            k if k == lsproto::AutoImportFixKind::UseNamespace => self.add_to_namespace.push(fix),
            k if k == lsproto::AutoImportFixKind::JsdocTypeImport => self.import_type.push(fix),
            k if k == lsproto::AutoImportFixKind::AddToExisting => {
                let existing_fix = get_add_to_existing_import_fix(&self.nodes, self.file, &fix);
                let entry = self
                    .add_to_existing
                    .entry(existing_fix.import_clause_or_binding_pattern)
                    .or_insert_with(|| AddToExistingState {
                        import_clause_or_binding_pattern: existing_fix
                            .import_clause_or_binding_pattern,
                        default_import: None,
                        named_imports: FxHashMap::default(),
                    });

                if fix.auto_import_fix.import_kind == lsproto::ImportKind::Named {
                    let prev_type_only = entry
                        .named_imports
                        .get(&symbol_name)
                        .map(|i| i.add_as_type_only);
                    entry.named_imports.insert(
                        symbol_name.clone(),
                        NewImportBinding {
                            kind: lsproto::ImportKind::Named,
                            name: symbol_name.clone(),
                            add_as_type_only: reduce_add_as_type_only_values(
                                prev_type_only,
                                fix.auto_import_fix.add_as_type_only,
                            ),
                            property_name: existing_fix
                                .named_import
                                .map(|ni| ni.property_name)
                                .unwrap_or_default(),
                        },
                    );
                } else {
                    // Default import
                    debug_assert!(
                        entry.default_import.is_none()
                            || entry.default_import.as_ref().unwrap().name == symbol_name,
                        "(Add to Existing) Default import should be missing or match symbolName"
                    );
                    let prev_type_only = entry.default_import.as_ref().map(|i| i.add_as_type_only);
                    entry.default_import = Some(NewImportBinding {
                        kind: lsproto::ImportKind::Default,
                        name: symbol_name,
                        property_name: String::new(),
                        add_as_type_only: reduce_add_as_type_only_values(
                            prev_type_only,
                            fix.auto_import_fix.add_as_type_only,
                        ),
                    });
                }
            }
            k if k == lsproto::AutoImportFixKind::AddNew => {
                let use_require = fix.auto_import_fix.use_require;
                let entry = self.get_new_import_entry(
                    &fix.auto_import_fix.module_specifier,
                    fix.auto_import_fix.import_kind,
                    use_require,
                    fix.auto_import_fix.add_as_type_only,
                );
                debug_assert!(
                    entry.use_require == use_require,
                    "(Add new) Tried to add an `import` and a `require` for the same module"
                );

                match fix.auto_import_fix.import_kind {
                    i if i == lsproto::ImportKind::Default => {
                        debug_assert!(
                            entry.default_import.is_none()
                                || entry.default_import.as_ref().unwrap().name == symbol_name,
                            "(Add new) Default import should be missing or match symbolName"
                        );
                        let prev_type_only =
                            entry.default_import.as_ref().map(|i| i.add_as_type_only);
                        entry.default_import = Some(NewImportBinding {
                            kind: lsproto::ImportKind::Default,
                            name: symbol_name,
                            property_name: String::new(),
                            add_as_type_only: reduce_add_as_type_only_values(
                                prev_type_only,
                                fix.auto_import_fix.add_as_type_only,
                            ),
                        });
                    }
                    i if i == lsproto::ImportKind::Named => {
                        let named_imports =
                            entry.named_imports.get_or_insert_with(FxHashMap::default);
                        let prev_type_only =
                            named_imports.get(&symbol_name).map(|i| i.add_as_type_only);
                        named_imports.insert(
                            symbol_name.clone(),
                            NewImportBinding {
                                kind: lsproto::ImportKind::Named,
                                name: symbol_name,
                                property_name: String::new(),
                                add_as_type_only: reduce_add_as_type_only_values(
                                    prev_type_only,
                                    fix.auto_import_fix.add_as_type_only,
                                ),
                                // !!! propertyName
                            },
                        );
                    }
                    i if i == lsproto::ImportKind::CommonJS => {
                        if compiler_options.verbatim_module_syntax.is_true() {
                            let named_imports =
                                entry.named_imports.get_or_insert_with(FxHashMap::default);
                            let prev_type_only =
                                named_imports.get(&symbol_name).map(|i| i.add_as_type_only);
                            named_imports.insert(
                                symbol_name.clone(),
                                NewImportBinding {
                                    kind: lsproto::ImportKind::CommonJS,
                                    name: symbol_name,
                                    property_name: String::new(),
                                    add_as_type_only: reduce_add_as_type_only_values(
                                        prev_type_only,
                                        fix.auto_import_fix.add_as_type_only,
                                    ),
                                    // !!! propertyName
                                },
                            );
                        } else {
                            debug_assert!(
                                entry.namespace_like_import.is_none()
                                    || entry.namespace_like_import.as_ref().unwrap().name
                                        == symbol_name,
                                "Namespacelike import should be missing or match symbolName"
                            );
                            entry.namespace_like_import = Some(NewImportBinding {
                                kind: lsproto::ImportKind::CommonJS,
                                name: symbol_name,
                                property_name: String::new(),
                                add_as_type_only: fix.auto_import_fix.add_as_type_only,
                            });
                        }
                    }
                    i if i == lsproto::ImportKind::Namespace => {
                        debug_assert!(
                            entry.namespace_like_import.is_none()
                                || entry.namespace_like_import.as_ref().unwrap().name
                                    == symbol_name,
                            "Namespacelike import should be missing or match symbolName"
                        );
                        entry.namespace_like_import = Some(NewImportBinding {
                            kind: lsproto::ImportKind::Namespace,
                            name: symbol_name,
                            property_name: String::new(),
                            add_as_type_only: fix.auto_import_fix.add_as_type_only,
                        });
                    }
                    _ => {}
                }
            }
            k if k == lsproto::AutoImportFixKind::PromoteTypeOnly => {
                // Excluding from fix-all
            }
            k => panic!("Unexpected fix kind: {k}"),
        }
    }
}

/// `sortedNamedImports`.
fn sorted_named_imports<'x>(
    m: &'x FxHashMap<String, NewImportBinding>,
) -> Vec<&'x NewImportBinding> {
    let mut keys: Vec<&String> = m.keys().collect();
    keys.sort();
    keys.into_iter().map(|k| &m[k]).collect()
}

fn sorted_named_imports_owned(
    m: &Option<FxHashMap<String, NewImportBinding>>,
) -> Vec<NewImportBinding> {
    match m {
        Some(m) => sorted_named_imports(m).into_iter().cloned().collect(),
        None => Vec::new(),
    }
}

// `NotAllowed` overrides `Required` because one addition of a new import might
// be required to be type-only because of `--importsNotUsedAsValues=error`, but
// if a second addition of the same import is `NotAllowed` to be type-only, the
// reason the first one was `Required` - the unused runtime dependency - is now
// moot. Alternatively, if one addition is `Required` because it has no value
// meaning under `--preserveValueImports` and `--isolatedModules`, it should be
// impossible for another addition to be `NotAllowed` since that would mean a
// type is being referenced in a value location.
fn reduce_add_as_type_only_values(
    prev_value: Option<lsproto::AddAsTypeOnly>,
    new_value: lsproto::AddAsTypeOnly,
) -> lsproto::AddAsTypeOnly {
    match prev_value {
        Some(prev) if new_value > prev => new_value,
        Some(prev) => prev,
        None => new_value,
    }
}

/// `TypeToAutoImportableTypeNode`.
pub fn type_to_auto_importable_type_node(
    c: &Rc<RefCell<Checker>>,
    import_adder: Option<&mut dyn ImportAdder>,
    t: tsc_checker::types::TypeId,
    context_node: NodeId, // !!! flags
) -> Option<NodeId> {
    let (type_node, id_to_symbol) = {
        c.borrow_mut().type_to_type_node_with_id_map(
            t,
            Some(context_node),
            nodebuilder::Flags::NONE,
        )
    };
    let type_node = type_node?;
    type_node_to_auto_importable_type_node(c, type_node, import_adder, id_to_symbol)
}

/// `TypeNodeToAutoImportableTypeNode` converts import type references in a
/// type node to simple type references and registers needed imports with the
/// import adder.
pub fn type_node_to_auto_importable_type_node(
    c: &Rc<RefCell<Checker>>,
    type_node: NodeId,
    import_adder: Option<&mut dyn ImportAdder>,
    id_to_symbol: FxHashMap<NodeId, SymbolId>,
) -> Option<NodeId> {
    let (reference_type_node, importable_symbols) =
        try_get_auto_importable_reference_from_type_node(c, type_node, &id_to_symbol);
    let mut type_node = type_node;
    if let Some(reference) = reference_type_node {
        if let Some(import_adder) = import_adder {
            import_symbols(import_adder, importable_symbols);
        }
        type_node = reference;
    }

    // !!! handle type node reuse: nodes needs to be fresh here but also
    // preserve symbols
    Some(type_node)
}

/// `importSymbols`.
fn import_symbols(import_adder: &mut dyn ImportAdder, symbols: Vec<SymbolId>) {
    for symbol in symbols {
        import_adder.add_import_from_exported_symbol(symbol, true /*isValidTypeOnlyUseSite*/);
    }
}

/// `TryGetAutoImportableReferenceFromTypeNode` — given a type node containing
/// `import("./a").SomeType<import("./b").OtherType<...>>`, returns an
/// equivalent type reference node with any nested ImportTypeNodes also
/// replaced with type references, and a list of symbols that must be imported
/// to use the type reference.
pub fn try_get_auto_importable_reference_from_type_node(
    c: &Rc<RefCell<Checker>>,
    import_type_node: NodeId,
    id_to_symbol: &FxHashMap<NodeId, SymbolId>,
) -> (Option<NodeId>, Vec<SymbolId>) {
    let file_index = import_type_node.file_index();
    let nodes_handle = {
        let c_borrowed = c.borrow();
        let program = c_borrowed.program.clone().expect("program");
        program.nodes_handle(file_index)
    };
    let mut nodes = nodes_handle.cow();
    let mut factory = ast::NodeFactory::new(ast::NodeFactoryHooks::default());
    let mut cx = ast::visitor::VisitorCx::new(&mut *nodes, &mut factory);
    let symbols: Rc<RefCell<Vec<SymbolId>>> = Rc::new(RefCell::new(Vec::new()));
    let symbols_out = symbols.clone();
    let id_to_symbol_ref = id_to_symbol;
    let checker_ref = c.clone();

    let visitor = ast::visitor::NodeVisitor::new(
        Box::new(
            move |v, cx: &mut ast::visitor::VisitorCx<'_, '_>, node: NodeId| {
                if ast::is_literal_import_type_node(&cx.nodes[node], cx.nodes)
                    && cx.nodes[node].as_import_type_node().qualifier.is_some()
                {
                    // Symbol for the left-most thing after the dot
                    let qualifier = cx.nodes[node].as_import_type_node().qualifier.unwrap();
                    let first_identifier = ast::get_first_identifier(qualifier, cx.nodes);
                    let Some(&symbol) = id_to_symbol_ref.get(&first_identifier) else {
                        // if symbol is missing then this doesn't come from a
                        // synthesized import type node — it has to be an import
                        // type node authored by the user and thus it has to be
                        // valid; it can't refer to reserved internal symbol names
                        // and such
                        return v.visit_each_child(cx, node).or(Some(node));
                    };
                    let name = get_name_for_exported_symbol(
                        &checker_ref,
                        symbol,
                        false, /*preferCapitalized*/
                    );
                    let new_qualifier = if name != cx.nodes[first_identifier].text(cx.nodes) {
                        let new_identifier = cx.factory.new_identifier(cx.nodes, &name);
                        replace_first_identifier_of_entity_name(cx, qualifier, new_identifier)
                    } else {
                        qualifier
                    };
                    symbols.borrow_mut().push(symbol);
                    let type_arguments = cx.nodes[node]
                        .as_import_type_node()
                        .node_with_type_arguments_base
                        .type_arguments
                        .clone();
                    let type_arguments = v.visit_nodes(cx, type_arguments);
                    return Some(cx.factory.new_type_reference_node(
                        cx.nodes,
                        Some(new_qualifier),
                        type_arguments,
                    ));
                }
                v.visit_each_child(cx, node).or(Some(node))
            },
        ),
        ast::visitor::NodeVisitorHooks::default(),
    );

    let type_node = visitor.visit_node(&mut cx, Some(import_type_node));
    debug_assert!(
        type_node.is_none_or(|t| ast::is_type_node(&cx.nodes[t])),
        "expected a type node"
    );
    drop(visitor);
    let symbols_result = std::mem::take(&mut *symbols_out.borrow_mut());
    (type_node, symbols_result)
}

/// `getNameForExportedSymbol` — if a type checker and multiple files are
/// available, consider using `forEachNameOfDefaultExport` instead, which
/// searches for names of re-exported defaults/namespaces in target files.
fn get_name_for_exported_symbol(
    ch: &Rc<RefCell<Checker>>,
    symbol: SymbolId,
    prefer_capitalized: bool,
) -> String {
    // Copy the fields used below so no symbol-arena borrow is held while the
    // helpers re-borrow it.
    let sym_shim = {
        let c = ch.borrow();
        let sa = c.symbol_arena.clone();
        let sym = &sa[symbol.index()];
        ast::symbol::Symbol {
            name: sym.name.clone(),
            declarations: sym.declarations.clone(),
            parent: sym.parent,
            ..Default::default()
        }
    };
    if sym_shim.name.as_ref() == ast::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
        || sym_shim.name.as_ref() == ast::INTERNAL_SYMBOL_NAME_DEFAULT
    {
        // Names for default exports:
        // - export default foo => foo
        // - export { foo as default } => foo
        // - export default 0 => filename converted to camelCase
        let name =
            crate::autoimport::util::get_default_like_export_name_from_declaration(&sym_shim, ch);
        if !name.is_empty() {
            return name;
        }
        let parent = sym_shim
            .parent
            .expect("Expected exported symbol to have module symbol as parent");
        let parent_shim = {
            let c = ch.borrow();
            let sa = c.symbol_arena.clone();
            let p = &sa[parent.index()];
            ast::symbol::Symbol {
                name: p.name.clone(),
                declarations: p.declarations.clone(),
                value_declaration: p.value_declaration,
                ..Default::default()
            }
        };
        return lsutil::module_symbol_to_valid_identifier(&parent_shim, prefer_capitalized);
    }
    sym_shim.name.to_string()
}

/// `replaceFirstIdentifierOfEntityName`.
fn replace_first_identifier_of_entity_name(
    cx: &mut ast::visitor::VisitorCx<'_, '_>,
    name: NodeId,
    new_identifier: NodeId,
) -> NodeId {
    if cx.nodes[name].kind == Kind::Identifier {
        return new_identifier;
    }
    let left = cx.nodes[name]
        .as_qualified_name()
        .left
        .expect("qualified name left");
    let right = cx.nodes[name].as_qualified_name().right;
    let new_left = replace_first_identifier_of_entity_name(cx, left, new_identifier);
    cx.factory
        .new_qualified_name(cx.nodes, Some(new_left), right)
}
