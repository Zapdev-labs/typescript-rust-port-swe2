// Ported from tsc/internal/ls/organizeimports.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go mutates a shared `[]*ast.Node` graph. Here factory calls mint
// nodes in a `nodes_mut` (`ArenaMut`) guard for the file's arena — writes
// land in place and are visible to every `nodes` snapshot handle
// (checker, tracker incidental `program.nodes()` reads). The guard is
// dropped before any tracker node operation (`borrow_nodes` asserts one
// live writer per arena).
// `removeUnusedImports` is split into a checker phase and a factory
// phase: `Checker::is_declaration_used` calls `program.nodes_mut`
// internally, so no arena guard may be alive while it runs.
use std::collections::HashMap;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{Kind, Node, NodeFactory, NodeFactoryHooks, NodeId, SubtreeFacts, self as ast};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::options_generated::JsxEmit;
use tsc_core::text::TextRange;
use tsc_lsproto as lsproto;
use tsc_lsutil::organizeimports as lsutil_organize;
use tsc_lsutil::userpreferences::{OrganizeImportsSort, OrganizeImportsTypeOrder};
use tsc_lsutil::userpreferences_generated::UserPreferences;
use tsc_printer::EmitFlags;
use tsc_scanner as scanner;
use tsc_stringutil as stringutil;
use tsc_tspath::RootedFilePath;

use crate::change::tracker::{
    LeadingTriviaOption, NodeOptions, Tracker, TrailingTriviaOption, new_tracker,
    positions_are_on_same_line,
};
use crate::languageservice::LanguageService;

/// `stringutil.Comparison` (i32) → `Ordering`.
fn ordering(c: i32) -> std::cmp::Ordering {
    c.cmp(&0)
}

/// `organizeImportsComparerSettings`.
#[derive(Clone)]
struct OrganizeImportsComparerSettings {
    module_specifier_comparer: Option<Rc<lsutil_organize::StringComparer>>,
    named_import_comparer: Option<Rc<lsutil_organize::StringComparer>>,
    type_order: OrganizeImportsTypeOrder,
}

impl<'h> LanguageService<'h> {
    /// `OrganizeImports` organizes imports by:
    ///  1. Removing unused imports
    ///  2. Coalescing imports from the same module
    ///  3. Sorting imports
    pub fn organize_imports(
        &self,
        ctx: &Context,
        source_file: NodeId,
        program: &Rc<Program>,
        kind: &lsproto::CodeActionKind,
    ) -> FxHashMap<RootedFilePath, Vec<lsproto::TextEdit>> {
        let nodes = program.nodes(source_file.file_index());
        let mut change_tracker = new_tracker(
            ctx.clone(),
            &program.options(),
            self.format_options(),
            &self.converters,
        );
        let should_sort = *kind == lsproto::CodeActionKind::SOURCE_SORT_IMPORTS_TS
            || *kind == lsproto::CodeActionKind::SOURCE_ORGANIZE_IMPORTS_TS;
        let should_combine = should_sort;
        let should_remove = *kind == lsproto::CodeActionKind::SOURCE_REMOVE_UNUSED_IMPORTS_TS
            || *kind == lsproto::CodeActionKind::SOURCE_ORGANIZE_IMPORTS_TS;
        let top_level_import_decls = lsutil_organize::filter_import_declarations(
            &nodes,
            nodes[source_file]
                .as_source_file()
                .statements
                .as_ref()
                .map_or(&[][..], |s| &s.nodes[..]),
        )
        .into_owned();
        let top_level_import_group_decls =
            group_by_newline_contiguous(&nodes, source_file, &top_level_import_decls);

        let preferences = self.user_preferences();
        let (comparers_to_test, type_orders_to_test) =
            lsutil_organize::get_detection_lists(preferences);
        let default_comparer = comparers_to_test[0].clone();
        let sort = lsutil_organize::resolve_organize_imports_sort(preferences);

        let mut module_specifier_comparer: Option<Rc<lsutil_organize::StringComparer>> = None;
        let mut named_import_comparer: Option<Rc<lsutil_organize::StringComparer>> = None;
        if sort != OrganizeImportsSort::AUTO {
            module_specifier_comparer = Some(default_comparer.clone());
            named_import_comparer = Some(default_comparer.clone());
        }
        let mut type_order = preferences.organize_imports_type_order;

        if sort == OrganizeImportsSort::AUTO {
            let (result, _) = lsutil_organize::detect_module_specifier_case_by_sort(
                &nodes,
                &top_level_import_group_decls,
                &comparers_to_test,
            );
            module_specifier_comparer = result;
        }

        if type_order == OrganizeImportsTypeOrder::AUTO || sort == OrganizeImportsSort::AUTO {
            let (named_import_comparer2, type_order2, found) =
                lsutil_organize::detect_named_import_organization_by_sort(
                    &nodes,
                    &top_level_import_decls,
                    &comparers_to_test,
                    &type_orders_to_test,
                );
            if found {
                if named_import_comparer.is_none() || sort == OrganizeImportsSort::AUTO {
                    named_import_comparer = named_import_comparer2;
                }
                if type_order == OrganizeImportsTypeOrder::AUTO {
                    type_order = type_order2;
                }
            }
        }

        let comparer = OrganizeImportsComparerSettings {
            module_specifier_comparer,
            named_import_comparer,
            type_order,
        };

        for import_group_decl in &top_level_import_group_decls {
            organize_imports_worker(
                ctx,
                program,
                import_group_decl,
                &comparer,
                should_sort,
                should_combine,
                should_remove,
                source_file,
                &nodes,
                &mut change_tracker,
            );
        }

        if *kind != lsproto::CodeActionKind::SOURCE_REMOVE_UNUSED_IMPORTS_TS {
            let top_level_export_group_decls = get_top_level_export_groups(&nodes, source_file);
            for export_group_decl in &top_level_export_group_decls {
                organize_exports_worker(
                    program,
                    export_group_decl,
                    &comparer,
                    source_file,
                    &mut change_tracker,
                );
            }
        }

        for &stmt in nodes[source_file]
            .as_source_file()
            .statements
            .as_ref()
            .map_or(&[][..], |s| &s.nodes[..])
        {
            if !tsc_ast::is_ambient_module(&nodes[stmt], &nodes) {
                continue;
            }

            let Some(body) = nodes[stmt].as_module_declaration().body_base.body else {
                continue;
            };
            if nodes[body].kind != Kind::ModuleBlock {
                continue;
            }
            let module_body = nodes[body].as_module_block();
            let module_body_statements: &[NodeId] = module_body
                .statements
                .as_ref()
                .map_or(&[][..], |s| &s.nodes[..]);

            let ambient_module_import_decls =
                lsutil_organize::filter_import_declarations(&nodes, module_body_statements)
                    .into_owned();
            let ambient_module_import_group_decls = group_by_newline_contiguous(
                &nodes,
                source_file,
                &ambient_module_import_decls,
            );

            for import_group_decl in &ambient_module_import_group_decls {
                organize_imports_worker(
                    ctx,
                    program,
                    import_group_decl,
                    &comparer,
                    should_sort,
                    should_combine,
                    should_remove,
                    source_file,
                    &nodes,
                    &mut change_tracker,
                );
            }

            if *kind != lsproto::CodeActionKind::SOURCE_REMOVE_UNUSED_IMPORTS_TS {
                let mut ambient_module_export_decls: Vec<NodeId> = Vec::new();
                for &s in module_body_statements {
                    if nodes[s].kind == Kind::ExportDeclaration {
                        ambient_module_export_decls.push(s);
                    }
                }
                organize_exports_worker(
                    program,
                    &ambient_module_export_decls,
                    &comparer,
                    source_file,
                    &mut change_tracker,
                );
            }
        }

        drop(nodes);

        // Unmappable files are dropped by get_changes, so a content-mapped file whose
        // imports cannot be faithfully rewritten yields no edits rather than a
        // corrupting one.
        let (changes, _unmappable) = change_tracker.get_changes();
        changes
    }
}

/// `organizeImportsWorker`.
#[allow(clippy::too_many_arguments)]
fn organize_imports_worker(
    ctx: &Context,
    program: &Rc<Program>,
    old_import_decls: &[NodeId],
    comparer: &OrganizeImportsComparerSettings,
    should_sort: bool,
    should_combine: bool,
    should_remove: bool,
    source_file: NodeId,
    nodes: &Rc<ast::NodeArenaBuf>,
    change_tracker: &mut Tracker<'_, '_>,
) {
    if old_import_decls.is_empty() {
        return;
    }

    // Header comment preservation is handled via LeadingTriviaOption::Exclude
    // in the change tracker below

    let mut processed_imports = old_import_decls.to_vec();
    if should_remove {
        processed_imports = remove_unused_imports(
            ctx,
            program,
            &processed_imports,
            source_file,
            nodes,
            change_tracker,
        );
    }

    // Mutations for the combine/sort phase — dropped before tracker calls so
    // the tracker always sees a live arena.
    let mut nodes_mut = program.nodes_mut(source_file.file_index());
    let mut factory = NodeFactory::new(NodeFactoryHooks::default());
    factory.set_file_index(source_file.file_index());

    let mut new_import_decls: Vec<NodeId>;
    if should_combine {
        let mut grouped = group_by_module_specifier(&nodes_mut, &processed_imports);
        if should_sort {
            grouped.sort_unstable_by(|a, b| {
                if a.is_empty() || b.is_empty() {
                    return std::cmp::Ordering::Equal;
                }
                ordering(lsutil_organize::compare_module_specifiers(
                    &nodes_mut,
                    nodes[a[0]].module_specifier(),
                    nodes[b[0]].module_specifier(),
                    comparer
                        .module_specifier_comparer
                        .as_deref()
                        .expect("moduleSpecifierComparer"),
                ))
            });
        }

        let specifier_comparer = lsutil_organize::get_named_import_specifier_comparer(
            &UserPreferences {
                organize_imports_type_order: comparer.type_order,
                ..Default::default()
            },
            comparer.named_import_comparer.clone(),
        );

        new_import_decls = Vec::new();
        for import_group in &grouped {
            let mut coalesced = coalesce_imports_worker(
                import_group,
                comparer
                    .module_specifier_comparer
                    .as_deref()
                    .expect("moduleSpecifierComparer"),
                specifier_comparer.as_ref(),
                source_file,
                &mut nodes_mut,
                &mut factory,
                change_tracker,
            );
            if should_sort {
                coalesced.sort_by(|a, b| {
                    ordering(
                        lsutil_organize::compare_imports_or_require_statements(
                            &nodes_mut,
                            *a,
                            *b,
                            comparer
                                .module_specifier_comparer
                                .as_deref()
                                .expect("moduleSpecifierComparer"),
                        ),
                    )
                });
            }
            new_import_decls.extend(coalesced);
        }
    } else {
        new_import_decls = processed_imports;
    }

    if should_sort && !should_combine {
        new_import_decls.sort_unstable_by(|a, b| {
            ordering(
                lsutil_organize::compare_imports_or_require_statements(
                    &nodes_mut,
                    *a,
                    *b,
                    comparer
                        .module_specifier_comparer
                        .as_deref()
                        .expect("moduleSpecifierComparer"),
                ),
            )
        });
    }

    drop(nodes_mut);

    let nodes_handle = program.nodes_handle(source_file.file_index());
    if new_import_decls.is_empty() {
        change_tracker.delete_node_range(
            &nodes_handle,
            source_file,
            old_import_decls[0],
            old_import_decls[old_import_decls.len() - 1],
            LeadingTriviaOption::Exclude, // Preserve header comment
            TrailingTriviaOption::Include,
        );
    } else {
        for &imp in &new_import_decls {
            change_tracker
                .emit_context
                .set_emit_flags(imp, EmitFlags::NO_LEADING_COMMENTS);
        }

        let options = NodeOptions {
            leading_trivia_option: LeadingTriviaOption::Exclude, // Preserve header comment
            trailing_trivia_option: TrailingTriviaOption::Include,
            suffix: "\n".to_string(),
            ..Default::default()
        };

        change_tracker.replace_node_with_nodes(
            &nodes_handle,
            source_file,
            old_import_decls[0],
            new_import_decls,
            Some(&options),
        );

        if old_import_decls.len() > 1 {
            for &decl in &old_import_decls[1..] {
                change_tracker.delete(&nodes_handle, source_file, decl);
            }
        }
    }
}

/// `groupByModuleSpecifier` — `map` + insertion-ordered key list, matching
/// Go's deterministic grouping.
fn group_by_module_specifier(nodes: &[Node], imports: &[NodeId]) -> Vec<Vec<NodeId>> {
    let mut groups: HashMap<String, Vec<NodeId>> = HashMap::new();
    let mut order: Vec<String> = Vec::new();

    for &imp in imports {
        let specifier =
            lsutil_organize::get_external_module_name(nodes, nodes[imp].module_specifier());
        groups
            .entry(specifier.clone())
            .or_insert_with(|| {
                order.push(specifier);
                Vec::new()
            })
            .push(imp);
    }

    let mut result: Vec<Vec<NodeId>> = Vec::with_capacity(order.len());
    for key in order {
        result.push(groups.remove(&key).unwrap());
    }
    result
}

/// `removeUnusedImports`. Split into a checker phase (usage decisions —
/// `isDeclarationUsed` mutates the arena internally) and a factory phase
/// (node updates under a `nodes_mut` guard).
fn remove_unused_imports(
    ctx: &Context,
    program: &Rc<Program>,
    old_imports: &[NodeId],
    source_file: NodeId,
    nodes: &Rc<ast::NodeArenaBuf>,
    change_tracker: &mut Tracker<'_, '_>,
) -> Vec<NodeId> {
    let compiler_options = program.options();
    let jsx_elements_present =
        nodes[source_file]
            .subtree_facts(nodes)
            .intersects(SubtreeFacts::CONTAINS_JSX);
    let jsx_mode_needs_explicit_import =
        compiler_options.jsx == JsxEmit::React || compiler_options.jsx == JsxEmit::ReactNative;

    let (checker, done) = program.get_type_checker_for_file(ctx.clone(), source_file);

    // Phase A — usage decisions; no arena guard may be held here.
    enum BindingPlan {
        Keep,
        Drop,
        Filter(Vec<NodeId>),
    }
    struct ClausePlan {
        name: Option<NodeId>,
        binding: BindingPlan,
        /// `namedBindings` node the `MULTI_LINE` flag applies to once built.
        multiline: bool,
    }

    let mut plans: Vec<Option<ClausePlan>> = Vec::with_capacity(old_imports.len());
    for &import_decl in old_imports {
        let Some(import_clause) = nodes[import_decl].as_import_declaration().import_clause
        else {
            plans.push(None);
            continue;
        };

        let clause = nodes[import_clause].as_import_clause();
        let mut name = clause.name;
        let named_bindings = clause.named_bindings;

        if let Some(name_id) = name {
            if !checker.borrow_mut().is_declaration_used(
                source_file,
                name_id,
                jsx_elements_present,
                jsx_mode_needs_explicit_import,
            ) {
                name = None;
            }
        }

        let mut binding = BindingPlan::Keep;
        let mut multiline = false;
        if let Some(named_bindings_id) = named_bindings {
            match nodes[named_bindings_id].kind {
                Kind::NamespaceImport => {
                    let ns_name = nodes[named_bindings_id].name();
                    if let Some(ns_name) = ns_name {
                        if !checker.borrow_mut().is_declaration_used(
                            source_file,
                            ns_name,
                            jsx_elements_present,
                            jsx_mode_needs_explicit_import,
                        ) {
                            binding = BindingPlan::Drop;
                        }
                    }
                }
                Kind::NamedImports => {
                    let named_imports = nodes[named_bindings_id].as_named_imports();
                    let original_elements: Vec<NodeId> = named_imports
                        .elements
                        .as_ref()
                        .map_or_else(Vec::new, |e| e.nodes.to_vec());
                    let mut new_elements: Vec<NodeId> = Vec::new();
                    for &elem in &original_elements {
                        let spec_name = nodes[elem].as_import_specifier().name;
                        if let Some(spec_name) = spec_name {
                            if checker.borrow_mut().is_declaration_used(
                                source_file,
                                spec_name,
                                jsx_elements_present,
                                jsx_mode_needs_explicit_import,
                            ) {
                                new_elements.push(elem);
                            }
                        }
                    }
                    if new_elements.is_empty() {
                        binding = BindingPlan::Drop;
                    } else if new_elements.len() < original_elements.len() {
                        binding = BindingPlan::Filter(new_elements);
                    }
                    if !matches!(binding, BindingPlan::Drop)
                        && !tsc_ast::node_is_synthesized(&nodes[named_bindings_id])
                        && !range_is_on_single_line(
                            nodes,
                            nodes[named_bindings_id].loc,
                            source_file,
                        )
                    {
                        multiline = true;
                    }
                }
                _ => {}
            }
        }

        plans.push(Some(ClausePlan {
            name,
            binding,
            multiline,
        }));
    }

    done();

    // Phase B — build updated declarations.
    let mut nodes_mut = program.nodes_mut(source_file.file_index());
    let mut factory = NodeFactory::new(NodeFactoryHooks::default());
    factory.set_file_index(source_file.file_index());
    let m: &mut Vec<Node> = &mut nodes_mut;

    let mut used_imports: Vec<NodeId> = Vec::with_capacity(old_imports.len());
    for (i, &import_decl) in old_imports.iter().enumerate() {
        let Some(plan) = plans[i].take() else {
            used_imports.push(import_decl);
            continue;
        };

        let import_decl_node = nodes[import_decl].as_import_declaration();
        let import_clause = import_decl_node.import_clause.unwrap();
        let clause = nodes[import_clause].as_import_clause();
        let phase_modifier = clause.phase_modifier;
        let modifiers = nodes[import_decl].modifiers().cloned();
        let module_specifier = import_decl_node.module_specifier;
        let attributes = import_decl_node.attributes;

        let mut named_bindings = clause.named_bindings;
        match plan.binding {
            BindingPlan::Keep => {}
            BindingPlan::Drop => named_bindings = None,
            BindingPlan::Filter(new_elements) => {
                let named_imports = named_bindings.unwrap();
                let new_list = factory.new_node_list(new_elements);
                named_bindings = Some(
                    factory
                        .update_named_imports(m, named_imports, Some(new_list))
                        .unwrap_or(named_imports),
                );
            }
        }
        if plan.multiline {
            if let Some(nb) = named_bindings {
                change_tracker
                    .emit_context
                    .set_emit_flags(nb, EmitFlags::MULTI_LINE);
            }
        }

        if plan.name.is_some() || named_bindings.is_some() {
            let new_clause = factory
                .update_import_clause(
                    m,
                    import_clause,
                    phase_modifier,
                    plan.name,
                    named_bindings,
                )
                .unwrap_or(import_clause);
            let new_import_decl = factory
                .update_import_declaration(
                    m,
                    import_decl,
                    modifiers,
                    Some(new_clause),
                    module_specifier,
                    attributes,
                )
                .unwrap_or(import_decl);
            used_imports.push(new_import_decl);
        } else {
            let module_specifier_node = nodes[import_decl].module_specifier();
            if has_module_declaration_matching_specifier(
                nodes,
                source_file,
                module_specifier_node,
            ) {
                if nodes[source_file].as_source_file().is_declaration_file {
                    let new_import_decl = factory
                        .update_import_declaration(
                            m,
                            import_decl,
                            modifiers,
                            None, // no import clause
                            module_specifier,
                            attributes,
                        )
                        .unwrap_or(import_decl);
                    used_imports.push(new_import_decl);
                } else {
                    used_imports.push(import_decl);
                }
            }
        }
    }

    used_imports
}

/// `filterUsedImportSpecifiers` — folded into `remove_unused_imports` phase A.

/// `hasModuleDeclarationMatchingSpecifier`.
fn has_module_declaration_matching_specifier(
    nodes: &[Node],
    source_file: NodeId,
    module_specifier: Option<NodeId>,
) -> bool {
    let Some(module_specifier) = module_specifier else {
        return false;
    };
    if !tsc_ast::is_string_literal(&nodes[module_specifier]) {
        return false;
    }
    let module_specifier_text = nodes[module_specifier].text(nodes).into_owned();

    for &module_name in &nodes[source_file].as_source_file().module_augmentations {
        if tsc_ast::is_string_literal(&nodes[module_name])
            && nodes[module_name].text(nodes) == module_specifier_text
        {
            return true;
        }
    }

    false
}

/// `getImportAttributesKey` returns a key for grouping imports by their
/// attributes.
fn get_import_attributes_key(nodes: &[Node], attributes: Option<NodeId>) -> String {
    let Some(attributes) = attributes else {
        return String::new();
    };

    let import_attrs = nodes[attributes].as_import_attributes();
    let mut key = String::new();
    key.push_str(import_attrs.token.kind_string());
    key.push(' ');

    let mut attr_nodes: Vec<NodeId> = import_attrs
        .attributes
        .as_ref()
        .map_or_else(Vec::new, |a| a.nodes.to_vec());
    attr_nodes.sort_unstable_by(|a, b| {
        let a_name = nodes[*a]
            .name()
            .map_or_else(String::new, |n| nodes[n].text(nodes).into_owned());
        let b_name = nodes[*b]
            .name()
            .map_or_else(String::new, |n| nodes[n].text(nodes).into_owned());
        ordering(stringutil::compare_strings_case_sensitive(
            a_name.as_bytes(),
            b_name.as_bytes(),
        ))
    });

    for attr_node in attr_nodes {
        let attr = nodes[attr_node].as_import_attribute();
        let attr_name = attr
            .name
            .map_or_else(String::new, |n| nodes[n].text(nodes).into_owned());
        key.push_str(&attr_name);
        key.push(':');
        if let Some(value) = attr.value {
            if tsc_ast::is_string_literal_like(&nodes[value]) {
                key.push('"');
                key.push_str(&nodes[value].text(nodes));
                key.push('"');
            } else {
                key.push_str(&nodes[value].text(nodes));
            }
        }
        key.push(' ');
    }

    key
}

/// `groupByNewlineContiguous` groups declarations by blank lines between them.
fn group_by_newline_contiguous(
    nodes: &Rc<ast::NodeArenaBuf>,
    source_file: NodeId,
    decls: &[NodeId],
) -> Vec<Vec<NodeId>> {
    let text = nodes[source_file].as_source_file().text();
    let mut s = scanner::scanner::Scanner::new();
    s.set_skip_trivia(false); // Must not skip trivia to detect newlines
    let mut groups: Vec<Vec<NodeId>> = Vec::new();
    let mut current_group: Vec<NodeId> = Vec::new();

    for &decl in decls {
        if !current_group.is_empty() && is_new_group(text, nodes[decl].pos(), &mut s) {
            groups.push(std::mem::take(&mut current_group));
        }
        current_group.push(decl);
    }

    if !current_group.is_empty() {
        groups.push(current_group);
    }

    groups
}

/// `isNewGroup`.
fn is_new_group<'t>(
    text: &'t str,
    decl_pos: i32,
    s: &mut scanner::scanner::Scanner<'t>,
) -> bool {
    let full_start = decl_pos;
    if full_start < 0 {
        return false;
    }
    let full_start = full_start as usize;

    let text_len = text.len();
    if full_start >= text_len {
        return false;
    }

    let start_pos = scanner::scanner::skip_trivia(text, full_start as i32);
    if start_pos as usize <= full_start {
        return false;
    }

    let trivia_len = start_pos as usize - full_start;
    s.set_text(&text[full_start..start_pos as usize]);

    let mut number_of_new_lines = 0;
    while s.token_start() < trivia_len {
        let token_kind = s.scan();
        if token_kind == Kind::NewLineTrivia {
            number_of_new_lines += 1;
            if number_of_new_lines >= 2 {
                return true;
            }
        }
    }

    false
}

/// `coalesceImportsWorker`.
#[allow(clippy::too_many_arguments)]
/// PORT: every node read goes through `m` (the guard's working buffer)
/// because `import_decls` may contain nodes minted by the remove-unused
/// phase that are not yet visible in any snapshot.
fn coalesce_imports_worker(
    import_decls: &[NodeId],
    comparer: &dyn Fn(&str, &str) -> i32,
    specifier_comparer: &lsutil_organize::SpecifierComparer,
    source_file: NodeId,
    m: &mut Vec<Node>,
    factory: &mut NodeFactory,
    change_tracker: &mut Tracker<'_, '_>,
) -> Vec<NodeId> {
    if import_decls.is_empty() {
        return import_decls.to_vec();
    }

    let mut import_groups_by_attributes: HashMap<String, Vec<NodeId>> = HashMap::new();
    let mut attribute_keys: Vec<String> = Vec::new();

    for &import_decl in import_decls {
        let key = get_import_attributes_key(
            m,
            m[import_decl].as_import_declaration().attributes,
        );
        import_groups_by_attributes
            .entry(key.clone())
            .or_insert_with(|| {
                attribute_keys.push(key);
                Vec::new()
            })
            .push(import_decl);
    }

    let mut coalesced_imports: Vec<NodeId> = Vec::new();

    for attribute_key in &attribute_keys {
        let import_group_same_attrs = import_groups_by_attributes[attribute_key].clone();
        let categorized = get_categorized_imports(m, &import_group_same_attrs);

        if let Some(import_without_clause) = categorized.import_without_clause {
            coalesced_imports.push(import_without_clause);
        }
        let mut source_phase_imports = categorized.source_phase_imports.clone();
        source_phase_imports.sort_by(|a, b| {
            let a_clause = m[*a].as_import_declaration().import_clause;
            let b_clause = m[*b].as_import_declaration().import_clause;
            let a_name = a_clause.and_then(|c| m[c].name());
            let b_name = b_clause.and_then(|c| m[c].name());
            if a_name.is_none() && b_name.is_none() {
                return std::cmp::Ordering::Equal;
            }
            if a_name.is_none() {
                return std::cmp::Ordering::Greater;
            }
            if b_name.is_none() {
                return std::cmp::Ordering::Less;
            }
            ordering(specifier_comparer(
                m,
                a_clause.unwrap(),
                b_clause.unwrap(),
            ))
        });
        coalesced_imports.extend(source_phase_imports);

        for (i, group) in [
            &categorized.regular_imports,
            &categorized.type_only_imports,
        ]
        .into_iter()
        .enumerate()
        {
            if group.is_empty() {
                continue;
            }

            let is_type_only = i == 1;

            if !is_type_only
                && group.default_imports.len() == 1
                && group.namespace_imports.len() == 1
                && group.named_imports.is_empty()
            {
                let default_import = group.default_imports[0];
                let namespace_import = group.namespace_imports[0];

                let default_clause =
                    m[default_import].as_import_declaration().import_clause.unwrap();
                let namespace_bindings = m[m[namespace_import]
                    .as_import_declaration()
                    .import_clause
                    .unwrap()]
                .as_import_clause()
                .named_bindings;

                let default_phase = m[default_clause].as_import_clause().phase_modifier;
                let default_name = m[default_clause].name();
                let new_clause = factory
                    .update_import_clause(
                        m,
                        default_clause,
                        default_phase,
                        default_name,
                        namespace_bindings,
                    )
                    .unwrap_or(default_clause);
                let default_decl = m[default_import].as_import_declaration();
                let modifiers = m[default_import].modifiers().cloned();
                let module_specifier = default_decl.module_specifier;
                let attributes = default_decl.attributes;
                let new_import_decl = factory
                    .update_import_declaration(
                        m,
                        default_import,
                        modifiers,
                        Some(new_clause),
                        module_specifier,
                        attributes,
                    )
                    .unwrap_or(default_import);
                coalesced_imports.push(new_import_decl);
                continue;
            }

            let mut namespace_imports = group.namespace_imports.clone();
            namespace_imports.sort_unstable_by(|a, b| {
                let n1 = m[m[m[*a].as_import_declaration().import_clause.unwrap()]
                    .as_import_clause()
                    .named_bindings
                    .unwrap()]
                .name()
                .map_or_else(String::new, |n| m[n].text(m).into_owned());
                let n2 = m[m[m[*b].as_import_declaration().import_clause.unwrap()]
                    .as_import_clause()
                    .named_bindings
                    .unwrap()]
                .name()
                .map_or_else(String::new, |n| m[n].text(m).into_owned());
                ordering(comparer(&n1, &n2))
            });

            for &ns_import in &namespace_imports {
                // Hoist all `m` reads before the `&mut m` factory calls.
                let ns_import_decl = m[ns_import].as_import_declaration();
                let clause_id = ns_import_decl.import_clause.unwrap();
                let module_specifier = ns_import_decl.module_specifier;
                let attributes = ns_import_decl.attributes;
                let clause_named_bindings = m[clause_id].as_import_clause().named_bindings;
                let phase = m[clause_id].as_import_clause().phase_modifier;
                let modifiers = m[ns_import].modifiers().cloned();
                let new_clause = factory
                    .update_import_clause(m, clause_id, phase, None, clause_named_bindings)
                    .unwrap_or(clause_id);
                let new_import_decl = factory
                    .update_import_declaration(
                        m,
                        ns_import,
                        modifiers,
                        Some(new_clause),
                        module_specifier,
                        attributes,
                    )
                    .unwrap_or(ns_import);
                coalesced_imports.push(new_import_decl);
            }

            let mut first_default_import: Option<NodeId> = None;
            let mut first_named_import: Option<NodeId> = None;

            if !group.default_imports.is_empty() {
                first_default_import = Some(group.default_imports[0]);
            }
            if !group.named_imports.is_empty() {
                first_named_import = Some(group.named_imports[0]);
            }

            let mut import_decl = first_default_import;
            if import_decl.is_none() {
                import_decl = first_named_import;
            }
            let Some(import_decl) = import_decl else {
                continue;
            };

            let mut new_default_import: Option<NodeId> = None;
            let mut new_import_specifiers: Vec<NodeId> = Vec::new();

            if group.default_imports.len() == 1 {
                new_default_import =
                    m[m[group.default_imports[0]]
                        .as_import_declaration()
                        .import_clause
                        .unwrap()]
                    .name();
            } else {
                for &default_import in &group.default_imports {
                    let default_clause =
                        m[default_import].as_import_declaration().import_clause.unwrap();
                    let default_name = m[default_clause].name();
                    let property_name = factory.new_identifier(m, "default");
                    let import_spec = factory.new_import_specifier(
                        m,
                        false,
                        Some(property_name),
                        default_name,
                    );
                    new_import_specifiers.push(import_spec);
                }
            }

            new_import_specifiers.extend(get_new_import_specifiers(
                m,
                &group.named_imports,
                factory,
            ));
            new_import_specifiers.sort_by(|a, b| {
                ordering(specifier_comparer(m, *a, *b))
            });

            let mut new_named_imports: Option<NodeId> = None;
            if new_import_specifiers.is_empty() {
                if new_default_import.is_some() {
                    new_named_imports = None;
                } else {
                    new_named_imports =
                        Some(factory.new_named_imports(m, Some(factory.new_node_list([]))));
                }
            } else {
                let mut sorted_list = factory.new_node_list(new_import_specifiers);
                if let Some(first_named_import) = first_named_import {
                    let first_named_bindings = m[m[first_named_import]
                        .as_import_declaration()
                        .import_clause
                        .unwrap()]
                    .as_import_clause()
                    .named_bindings
                    .unwrap();
                    let original_elements = m[first_named_bindings]
                        .as_named_imports()
                        .elements
                        .clone();
                    if let Some(original_elements) = &original_elements {
                        if original_elements.has_trailing_comma(m) {
                            sorted_list.loc = original_elements.loc;
                        }
                    }
                    new_named_imports = Some(
                        factory
                            .update_named_imports(m, first_named_bindings, Some(sorted_list))
                            .unwrap_or(first_named_bindings),
                    );
                } else {
                    new_named_imports = Some(factory.new_named_imports(m, Some(sorted_list)));
                }
            }

            if let (Some(new_named_imports_id), Some(first_named_import)) =
                (new_named_imports, first_named_import)
            {
                let first_named_bindings = m[m[first_named_import]
                    .as_import_declaration()
                    .import_clause
                    .unwrap()]
                .as_import_clause()
                .named_bindings
                .unwrap();
                if !tsc_ast::node_is_synthesized(&m[first_named_bindings])
                    && !range_is_on_single_line(
                        m,
                        m[first_named_bindings].loc,
                        source_file,
                    )
                {
                    change_tracker
                        .emit_context
                        .set_emit_flags(new_named_imports_id, EmitFlags::MULTI_LINE);
                }
            }

            if is_type_only && new_default_import.is_some() && new_named_imports.is_some() {
                let import_decl_clause =
                    m[import_decl].as_import_declaration().import_clause.unwrap();
                let phase = m[import_decl_clause].as_import_clause().phase_modifier;
                let default_clause =
                    factory.new_import_clause(m, phase, new_default_import, None);
                let modifiers = m[import_decl].modifiers().cloned();
                let module_specifier = m[import_decl].as_import_declaration().module_specifier;
                let attributes = m[import_decl].as_import_declaration().attributes;
                let default_import_decl = factory
                    .update_import_declaration(
                        m,
                        import_decl,
                        modifiers.clone(),
                        Some(default_clause),
                        module_specifier,
                        attributes,
                    )
                    .unwrap_or(import_decl);
                coalesced_imports.push(default_import_decl);

                let mut named_decl_node = first_named_import;
                if named_decl_node.is_none() {
                    named_decl_node = Some(import_decl);
                }
                let named_decl_node = named_decl_node.unwrap();
                let named_import_decl_clause =
                    m[named_decl_node].as_import_declaration().import_clause.unwrap();
                let named_phase = m[named_import_decl_clause]
                    .as_import_clause()
                    .phase_modifier;
                let named_clause = factory.new_import_clause(
                    m,
                    named_phase,
                    None,
                    new_named_imports,
                );
                let named_modifiers = m[named_decl_node].modifiers().cloned();
                let named_module_specifier =
                    m[named_decl_node].as_import_declaration().module_specifier;
                let named_attributes = m[named_decl_node].as_import_declaration().attributes;
                let named_import_decl = factory
                    .update_import_declaration(
                        m,
                        named_decl_node,
                        named_modifiers,
                        Some(named_clause),
                        named_module_specifier,
                        named_attributes,
                    )
                    .unwrap_or(named_decl_node);
                coalesced_imports.push(named_import_decl);
            } else {
                let clause_node =
                    m[import_decl].as_import_declaration().import_clause.unwrap();
                let phase = m[clause_node].as_import_clause().phase_modifier;
                let new_clause = factory
                    .update_import_clause(
                        m,
                        clause_node,
                        phase,
                        new_default_import,
                        new_named_imports,
                    )
                    .unwrap_or(clause_node);
                let modifiers = m[import_decl].modifiers().cloned();
                let module_specifier = m[import_decl].as_import_declaration().module_specifier;
                let attributes = m[import_decl].as_import_declaration().attributes;
                let new_import_decl = factory
                    .update_import_declaration(
                        m,
                        import_decl,
                        modifiers,
                        Some(new_clause),
                        module_specifier,
                        attributes,
                    )
                    .unwrap_or(import_decl);
                coalesced_imports.push(new_import_decl);
            }
        }
    }
    coalesced_imports
}

/// `categorizedImports`.
#[derive(Default)]
struct CategorizedImports {
    import_without_clause: Option<NodeId>,
    source_phase_imports: Vec<NodeId>,
    type_only_imports: ImportGroup,
    regular_imports: ImportGroup,
}

/// `importGroup`.
#[derive(Default, Clone)]
struct ImportGroup {
    default_imports: Vec<NodeId>,
    namespace_imports: Vec<NodeId>,
    named_imports: Vec<NodeId>,
}

impl ImportGroup {
    fn is_empty(&self) -> bool {
        self.default_imports.is_empty()
            && self.namespace_imports.is_empty()
            && self.named_imports.is_empty()
    }
}

/// `getCategorizedImports`.
fn get_categorized_imports(nodes: &[Node], import_decls: &[NodeId]) -> CategorizedImports {
    let mut import_without_clause: Option<NodeId> = None;
    let mut source_phase_imports: Vec<NodeId> = Vec::new();
    let mut type_only_imports = ImportGroup::default();
    let mut regular_imports = ImportGroup::default();

    for &import_decl in import_decls {
        let Some(import_clause_id) = nodes[import_decl].as_import_declaration().import_clause
        else {
            if import_without_clause.is_none() {
                import_without_clause = Some(import_decl);
            }
            continue;
        };

        let clause = nodes[import_clause_id].as_import_clause();
        if clause.phase_modifier == Kind::SourceKeyword {
            source_phase_imports.push(import_decl);
            continue;
        }
        let group = if nodes[import_clause_id].is_type_only() {
            &mut type_only_imports
        } else {
            &mut regular_imports
        };

        let name = clause.name;
        let named_bindings = clause.named_bindings;

        if name.is_some() {
            group.default_imports.push(import_decl);
        }

        if let Some(named_bindings_id) = named_bindings {
            match nodes[named_bindings_id].kind {
                Kind::NamespaceImport => group.namespace_imports.push(import_decl),
                Kind::NamedImports => group.named_imports.push(import_decl),
                _ => {}
            }
        }
    }

    CategorizedImports {
        import_without_clause,
        source_phase_imports,
        type_only_imports,
        regular_imports,
    }
}

/// `getNewImportSpecifiers`.
fn get_new_import_specifiers(
    nodes: &mut Vec<Node>,
    named_imports: &[NodeId],
    factory: &mut NodeFactory,
) -> Vec<NodeId> {
    let mut result: Vec<NodeId> = Vec::new();

    for &named_import in named_imports {
        let Some(elements) = try_get_named_binding_elements(nodes, named_import) else {
            continue;
        };

        for elem in elements {
            let spec = nodes[elem].as_import_specifier();
            if let (Some(property_name), Some(name)) = (spec.property_name, spec.name) {
                let property_text = nodes[property_name].text(nodes).into_owned();
                let name_text = nodes[name].text(nodes).into_owned();

                if property_text == name_text {
                    let is_type_only = spec.is_type_only;
                    let normalized = factory
                        .update_import_specifier(nodes, elem, is_type_only, None, Some(name))
                        .unwrap_or(elem);
                    result.push(normalized);
                    continue;
                }
            }

            result.push(elem);
        }
    }

    result
}

/// `tryGetNamedBindingElements`.
fn try_get_named_binding_elements(nodes: &[Node], named_import: NodeId) -> Option<Vec<NodeId>> {
    if nodes[named_import].kind != Kind::ImportDeclaration {
        return None;
    }

    let import_decl = nodes[named_import].as_import_declaration();
    let import_clause = import_decl.import_clause?;
    let clause = nodes[import_clause].as_import_clause();
    let named_bindings = clause.named_bindings?;

    if nodes[named_bindings].kind == Kind::NamedImports {
        let named_imports_node = nodes[named_bindings].as_named_imports();
        return named_imports_node
            .elements
            .as_ref()
            .map(|e| e.nodes.to_vec());
    }

    None
}

/// `getTopLevelExportGroups`.
fn get_top_level_export_groups(
    nodes: &Rc<ast::NodeArenaBuf>,
    source_file: NodeId,
) -> Vec<Vec<NodeId>> {
    let mut top_level_export_groups: Vec<Vec<NodeId>> = Vec::new();
    let statements: &[NodeId] = nodes[source_file]
        .as_source_file()
        .statements
        .as_ref()
        .map_or(&[][..], |s| &s.nodes[..]);
    let statements_len = statements.len();

    let mut i = 0;
    let mut group_index = 0;
    while i < statements_len {
        if nodes[statements[i]].kind == Kind::ExportDeclaration {
            if group_index >= top_level_export_groups.len() {
                top_level_export_groups.push(Vec::new());
            }
            let export_decl = nodes[statements[i]].as_export_declaration();
            if export_decl.module_specifier.is_some() {
                top_level_export_groups[group_index].push(statements[i]);
                i += 1;
            } else {
                while i < statements_len && nodes[statements[i]].kind == Kind::ExportDeclaration
                {
                    top_level_export_groups[group_index].push(statements[i]);
                    i += 1;
                }
                group_index += 1;
            }
        } else {
            i += 1;
            if group_index < top_level_export_groups.len()
                && !top_level_export_groups[group_index].is_empty()
            {
                group_index += 1;
            }
        }
    }

    let mut result: Vec<Vec<NodeId>> = Vec::new();
    for export_group in &top_level_export_groups {
        let sub_groups = group_by_newline_contiguous(nodes, source_file, export_group);
        result.extend(sub_groups);
    }

    result
}

/// `organizeExportsWorker`.
fn organize_exports_worker(
    program: &Rc<Program>,
    old_export_decls: &[NodeId],
    comparer: &OrganizeImportsComparerSettings,
    source_file: NodeId,
    change_tracker: &mut Tracker<'_, '_>,
) {
    if old_export_decls.is_empty() {
        return;
    }

    let specifier_comparer = lsutil_organize::get_named_import_specifier_comparer(
        &UserPreferences {
            organize_imports_type_order: comparer.type_order,
            ..Default::default()
        },
        comparer.named_import_comparer.clone(),
    );

    let mut nodes_mut = program.nodes_mut(source_file.file_index());
    let mut factory = NodeFactory::new(NodeFactoryHooks::default());
    factory.set_file_index(source_file.file_index());

    let new_export_decls = coalesce_exports_worker(
        old_export_decls,
        specifier_comparer.as_ref(),
        comparer
            .module_specifier_comparer
            .as_deref()
            .expect("moduleSpecifierComparer"),
        source_file,
        &mut nodes_mut,
        &mut factory,
        change_tracker,
    );

    drop(nodes_mut);

    let nodes_handle = program.nodes_handle(source_file.file_index());
    if new_export_decls.is_empty() {
        change_tracker.delete_node_range(
            &nodes_handle,
            source_file,
            old_export_decls[0],
            old_export_decls[old_export_decls.len() - 1],
            LeadingTriviaOption::Exclude,
            TrailingTriviaOption::Include,
        );
    } else {
        for &exp in &new_export_decls {
            change_tracker
                .emit_context
                .add_emit_flags(exp, EmitFlags::NO_LEADING_COMMENTS);
        }

        let options = NodeOptions {
            leading_trivia_option: LeadingTriviaOption::Exclude,
            trailing_trivia_option: TrailingTriviaOption::Include,
            suffix: "\n".to_string(),
            ..Default::default()
        };

        change_tracker.replace_node_with_nodes(
            &nodes_handle,
            source_file,
            old_export_decls[0],
            new_export_decls,
            Some(&options),
        );

        if old_export_decls.len() > 1 {
            for &decl in &old_export_decls[1..] {
                change_tracker.delete(&nodes_handle, source_file, decl);
            }
        }
    }
}

/// `coalesceExportsWorker`.
#[allow(clippy::too_many_arguments)]
fn coalesce_exports_worker(
    export_group: &[NodeId],
    specifier_comparer: &lsutil_organize::SpecifierComparer,
    module_specifier_comparer: &dyn Fn(&str, &str) -> i32,
    source_file: NodeId,
    m: &mut Vec<Node>,
    factory: &mut NodeFactory,
    change_tracker: &mut Tracker<'_, '_>,
) -> Vec<NodeId> {
    if export_group.is_empty() {
        return export_group.to_vec();
    }

    let mut exports_by_module_specifier: HashMap<String, Vec<NodeId>> = HashMap::new();
    let mut module_specifier_order: Vec<String> = Vec::new();

    for &export_decl in export_group {
        let export = m[export_decl].as_export_declaration();
        let module_specifier = export
            .module_specifier
            .map_or_else(String::new, |ms| m[ms].text(m).into_owned());
        exports_by_module_specifier
            .entry(module_specifier.clone())
            .or_insert_with(|| {
                module_specifier_order.push(module_specifier);
                Vec::new()
            })
            .push(export_decl);
    }

    module_specifier_order.sort_by(|a, b| {
        if a.is_empty() && !b.is_empty() {
            return std::cmp::Ordering::Greater;
        }
        if !a.is_empty() && b.is_empty() {
            return std::cmp::Ordering::Less;
        }
        ordering(module_specifier_comparer(a, b))
    });

    let mut coalesced_exports: Vec<NodeId> = Vec::new();

    for module_specifier in &module_specifier_order {
        let group = exports_by_module_specifier[module_specifier].clone();

        let categorized = get_categorized_exports(m, &group);

        if let Some(export_without_clause) = categorized.export_without_clause {
            coalesced_exports.push(export_without_clause);
        }

        for sub_group in [&categorized.named_exports, &categorized.type_only_exports] {
            if sub_group.is_empty() {
                continue;
            }

            let mut new_export_specifiers: Vec<NodeId> = Vec::new();
            for &export_decl in sub_group {
                if let Some(export_clause) =
                    m[export_decl].as_export_declaration().export_clause
                {
                    if m[export_clause].kind == Kind::NamedExports {
                        if let Some(elements) =
                            m[export_clause].as_named_exports().elements.as_ref()
                        {
                            new_export_specifiers.extend(elements.nodes.iter().copied());
                        }
                    }
                }
            }

            new_export_specifiers.sort_by(|a, b| {
                ordering(specifier_comparer(m, *a, *b))
            });

            let export_decl = sub_group[0];

            let mut updated_export_clause: Option<NodeId> =
                m[export_decl].as_export_declaration().export_clause;
            if let Some(export_clause) = m[export_decl].as_export_declaration().export_clause
            {
                if m[export_clause].kind == Kind::NamedExports {
                    let sorted_list = factory.new_node_list(new_export_specifiers.clone());
                    updated_export_clause = Some(
                        factory
                            .update_named_exports(m, export_clause, Some(sorted_list))
                            .unwrap_or(export_clause),
                    );

                    if !tsc_ast::node_is_synthesized(&m[export_clause])
                        && !range_is_on_single_line(
                            m,
                            m[export_clause].loc,
                            source_file,
                        )
                    {
                        change_tracker.emit_context.set_emit_flags(
                            updated_export_clause.unwrap(),
                            EmitFlags::MULTI_LINE,
                        );
                    }
                }
            }

            let export_decl_data = m[export_decl].as_export_declaration();
            let modifiers = m[export_decl].modifiers().cloned();
            let is_type_only = export_decl_data.is_type_only;
            let module_specifier_id = export_decl_data.module_specifier;
            let attributes = export_decl_data.attributes;
            let new_export_decl = factory
                .update_export_declaration(
                    m,
                    export_decl,
                    modifiers,
                    is_type_only,
                    updated_export_clause,
                    module_specifier_id,
                    attributes,
                )
                .unwrap_or(export_decl);
            coalesced_exports.push(new_export_decl);
        }
    }

    coalesced_exports
}

/// `categorizedExports`.
#[derive(Default)]
struct CategorizedExports {
    export_without_clause: Option<NodeId>,
    named_exports: Vec<NodeId>,
    type_only_exports: Vec<NodeId>,
}

/// `getCategorizedExports`.
fn get_categorized_exports(nodes: &[Node], export_group: &[NodeId]) -> CategorizedExports {
    let mut export_without_clause: Option<NodeId> = None;
    let mut named_exports: Vec<NodeId> = Vec::new();
    let mut type_only_exports: Vec<NodeId> = Vec::new();

    for &export_decl in export_group {
        let export = nodes[export_decl].as_export_declaration();
        if export.export_clause.is_none() {
            if export_without_clause.is_none() {
                export_without_clause = Some(export_decl);
            }
        } else if export.is_type_only {
            type_only_exports.push(export_decl);
        } else {
            named_exports.push(export_decl);
        }
    }

    CategorizedExports {
        export_without_clause,
        named_exports,
        type_only_exports,
    }
}

/// `printer.RangeIsOnSingleLine` — `pub(crate)` in the printer crate, so it
/// is reimplemented here over `skip_trivia` + `positions_are_on_same_line`
/// (mirroring `tracker.rs`'s port of `RangeStartPositionsAreOnSameLine`).
fn range_is_on_single_line(nodes: &[Node], r: TextRange, source_file: NodeId) -> bool {
    let start = scanner::scanner::skip_trivia(
        nodes[source_file].as_source_file().text(),
        r.pos(),
    );
    positions_are_on_same_line(start, r.end(), source_file, nodes)
}
