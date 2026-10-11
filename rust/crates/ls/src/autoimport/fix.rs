// Ported from tsc/internal/ls/autoimport/fix.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(arena): `*ast.SourceFile` → `file: NodeId` plus the owning arena
// `nodes: &Rc<ArenaCell>`; `*ast.Node` → `NodeId`; `*ast.Symbol` →
// `SymbolId`. The `change.Tracker` mints synthesized nodes into `file`'s
// arena via `tracker.node_factory(file)`.

use std::cell::{Ref, RefCell};
use std::rc::Rc;

use tsc_ast::{ArenaCell, Kind, Node, NodeId, self as ast};
use tsc_astnav::tokens as astnav;
use tsc_collections::MultiMap;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::options_generated::{CompilerOptions, ModuleDetectionKind, ModuleKind};
use tsc_core::text::TextRange;
use tsc_core::tristate::Tristate;
use tsc_lsconv::converters::Converters;
use tsc_lsproto as lsproto;
use tsc_lsutil::{self as lsutil, FormatCodeSettings, UserPreferences};
use tsc_modulespecifiers::{self as modulespecifiers, ResultKind};
use tsc_scanner::scanner;
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::autoimport::export::{Export, ExportSyntax, ModuleID};
use crate::autoimport::view::{ExistingImport, View};
use crate::change::{self, LeadingTriviaOption, NodeOptions, Tracker};

/// `type newImportBinding struct`.
#[derive(Clone)]
pub(crate) struct NewImportBinding {
    pub(crate) kind: lsproto::ImportKind,
    pub(crate) property_name: String,
    pub(crate) name: String,
    pub(crate) add_as_type_only: lsproto::AddAsTypeOnly,
}

/// `type Fix struct` — Go embeds `*lsproto.AutoImportFix`.
#[derive(Clone, Default)]
pub struct Fix {
    /// `*lsproto.AutoImportFix` — the serialized fix payload.
    pub auto_import_fix: lsproto::AutoImportFix,
    /// `ModuleSpecifierKind`.
    pub module_specifier_kind: ResultKind,
    /// `IsReExport`.
    pub is_re_export: bool,
    /// `ModuleFileName`.
    pub module_file_name: RootedFilePath,
    /// `TypeOnlyAliasDeclaration`.
    pub type_only_alias_declaration: Option<NodeId>,
}

/// `type addToExistingImportFix struct`.
pub(crate) struct AddToExistingImportFix {
    pub(crate) import_clause_or_binding_pattern: NodeId,
    /// One of `default_import` or `named_import` will be present.
    pub(crate) default_import: Option<NewImportBinding>,
    pub(crate) named_import: Option<NewImportBinding>,
}

impl Fix {
    /// `Edits` produces the text edits and a human-readable description for
    /// the fix. The returned bool is `false` when the fix targets a
    /// content-mapped file and any edit could not be placed within a single
    /// verbatim span, meaning it cannot be safely applied to the original
    /// text and the caller should discard it.
    pub fn edits(
        &self,
        ctx: &Context,
        nodes: &Rc<ArenaCell>,
        file: NodeId,
        compiler_options: &CompilerOptions,
        format_options: FormatCodeSettings,
        converters: &Converters<'_>,
        preferences: &UserPreferences,
    ) -> (Vec<lsproto::TextEdit>, String, bool) {
        let locale = tsc_locale::from_context(ctx);
        let mut tracker =
            change::new_tracker(ctx.clone(), compiler_options, format_options, converters);
        let f = self;
        match f.auto_import_fix.kind {
            k if k == lsproto::AutoImportFixKind::UseNamespace => {
                let description = add_namespace_qualifier(f, &mut tracker, nodes, file, &locale);
                let (edits, safe) = file_edits(&mut tracker, nodes, file);
                (edits, description, safe)
            }
            k if k == lsproto::AutoImportFixKind::AddToExisting => {
                let imports = nodes.snapshot()[file].as_source_file().imports().len();
                if imports <= f.auto_import_fix.import_index as usize {
                    panic!("import index out of range");
                }
                let existing_fix = get_add_to_existing_import_fix(nodes, file, f);
                let named_imports: Vec<NewImportBinding> =
                    tsc_core::core::single_element_slice(existing_fix.named_import);
                add_to_existing_import(
                    &mut tracker,
                    nodes,
                    file,
                    existing_fix.import_clause_or_binding_pattern,
                    existing_fix.default_import.as_ref(),
                    named_imports.iter().collect::<Vec<_>>(),
                    preferences,
                );
                let (edits, safe) = file_edits(&mut tracker, nodes, file);
                (
                    edits,
                    tsc_diagnostics::Update_import_from_0
                        .localize(&locale, &[&f.auto_import_fix.module_specifier]),
                    safe,
                )
            }
            k if k == lsproto::AutoImportFixKind::AddNew => {
                let mut declarations: Vec<NodeId> = Vec::new();
                let default_import =
                    if f.auto_import_fix.import_kind == lsproto::ImportKind::Default {
                        Some(NewImportBinding {
                            kind: lsproto::ImportKind::Default,
                            property_name: String::new(),
                            name: f.auto_import_fix.name.clone(),
                            add_as_type_only: f.auto_import_fix.add_as_type_only,
                        })
                    } else {
                        None
                    };
                let named_imports: Vec<NewImportBinding> =
                    if f.auto_import_fix.import_kind == lsproto::ImportKind::Named {
                        vec![NewImportBinding {
                            kind: lsproto::ImportKind::Named,
                            property_name: String::new(),
                            name: f.auto_import_fix.name.clone(),
                            add_as_type_only: f.auto_import_fix.add_as_type_only,
                        }]
                    } else {
                        Vec::new()
                    };
                let mut namespace_like_import: Option<NewImportBinding> = None;
                if f.auto_import_fix.import_kind == lsproto::ImportKind::Namespace
                    || f.auto_import_fix.import_kind == lsproto::ImportKind::CommonJS
                {
                    namespace_like_import = Some(NewImportBinding {
                        kind: f.auto_import_fix.import_kind,
                        property_name: String::new(),
                        name: f.auto_import_fix.name.clone(),
                        add_as_type_only: f.auto_import_fix.add_as_type_only,
                    });
                }

                let quote_preference = {
                    let n = nodes.snapshot();
                    lsutil::get_quote_preference(&n, file, preferences)
                };
                if f.auto_import_fix.use_require {
                    declarations = get_new_requires(
                        &mut tracker,
                        nodes,
                        file,
                        &f.auto_import_fix.module_specifier,
                        quote_preference,
                        default_import.as_ref(),
                        &named_imports,
                        namespace_like_import.as_ref(),
                        compiler_options,
                    );
                } else {
                    declarations = get_new_imports(
                        &mut tracker,
                        nodes,
                        file,
                        &f.auto_import_fix.module_specifier,
                        quote_preference,
                        default_import.as_ref(),
                        &named_imports,
                        namespace_like_import.as_ref(),
                        compiler_options,
                        preferences,
                    );
                }

                insert_imports(
                    &mut tracker,
                    nodes,
                    file,
                    declarations,
                    true, /*blankLineBetween*/
                    preferences,
                );
                let (edits, safe) = file_edits(&mut tracker, nodes, file);
                (
                    edits,
                    tsc_diagnostics::Add_import_from_0
                        .localize(&locale, &[&f.auto_import_fix.module_specifier]),
                    safe,
                )
            }
            k if k == lsproto::AutoImportFixKind::PromoteTypeOnly => {
                let promoted_declaration = promote_from_type_only(
                    &mut tracker,
                    nodes,
                    f.type_only_alias_declaration
                        .expect("TypeOnlyAliasDeclaration"),
                    compiler_options,
                    file,
                    preferences,
                );
                if nodes.snapshot()[promoted_declaration].kind == Kind::ImportSpecifier {
                    let module_spec = get_module_specifier_text(
                        &nodes.snapshot(),
                        nodes.snapshot()[promoted_declaration]
                            .parent
                            .and_then(|p| nodes.snapshot()[p].parent)
                            .expect("import specifier must have import declaration"),
                    );
                    let (edits, safe) = file_edits(&mut tracker, nodes, file);
                    return (
                        edits,
                        tsc_diagnostics::Remove_type_from_import_of_0_from_1
                            .localize(&locale, &[&f.auto_import_fix.name, &module_spec]),
                        safe,
                    );
                }
                let module_spec = get_module_specifier_text(&nodes.snapshot(), promoted_declaration);
                let (edits, safe) = file_edits(&mut tracker, nodes, file);
                (
                    edits,
                    tsc_diagnostics::Remove_type_from_import_declaration_from_0
                        .localize(&locale, &[&module_spec]),
                    safe,
                )
            }
            k if k == lsproto::AutoImportFixKind::JsdocTypeImport => {
                let description =
                    add_import_type(f, nodes, file, preferences, &mut tracker, &locale);
                let (edits, safe) = file_edits(&mut tracker, nodes, file);
                (edits, description, safe)
            }
            _ => panic!("unimplemented fix edit"),
        }
    }
}

/// `fileEdits` returns the edits recorded for `file`, along with whether they
/// are safe to apply. `get_changes` drops the edits of any content-mapped
/// file that cannot be faithfully mapped back to the original text, so an
/// empty result with `safe == false` means the fix could not be represented
/// and must be discarded.
fn file_edits(
    tracker: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    file: NodeId,
) -> (Vec<lsproto::TextEdit>, bool) {
    let (mut changes, unmappable) = tracker.get_changes();
    let file_name = nodes.snapshot()[file]
        .as_source_file()
        .original_file_name(&nodes.snapshot())
        .clone();
    (
        changes.remove(&file_name).unwrap_or_default(),
        unmappable.is_empty(),
    )
}

/// `addImportType`.
pub(crate) fn add_import_type(
    f: &Fix,
    nodes: &Rc<ArenaCell>,
    file: NodeId,
    preferences: &UserPreferences,
    tracker: &mut Tracker<'_, '_>,
    locale: &tsc_locale::Locale,
) -> String {
    let Some(usage_position) = f.auto_import_fix.usage_position else {
        panic!("UsagePosition must be set for JSDoc type import fix")
    };
    let quote_preference = {
        let n = nodes.snapshot();
        lsutil::get_quote_preference(&n, file, preferences)
    };
    let quote_char = if quote_preference == lsutil::QuotePreference::SINGLE {
        "'"
    } else {
        "\""
    };
    let import_type_prefix = format!(
        "import({}{}{}).",
        quote_char, f.auto_import_fix.module_specifier, quote_char
    );
    tracker.insert_text(nodes, file, usage_position, &import_type_prefix);
    tsc_diagnostics::Change_0_to_1.localize(
        locale,
        &[
            &f.auto_import_fix.name,
            &format!("{}{}", import_type_prefix, f.auto_import_fix.name),
        ],
    )
}

/// `addNamespaceQualifier`.
pub(crate) fn add_namespace_qualifier(
    f: &Fix,
    tracker: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    file: NodeId,
    locale: &tsc_locale::Locale,
) -> String {
    if f.auto_import_fix.usage_position.is_none() || f.auto_import_fix.namespace_prefix.is_empty() {
        panic!("namespace fix requires usage position and prefix");
    }
    let qualified = format!(
        "{}.{}",
        f.auto_import_fix.namespace_prefix, f.auto_import_fix.name
    );
    tracker.insert_text(
        nodes,
        file,
        f.auto_import_fix.usage_position.unwrap(),
        &format!("{}.", f.auto_import_fix.namespace_prefix),
    );
    tsc_diagnostics::Change_0_to_1.localize(locale, &[&f.auto_import_fix.name, &qualified])
}

/// `getAddToExistingImportFix`.
pub(crate) fn get_add_to_existing_import_fix(
    nodes: &Rc<ArenaCell>,
    file: NodeId,
    fix: &Fix,
) -> AddToExistingImportFix {
    if fix.auto_import_fix.kind != lsproto::AutoImportFixKind::AddToExisting {
        panic!("expected add to existing import fix");
    }
    let n = nodes.snapshot();
    let module_specifier =
        n[file].as_source_file().imports()[fix.auto_import_fix.import_index as usize];
    let import_node = ast::try_get_import_from_module_specifier(module_specifier, &n)
        .expect("expected import declaration");
    let import_clause_or_binding_pattern = match n[import_node].kind {
        Kind::ImportDeclaration => n[import_node]
            .import_clause()
            .expect("expected import clause"),
        Kind::CallExpression => {
            let parent = n[import_node].parent.expect("import node parent");
            if !ast::is_variable_declaration_initialized_to_require(parent, &n) {
                panic!("expected require call expression to be in variable declaration");
            }
            let name = n[parent].name().expect("variable declaration name");
            if !ast::is_object_binding_pattern(&n[name]) {
                panic!("expected object binding pattern in variable declaration");
            }
            name
        }
        _ => panic!("expected import declaration or require call expression"),
    };

    let default_import = if fix.auto_import_fix.import_kind == lsproto::ImportKind::Default {
        Some(NewImportBinding {
            kind: lsproto::ImportKind::Default,
            property_name: String::new(),
            name: fix.auto_import_fix.name.clone(),
            add_as_type_only: fix.auto_import_fix.add_as_type_only,
        })
    } else {
        None
    };
    let named_import = if fix.auto_import_fix.import_kind == lsproto::ImportKind::Named {
        Some(NewImportBinding {
            kind: lsproto::ImportKind::Named,
            property_name: String::new(),
            name: fix.auto_import_fix.name.clone(),
            add_as_type_only: fix.auto_import_fix.add_as_type_only,
        })
    } else {
        None
    };
    AddToExistingImportFix {
        import_clause_or_binding_pattern,
        default_import,
        named_import,
    }
}

/// `addToExistingImport`.
pub(crate) fn add_to_existing_import(
    ct: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    file: NodeId,
    import_clause_or_binding_pattern: NodeId,
    default_import: Option<&NewImportBinding>,
    named_imports: Vec<&NewImportBinding>,
    preferences: &UserPreferences,
) {
    match nodes.snapshot()[import_clause_or_binding_pattern].kind {
        Kind::ObjectBindingPattern => {
            if let Some(d) = default_import {
                add_element_to_binding_pattern(
                    ct,
                    nodes,
                    file,
                    import_clause_or_binding_pattern,
                    &d.name,
                    "default",
                );
            }
            for named_import in &named_imports {
                add_element_to_binding_pattern(
                    ct,
                    nodes,
                    file,
                    import_clause_or_binding_pattern,
                    &named_import.name,
                    "",
                );
            }
        }
        Kind::ImportClause => {
            // promote_from_type_only = true if we need to promote the entire
            // original clause from type only
            let import_clause_is_type_only =
                { nodes.snapshot()[import_clause_or_binding_pattern].is_type_only() };
            let promote_from_type_only = import_clause_is_type_only
                && named_imports
                    .iter()
                    .chain(default_import.iter())
                    .any(|i| i.add_as_type_only == lsproto::AddAsTypeOnly::NotAllowed);

            let (named_bindings, import_decl) = {
                let n = nodes.snapshot();
                let clause = n[import_clause_or_binding_pattern].as_import_clause();
                (
                    clause.named_bindings,
                    n[import_clause_or_binding_pattern].parent,
                )
            };
            let existing_specifiers: Vec<NodeId> = {
                let n = nodes.snapshot();
                match named_bindings {
                    Some(nb) if n[nb].kind == Kind::NamedImports => {
                        n[nb].elements().map(|e| e.to_vec()).unwrap_or_default()
                    }
                    _ => Vec::new(),
                }
            };

            if let Some(d) = default_import {
                debug_assert!(
                    nodes.snapshot()[import_clause_or_binding_pattern]
                        .name()
                        .is_none(),
                    "Cannot add a default import to an import clause that already has one"
                );
                let identifier = {
                    let mut n = nodes.cow();
                    ct.node_factory(file).new_identifier(&mut n, &d.name)
                };
                let start = {
                    let mut n = nodes.cow();
                    astnav::get_start_of_node(&mut n, file, import_clause_or_binding_pattern, false)
                };
                ct.insert_node_at(
                    nodes,
                    file,
                    start,
                    identifier,
                    NodeOptions {
                        suffix: ", ".to_string(),
                        ..Default::default()
                    },
                );
            }

            if !named_imports.is_empty() {
                let (specifier_comparer, is_sorted) = {
                    let n = nodes.snapshot();
                    lsutil::get_named_import_specifier_comparer_with_detection(
                        &n,
                        import_decl.expect("import clause parent"),
                        Some(file),
                        preferences,
                    )
                };
                let mut new_specifiers: Vec<NodeId> = Vec::with_capacity(named_imports.len());
                {
                    let mut n = nodes.cow();
                    for named_import in &named_imports {
                        let identifier = if !named_import.property_name.is_empty() {
                            Some(
                                ct.node_factory(file)
                                    .new_identifier(&mut n, &named_import.property_name),
                            )
                        } else {
                            None
                        };
                        let name = ct
                            .node_factory(file)
                            .new_identifier(&mut n, &named_import.name);
                        new_specifiers.push(ct.node_factory(file).new_import_specifier(
                            &mut n,
                            (!import_clause_is_type_only || promote_from_type_only)
                                && should_use_type_only(named_import.add_as_type_only, preferences),
                            identifier,
                            Some(name),
                        ));
                    }
                }
                {
                    let n = nodes.snapshot();
                    new_specifiers.sort_by(|a, b| specifier_comparer(&n, *a, *b).cmp(&0));
                }
                if !existing_specifiers.is_empty() && is_sorted != Tristate::False {
                    // The sorting preference computed earlier may or may not have validated
                    // that these particular import specifiers are sorted. If they aren't,
                    // `getImportSpecifierInsertionIndex` will return nonsense. So if there are
                    // existing specifiers, even if we know the sorting preference, we
                    // need to ensure that the existing specifiers are sorted according to
                    // the preference in order to do a sorted insertion.

                    // If we're promoting the clause from type-only, we need to transform the
                    // existing imports before attempting to insert the new named imports
                    // (for comparison purposes only)
                    let specs_to_compare_against: Vec<NodeId> = if promote_from_type_only {
                        let mut n = nodes.cow();
                        existing_specifiers
                            .iter()
                            .map(|&e| {
                                let spec = n[e].as_import_specifier();
                                let property_name = spec.property_name;
                                let name = spec.name;
                                ct.node_factory(file).new_import_specifier(
                                    &mut n,
                                    true, // isTypeOnly
                                    property_name,
                                    name,
                                )
                            })
                            .collect()
                    } else {
                        existing_specifiers.clone()
                    };

                    for &spec in &new_specifiers {
                        let insertion_index = {
                            let n = nodes.snapshot();
                            lsutil::get_import_specifier_insertion_index(
                                &n,
                                &specs_to_compare_against,
                                spec,
                                &*specifier_comparer,
                            )
                        };
                        ct.insert_import_specifier_at_index(
                            nodes,
                            file,
                            spec,
                            named_bindings.expect("named bindings"),
                            insertion_index,
                        );
                    }
                } else if !existing_specifiers.is_empty() {
                    for &spec in &new_specifiers {
                        ct.insert_node_in_list_after(
                            nodes,
                            file,
                            existing_specifiers[existing_specifiers.len() - 1],
                            spec,
                            None,
                        );
                    }
                } else if !new_specifiers.is_empty() {
                    let named_imports_list = {
                        let mut n = nodes.cow();
                        let list = ct.node_factory(file).new_node_list(new_specifiers.clone());
                        ct.node_factory(file).new_named_imports(&mut n, Some(list))
                    };
                    match named_bindings {
                        Some(nb) => {
                            ct.replace_node(nodes, file, nb, named_imports_list, None);
                        }
                        None => {
                            let clause_name =
                                { nodes.snapshot()[import_clause_or_binding_pattern].name() };
                            let Some(clause_name) = clause_name else {
                                panic!(
                                    "Import clause must have either named imports or a default import"
                                )
                            };
                            ct.insert_node_after(nodes, file, clause_name, named_imports_list);
                        }
                    }
                }
            }

            if promote_from_type_only {
                // Delete the 'type' keyword from the import clause
                let type_keyword = {
                    let mut n = nodes.cow();
                    get_type_keyword_of_type_only_import(
                        &mut n,
                        import_clause_or_binding_pattern,
                        file,
                    )
                };
                ct.delete(nodes, file, type_keyword);

                // Add 'type' modifier to existing specifiers (not newly added ones)
                // We preserve the type-onlyness of existing specifiers regardless of whether
                // it would make a difference in emit (user preference).
                for &specifier in &existing_specifiers {
                    if !nodes.snapshot()[specifier].as_import_specifier().is_type_only {
                        ct.insert_modifier_before(nodes, file, Kind::TypeKeyword, specifier);
                    }
                }
            }
        }
        k => {
            panic!("Unsupported clause kind: {:?} for addToExistingImport", k)
        }
    }
}

/// `getTypeKeywordOfTypeOnlyImport`.
fn get_type_keyword_of_type_only_import(
    nodes: &mut Vec<Node>,
    import_clause: NodeId,
    source_file: NodeId,
) -> NodeId {
    debug_assert!(
        nodes[import_clause].is_type_only(),
        "import clause must be type-only"
    );
    // The first child of a type-only import clause is the 'type' keyword
    // import type { foo } from './bar'
    //        ^^^^
    let type_keyword =
        astnav::find_child_of_kind(nodes, source_file, import_clause, Kind::TypeKeyword);
    type_keyword.expect("type-only import clause should have a type keyword")
}

/// `addElementToBindingPattern`.
fn add_element_to_binding_pattern(
    ct: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    file: NodeId,
    binding_pattern: NodeId,
    name: &str,
    property_name: &str,
) {
    let (element, last_element) = {
        let mut n = nodes.cow();
        let identifier = ct.node_factory(file).new_identifier(&mut n, name);
        let prop = if property_name.is_empty() {
            None
        } else {
            Some(ct.node_factory(file).new_identifier(&mut n, property_name))
        };
        let element =
            ct.node_factory(file)
                .new_binding_element(&mut n, None, prop, Some(identifier), None);
        let elements = n[binding_pattern]
            .as_binding_pattern()
            .elements
            .as_ref()
            .map(|e| e.nodes.to_vec())
            .unwrap_or_default();
        (element, elements.last().copied())
    };
    match last_element {
        Some(last) => {
            let elements = nodes.snapshot()[binding_pattern]
                .as_binding_pattern()
                .elements
                .clone();
            ct.insert_node_in_list_after(nodes, file, last, element, elements.as_ref());
        }
        None => {
            let new_pattern = {
                let mut n = nodes.cow();
                let list = ct.node_factory(file).new_node_list(vec![element]);
                ct.node_factory(file).new_binding_pattern(
                    &mut n,
                    Kind::ObjectBindingPattern,
                    Some(list),
                )
            };
            ct.replace_node(nodes, file, binding_pattern, new_pattern, None);
        }
    }
}

/// `getNewImports`.
pub(crate) fn get_new_imports(
    ct: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    file: NodeId,
    module_specifier: &str,
    quote_preference: lsutil::QuotePreference,
    default_import: Option<&NewImportBinding>,
    named_imports: &[NewImportBinding],
    namespace_like_import: Option<&NewImportBinding>,
    compiler_options: &CompilerOptions,
    preferences: &UserPreferences,
) -> Vec<NodeId> {
    let token_flags = if quote_preference == lsutil::QuotePreference::SINGLE {
        ast::TokenFlags::SINGLE_QUOTE
    } else {
        ast::TokenFlags::NONE
    };
    let module_specifier_string_literal = {
        let mut n = nodes.cow();
        ct.node_factory(file)
            .new_string_literal(&mut n, module_specifier, token_flags)
    };
    let mut statements: Vec<NodeId> = Vec::new();
    if default_import.is_some() || !named_imports.is_empty() {
        // `verbatimModuleSyntax` should prefer top-level `import type` -
        // even though it's not an error, it would add unnecessary runtime emit.
        let top_level_type_only = (default_import.is_none()
            || needs_type_only(default_import.unwrap().add_as_type_only))
            && named_imports
                .iter()
                .all(|i| needs_type_only(i.add_as_type_only))
            || (compiler_options.verbatim_module_syntax.is_true()
                || preferences.prefer_type_only_auto_imports.is_true())
                && (default_import.is_none()
                    || default_import.unwrap().add_as_type_only
                        != lsproto::AddAsTypeOnly::NotAllowed)
                && !named_imports
                    .iter()
                    .any(|i| i.add_as_type_only == lsproto::AddAsTypeOnly::NotAllowed);

        let default_import_node = default_import.map(|d| {
            let mut n = nodes.cow();
            ct.node_factory(file).new_identifier(&mut n, &d.name)
        });

        let named_import_nodes: Vec<NodeId> = {
            let mut n = nodes.cow();
            named_imports
                .iter()
                .map(|named_import| {
                    let named_import_property_name = if !named_import.property_name.is_empty() {
                        Some(
                            ct.node_factory(file)
                                .new_identifier(&mut n, &named_import.property_name),
                        )
                    } else {
                        None
                    };
                    let name = ct
                        .node_factory(file)
                        .new_identifier(&mut n, &named_import.name);
                    ct.node_factory(file).new_import_specifier(
                        &mut n,
                        !top_level_type_only
                            && should_use_type_only(named_import.add_as_type_only, preferences),
                        named_import_property_name,
                        Some(name),
                    )
                })
                .collect()
        };
        statements.push(make_import(
            ct,
            nodes,
            file,
            default_import_node,
            named_import_nodes,
            module_specifier_string_literal,
            top_level_type_only,
        ));
    }

    if let Some(ns) = namespace_like_import {
        let declaration = if ns.kind == lsproto::ImportKind::CommonJS {
            let mut n = nodes.cow();
            let name = ct.node_factory(file).new_identifier(&mut n, &ns.name);
            let module_ref = ct
                .node_factory(file)
                .new_external_module_reference(&mut n, Some(module_specifier_string_literal));
            ct.node_factory(file).new_import_equals_declaration(
                &mut n,
                None,
                should_use_type_only(ns.add_as_type_only, preferences),
                Some(name),
                Some(module_ref),
            )
        } else {
            let mut n = nodes.cow();
            let name = ct.node_factory(file).new_identifier(&mut n, &ns.name);
            let ns_import = ct
                .node_factory(file)
                .new_namespace_import(&mut n, Some(name));
            let clause = ct.node_factory(file).new_import_clause(
                &mut n,
                if should_use_type_only(ns.add_as_type_only, preferences) {
                    Kind::TypeKeyword
                } else {
                    Kind::Unknown
                },
                None,
                Some(ns_import),
            );
            ct.node_factory(file).new_import_declaration(
                &mut n,
                None,
                Some(clause),
                Some(module_specifier_string_literal),
                None,
            )
        };
        statements.push(declaration);
    }
    if statements.is_empty() {
        panic!("No statements to insert for new imports");
    }
    statements
}

/// `getNewRequires`.
pub(crate) fn get_new_requires(
    change_tracker: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    file: NodeId,
    module_specifier: &str,
    quote_preference: lsutil::QuotePreference,
    default_import: Option<&NewImportBinding>,
    named_imports: &[NewImportBinding],
    namespace_like_import: Option<&NewImportBinding>,
    _compiler_options: &CompilerOptions,
) -> Vec<NodeId> {
    let quoted_module_specifier = {
        let mut n = nodes.cow();
        change_tracker.node_factory(file).new_string_literal(
            &mut n,
            module_specifier,
            if quote_preference == lsutil::QuotePreference::SINGLE {
                ast::TokenFlags::SINGLE_QUOTE
            } else {
                ast::TokenFlags::NONE
            },
        )
    };
    let mut statements: Vec<NodeId> = Vec::new();

    // const { default: foo, bar, etc } = require('./mod');
    if default_import.is_some() || !named_imports.is_empty() {
        let mut binding_elements: Vec<NodeId> = Vec::new();
        {
            let mut n = nodes.cow();
            for named_import in named_imports {
                let property_name = if !named_import.property_name.is_empty() {
                    Some(
                        change_tracker
                            .node_factory(file)
                            .new_identifier(&mut n, &named_import.property_name),
                    )
                } else {
                    None
                };
                let name = change_tracker
                    .node_factory(file)
                    .new_identifier(&mut n, &named_import.name);
                binding_elements.push(change_tracker.node_factory(file).new_binding_element(
                    &mut n,
                    None,
                    property_name,
                    Some(name),
                    None,
                ));
            }
        }
        if let Some(d) = default_import {
            let mut n = nodes.cow();
            let default_prop = change_tracker
                .node_factory(file)
                .new_identifier(&mut n, "default");
            let name = change_tracker
                .node_factory(file)
                .new_identifier(&mut n, &d.name);
            let element = change_tracker.node_factory(file).new_binding_element(
                &mut n,
                None,
                Some(default_prop),
                Some(name),
                None,
            );
            binding_elements.insert(0, element);
        }
        let declaration = {
            let mut n = nodes.cow();
            let list = change_tracker
                .node_factory(file)
                .new_node_list(binding_elements);
            let pattern = change_tracker.node_factory(file).new_binding_pattern(
                &mut n,
                Kind::ObjectBindingPattern,
                Some(list),
            );
            create_const_equals_require_declaration(
                change_tracker,
                &mut n,
                file,
                pattern,
                quoted_module_specifier,
            )
        };
        statements.push(declaration);
    }

    // const foo = require('./mod');
    if let Some(ns) = namespace_like_import {
        let declaration = {
            let mut n = nodes.cow();
            let name = change_tracker
                .node_factory(file)
                .new_identifier(&mut n, &ns.name);
            create_const_equals_require_declaration(
                change_tracker,
                &mut n,
                file,
                name,
                quoted_module_specifier,
            )
        };
        statements.push(declaration);
    }

    debug_assert!(!statements.is_empty());
    statements
}

/// `createConstEqualsRequireDeclaration`.
fn create_const_equals_require_declaration(
    change_tracker: &mut Tracker<'_, '_>,
    nodes: &mut Vec<Node>,
    file: NodeId,
    name: NodeId,
    quoted_module_specifier: NodeId,
) -> NodeId {
    let require_id = change_tracker
        .node_factory(file)
        .new_identifier(nodes, "require");
    let arg_list = change_tracker
        .node_factory(file)
        .new_node_list(vec![quoted_module_specifier]);
    let call = change_tracker.node_factory(file).new_call_expression(
        nodes,
        Some(require_id),
        None,
        None,
        Some(arg_list),
        ast::NodeFlags::NONE,
    );
    let decl = change_tracker.node_factory(file).new_variable_declaration(
        nodes,
        Some(name),
        None,
        None,
        Some(call),
    );
    let decl_list = change_tracker.node_factory(file).new_node_list(vec![decl]);
    let var_list = change_tracker
        .node_factory(file)
        .new_variable_declaration_list(nodes, Some(decl_list), ast::NodeFlags::CONST);
    change_tracker
        .node_factory(file)
        .new_variable_statement(nodes, None, Some(var_list))
}

/// `insertImports`.
pub(crate) fn insert_imports(
    ct: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    source_file: NodeId,
    imports: Vec<NodeId>,
    blank_line_between: bool,
    preferences: &UserPreferences,
) {
    let existing_import_statements: Vec<NodeId> = {
        let n = nodes.snapshot();
        let statements = n[source_file].statements().unwrap_or(&[]);
        if n[imports[0]].kind == Kind::VariableStatement {
            statements
                .iter()
                .copied()
                .filter(|&s| ast::is_require_variable_statement(&n[s], &n))
                .collect()
        } else {
            statements
                .iter()
                .copied()
                .filter(|&s| ast::is_any_import_syntax(&n[s]))
                .collect()
        }
    };
    let (comparer, is_sorted) = {
        let n = nodes.snapshot();
        lsutil::get_organize_imports_string_comparer_with_detection(
            &n,
            &existing_import_statements,
            preferences,
        )
    };
    let comparer = comparer.unwrap_or_else(|| {
        Rc::new(|a: &str, b: &str| {
            tsc_stringutil::compare_strings_case_sensitive(a.as_bytes(), b.as_bytes())
        }) as Rc<lsutil::StringComparer>
    });
    let mut sorted_new_imports = imports.clone();
    {
        let n = nodes.snapshot();
        sorted_new_imports.sort_by(|a, b| {
            lsutil::compare_imports_or_require_statements(&n, *a, *b, &*comparer).cmp(&0)
        });
    }

    if !existing_import_statements.is_empty() && is_sorted {
        // Existing imports are sorted, insert each new import at the correct position
        for new_import in sorted_new_imports {
            let insertion_index = {
                let n = nodes.snapshot();
                let comparer = comparer.clone();
                lsutil::get_import_declaration_insert_index(
                    &n,
                    &existing_import_statements,
                    new_import,
                    &move |nodes: &[Node], a: NodeId, b: NodeId| {
                        lsutil::compare_imports_or_require_statements(nodes, a, b, &*comparer)
                    },
                )
            };
            if insertion_index == 0 {
                // If the first import is top-of-file, insert after the leading
                // comment which is likely the header.
                let leading_trivia_option = {
                    let n = nodes.snapshot();
                    if n[source_file]
                        .statements()
                        .and_then(|s| s.first().copied())
                        .is_some_and(|s| s == existing_import_statements[0])
                    {
                        LeadingTriviaOption::Exclude
                    } else {
                        LeadingTriviaOption::None
                    }
                };
                ct.insert_node_before(
                    nodes,
                    source_file,
                    existing_import_statements[0],
                    new_import,
                    false, /*blankLineBetween*/
                    leading_trivia_option,
                );
            } else {
                let prev_import = existing_import_statements[insertion_index - 1];
                ct.insert_node_after(nodes, source_file, prev_import, new_import);
            }
        }
    } else if !existing_import_statements.is_empty() {
        let last = existing_import_statements[existing_import_statements.len() - 1];
        ct.insert_nodes_after(nodes, source_file, last, sorted_new_imports);
    } else {
        ct.insert_at_top_of_file(nodes, source_file, sorted_new_imports, blank_line_between);
    }
}

/// `makeImport`.
fn make_import(
    ct: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    file: NodeId,
    default_import: Option<NodeId>,
    named_imports: Vec<NodeId>,
    module_specifier: NodeId,
    is_type_only: bool,
) -> NodeId {
    let mut n = nodes.cow();
    let new_named_imports = if !named_imports.is_empty() {
        let list = ct.node_factory(file).new_node_list(named_imports);
        Some(ct.node_factory(file).new_named_imports(&mut n, Some(list)))
    } else {
        None
    };
    let import_clause = if default_import.is_some() || new_named_imports.is_some() {
        Some(ct.node_factory(file).new_import_clause(
            &mut n,
            if is_type_only {
                Kind::TypeKeyword
            } else {
                Kind::Unknown
            },
            default_import,
            new_named_imports,
        ))
    } else {
        None
    };
    ct.node_factory(file).new_import_declaration(
        &mut n,
        None,
        import_clause,
        Some(module_specifier),
        None,
    )
}

impl View<'_> {
    /// `View.GetFixes`.
    pub fn get_fixes(
        &self,
        export: &Rc<Export>,
        for_jsx: bool,
        is_valid_type_only_use_site: bool,
        usage_position: Option<lsproto::Position>,
    ) -> Vec<Fix> {
        let mut fixes: Vec<Fix> = Vec::new();
        if let Some(namespace_fix) = self.try_use_existing_namespace_import(export, usage_position)
        {
            fixes.push(namespace_fix);
        }

        if let Some(fix) = self.try_add_to_existing_import(export, is_valid_type_only_use_site) {
            fixes.push(fix);
            return fixes;
        }

        // !!! getNewImportFromExistingSpecifier - even worth it?

        let (module_specifier, module_specifier_kind) =
            self.get_module_specifier(export, &self.user_preferences);
        if module_specifier.as_string().is_empty() {
            if !fixes.is_empty() {
                return fixes;
            }
            return Vec::new();
        }

        // Check if we need a JSDoc import type fix (for JS files with type-only imports)
        let is_js = {
            let nodes = self.program.nodes(self.from_file.file_index());
            nodes[self.from_file]
                .as_source_file()
                .file_name()
                .has_js_file_extension()
        };
        let imported_symbol_has_value_meaning =
            export.flags.intersects(ast::SymbolFlags::VALUE) || export.is_unresolved_alias();
        if !imported_symbol_has_value_meaning && is_js && usage_position.is_some() {
            // For pure types in JS files, use JSDoc import type syntax
            return vec![Fix {
                auto_import_fix: lsproto::AutoImportFix {
                    kind: lsproto::AutoImportFixKind::JsdocTypeImport,
                    module_specifier: module_specifier.as_string().to_string(),
                    name: export.name().to_string(),
                    usage_position,
                    ..Default::default()
                },
                module_specifier_kind,
                is_re_export: export.target.module_id != export.export_id.module_id,
                module_file_name: export.module_file_name.clone(),
                ..Default::default()
            }];
        }

        let import_kind = get_import_kind(
            self.from_file,
            export,
            &self.program,
            false, /*forceImportKeyword*/
        );
        let add_as_type_only =
            get_add_as_type_only(is_valid_type_only_use_site, export, &self.program.options());

        let mut name = export.name().to_string();
        let starts_with_upper = name.chars().next().is_some_and(char::is_uppercase);
        if for_jsx && !starts_with_upper {
            if export.is_renameable() {
                let mut chars = name.chars();
                let first = chars.next().unwrap().to_uppercase();
                name = format!("{}{}", first, chars.as_str());
            } else {
                return Vec::new();
            }
        }

        fixes.push(Fix {
            auto_import_fix: lsproto::AutoImportFix {
                kind: lsproto::AutoImportFixKind::AddNew,
                import_kind,
                module_specifier: module_specifier.as_string().to_string(),
                name,
                use_require: self.should_use_require(),
                add_as_type_only,
                ..Default::default()
            },
            module_specifier_kind,
            is_re_export: export.target.module_id != export.export_id.module_id,
            module_file_name: export.module_file_name.clone(),
            ..Default::default()
        });
        fixes
    }

    /// `View.tryUseExistingNamespaceImport`.
    fn try_use_existing_namespace_import(
        &self,
        export: &Export,
        usage_position: Option<lsproto::Position>,
    ) -> Option<Fix> {
        let usage_position = usage_position?;

        if get_import_kind(self.from_file, export, &self.program, false)
            != lsproto::ImportKind::Named
        {
            return None;
        }

        let existing_imports = self.get_existing_imports();
        for existing_import in existing_imports.get(&export.export_id.module_id) {
            let namespace_prefix = {
                let nodes = self.program.nodes(self.from_file.file_index());
                get_namespace_like_import_text(&nodes, existing_import.node)
            };
            if namespace_prefix.is_empty() || existing_import.module_specifier.is_empty() {
                continue;
            }
            return Some(Fix {
                auto_import_fix: lsproto::AutoImportFix {
                    kind: lsproto::AutoImportFixKind::UseNamespace,
                    name: export.name().to_string(),
                    module_specifier: existing_import.module_specifier.clone(),
                    import_kind: lsproto::ImportKind::Namespace,
                    add_as_type_only: lsproto::AddAsTypeOnly::Allowed,
                    import_index: existing_import.index as i32,
                    usage_position: Some(usage_position),
                    namespace_prefix,
                    ..Default::default()
                },
                ..Default::default()
            });
        }

        None
    }

    /// `View.tryAddToExistingImport`.
    fn try_add_to_existing_import(
        &self,
        export: &Export,
        is_valid_type_only_use_site: bool,
    ) -> Option<Fix> {
        let existing_imports = self.get_existing_imports();
        let matching_declarations = existing_imports.get(&export.export_id.module_id);
        if matching_declarations.is_empty() {
            return None;
        }
        let matching_declarations: Vec<ExistingImport> = matching_declarations.to_vec();

        // Can't use an es6 import for a type in JS.
        let is_js = {
            let nodes = self.program.nodes(self.from_file.file_index());
            ast::is_source_file_js(nodes[self.from_file].as_source_file())
        };
        if is_js
            && !export.flags.intersects(ast::SymbolFlags::VALUE)
            && !matching_declarations.iter().all(|i| {
                let nodes = self.program.nodes(self.from_file.file_index());
                nodes[i.node].kind == Kind::JSDocImportTag
            })
        {
            return None;
        }

        let import_kind = get_import_kind(self.from_file, export, &self.program, false);
        if import_kind == lsproto::ImportKind::CommonJS
            || import_kind == lsproto::ImportKind::Namespace
        {
            return None;
        }

        let add_as_type_only =
            get_add_as_type_only(is_valid_type_only_use_site, export, &self.program.options());

        let mut best: Option<Fix> = None;
        for existing_import in &matching_declarations {
            let nodes = self.program.nodes(self.from_file.file_index());
            let node = existing_import.node;
            match nodes[node].kind {
                Kind::ImportEqualsDeclaration => continue,
                Kind::VariableDeclaration => {
                    let name_kind = nodes[node].name().map(|n| nodes[n].kind);
                    if (import_kind == lsproto::ImportKind::Named
                        || import_kind == lsproto::ImportKind::Default)
                        && name_kind == Some(Kind::ObjectBindingPattern)
                    {
                        let fix = Fix {
                            auto_import_fix: lsproto::AutoImportFix {
                                kind: lsproto::AutoImportFixKind::AddToExisting,
                                name: export.name().to_string(),
                                import_kind,
                                import_index: existing_import.index as i32,
                                module_specifier: existing_import.module_specifier.clone(),
                                add_as_type_only,
                                ..Default::default()
                            },
                            ..Default::default()
                        };
                        // Variable declarations are never type-only.
                        // Give preference to putting types in existing type-only
                        // imports and avoiding conversions of import statements
                        // to/from type-only.
                        if add_as_type_only == lsproto::AddAsTypeOnly::NotAllowed {
                            return Some(fix);
                        }
                        if best.is_none() {
                            best = Some(fix);
                        }
                    }
                    continue;
                }
                _ => {}
            }

            let Some(import_clause_node) = nodes[node].import_clause() else {
                continue;
            };
            let module_specifier_node = nodes[node].module_specifier();
            if module_specifier_node.is_none_or(|ms| !ast::is_string_literal_like(&nodes[ms])) {
                // Side-effect import (no import clause) - can't add to it
                continue;
            }
            let import_clause = nodes[import_clause_node].as_import_clause();
            if import_clause.phase_modifier == Kind::SourceKeyword {
                continue;
            }

            let named_bindings = import_clause.named_bindings;
            let import_clause_is_type_only = nodes[import_clause_node].is_type_only();
            // A type-only import may not have both a default and named imports, so
            // the only way a name can be added to an existing type-only import is
            // adding a named import to existing named bindings.
            if import_clause_is_type_only
                && !(import_kind == lsproto::ImportKind::Named && named_bindings.is_some())
            {
                continue;
            }

            if import_kind == lsproto::ImportKind::Default
                && (nodes[import_clause_node].name().is_some()
                    // Cannot add a default import as type-only if the import
                    // already has named bindings
                    || add_as_type_only == lsproto::AddAsTypeOnly::Required
                        && named_bindings.is_some())
            {
                continue;
            }

            // Cannot add a named import to a declaration that has a namespace import
            if import_kind == lsproto::ImportKind::Named
                && named_bindings.is_some_and(|nb| nodes[nb].kind == Kind::NamespaceImport)
            {
                continue;
            }

            let fix = Fix {
                auto_import_fix: lsproto::AutoImportFix {
                    kind: lsproto::AutoImportFixKind::AddToExisting,
                    name: export.name().to_string(),
                    import_kind,
                    import_index: existing_import.index as i32,
                    module_specifier: existing_import.module_specifier.clone(),
                    add_as_type_only,
                    ..Default::default()
                },
                ..Default::default()
            };

            // Give preference to putting types in existing type-only imports and
            // avoiding conversions of import statements to/from type-only.
            if (add_as_type_only != lsproto::AddAsTypeOnly::NotAllowed
                && import_clause_is_type_only)
                || (add_as_type_only == lsproto::AddAsTypeOnly::NotAllowed
                    && !import_clause_is_type_only)
            {
                return Some(fix);
            }
            if best.is_none() {
                best = Some(fix);
            }
        }

        best
    }

    /// `View.getExistingImports`.
    fn get_existing_imports(&self) -> Ref<'_, MultiMap<ModuleID, ExistingImport>> {
        if self.existing_imports.borrow().is_none() {
            let mut result: MultiMap<ModuleID, ExistingImport> = {
                let nodes = self.program.nodes(self.from_file.file_index());
                MultiMap::with_size_hint(nodes[self.from_file].as_source_file().imports().len())
            };

            let imports: Vec<NodeId> = {
                let nodes = self.program.nodes(self.from_file.file_index());
                nodes[self.from_file].as_source_file().imports().to_vec()
            };
            for (i, module_specifier) in imports.iter().copied().enumerate() {
                let node = {
                    let nodes = self.program.nodes(self.from_file.file_index());
                    let node = ast::try_get_import_from_module_specifier(module_specifier, &nodes)
                        .unwrap_or_else(|| {
                            panic!(
                                "error: did not expect node kind {}",
                                nodes[module_specifier].kind_string()
                            )
                        });
                    let parent_is_require = nodes[node].parent.is_some_and(|p| {
                        ast::is_variable_declaration_initialized_to_require(p, &nodes)
                    });
                    (node, parent_is_require)
                };
                if node.1 {
                    if let Some(module_symbol) = self
                        .type_checker
                        .borrow_mut()
                        .resolve_external_module_name_api(module_specifier, None)
                        && let Some((module_id, _)) =
                            crate::autoimport::util::try_get_module_id_and_file_name_of_module_symbol(
                                module_symbol,
                                &self.type_checker,
                            )
                    {
                        let nodes = self.program.nodes(self.from_file.file_index());
                        result.add(
                            module_id,
                            ExistingImport {
                                node: nodes[node.0].parent.unwrap(),
                                module_specifier: nodes[module_specifier].text(&nodes).into_owned(),
                                index: i,
                            },
                        );
                    }
                } else {
                    let is_import_like = {
                        let nodes = self.program.nodes(self.from_file.file_index());
                        matches!(
                            nodes[node.0].kind,
                            Kind::ImportDeclaration
                                | Kind::ImportEqualsDeclaration
                                | Kind::JSDocImportTag
                        )
                    };
                    if is_import_like
                        && let Some(module_symbol) = self
                            .type_checker
                            .borrow_mut()
                            .get_symbol_at_location_api(module_specifier)
                        && let Some((module_id, _)) =
                            crate::autoimport::util::try_get_module_id_and_file_name_of_module_symbol(
                                module_symbol,
                                &self.type_checker,
                            )
                    {
                        let nodes = self.program.nodes(self.from_file.file_index());
                        result.add(
                            module_id,
                            ExistingImport {
                                node: node.0,
                                module_specifier: nodes[module_specifier].text(&nodes).into_owned(),
                                index: i,
                            },
                        );
                    }
                }
            }
            *self.existing_imports.borrow_mut() = Some(result);
        }
        Ref::map(self.existing_imports.borrow(), |o| {
            o.as_ref().expect("existing imports")
        })
    }

    /// `View.shouldUseRequire`.
    pub(crate) fn should_use_require(&self) -> bool {
        if let Some(v) = self.should_use_require_for_fixes.get() {
            return v;
        }
        let should_use_require = self.compute_should_use_require();
        self.should_use_require_for_fixes
            .set(Some(should_use_require));
        should_use_require
    }

    /// `View.computeShouldUseRequire`.
    fn compute_should_use_require(&self) -> bool {
        let nodes = self.program.nodes(self.from_file.file_index());
        let source_file = nodes[self.from_file].as_source_file();

        // 1. TypeScript files don't use require variable declarations
        if !source_file.file_name().has_js_file_extension() {
            return false;
        }

        // 2. If the current source file is unambiguously CJS or ESM, go with that
        match detect_syntax(
            nodes[self.from_file].as_source_file(),
            &self.program.options(),
            &nodes,
        ) {
            FileSyntaxKind::Cjs => return true,
            FileSyntaxKind::Esm => return false,
            _ => {}
        }

        // 3. Use the implied node format to determine CJS vs ESM
        //    TODO: consider removing `impliedNodeFormatForEmit`
        match self
            .program
            .get_implied_node_format_for_emit(nodes[self.from_file].as_source_file())
        {
            ModuleKind::CommonJS => return true,
            ModuleKind::ESNext => return false,
            _ => {}
        }

        // 4. If there's a tsconfig/jsconfig, use its module setting
        if !self.program.options().config_file_path.is_empty() {
            return self.program.options().get_emit_module_kind() < ModuleKind::ES2015;
        }

        // 5. Match the first other JS file in the program that's unambiguously
        //    CJS or ESM
        for other_file in self.program.source_files() {
            if other_file == self.from_file {
                continue;
            }
            let other_nodes = self.program.nodes(other_file.file_index());
            let other_sf = other_nodes[other_file].as_source_file();
            if !ast::is_source_file_js(other_sf)
                || self
                    .program
                    .is_source_file_from_external_library(other_file)
            {
                continue;
            }
            match detect_syntax(other_sf, &self.program.options(), &other_nodes) {
                FileSyntaxKind::Cjs => return true,
                FileSyntaxKind::Esm => return false,
                _ => {}
            }
        }

        // 6. Literally nothing to go on
        true
    }

    /// `View.CompareFixesForSorting` — returns negative if `a` is better than
    /// `b`. Sorting with this comparator will place the best fix first. After
    /// rank sorting, fixes will be sorted by arbitrary but stable criteria to
    /// ensure a deterministic order.
    pub fn compare_fixes_for_sorting(&self, a: &Fix, b: &Fix) -> i32 {
        let res = self.compare_fixes_for_ranking(a, b);
        if res != 0 {
            return res;
        }
        self.compare_module_specifiers_for_sorting(a, b)
    }

    /// `View.CompareFixesForRanking` — returns negative if `a` is better than
    /// `b`. Sorting with this comparator will place the best fix first. Fixes
    /// of equal desirability will be considered equal.
    pub fn compare_fixes_for_ranking(&self, a: &Fix, b: &Fix) -> i32 {
        let res = compare_fix_kinds(a.auto_import_fix.kind, b.auto_import_fix.kind);
        if res != 0 {
            return res;
        }
        self.compare_module_specifiers_for_ranking(a, b)
    }

    /// `View.compareModuleSpecifiersForRanking`.
    fn compare_module_specifiers_for_ranking(&self, a: &Fix, b: &Fix) -> i32 {
        let comparison = compare_module_specifier_relativity(a, b, &self.user_preferences);
        if comparison != 0 {
            return comparison;
        }
        if a.module_specifier_kind == ResultKind::Ambient
            && b.module_specifier_kind == ResultKind::Ambient
        {
            let comparison = self.compare_node_core_module_specifiers(
                &a.auto_import_fix.module_specifier,
                &b.auto_import_fix.module_specifier,
            );
            if comparison != 0 {
                return comparison;
            }
        }
        if a.module_specifier_kind == ResultKind::Relative
            && b.module_specifier_kind == ResultKind::Relative
        {
            let importing_file_name = {
                let nodes = self.program.nodes(self.from_file.file_index());
                nodes[self.from_file].as_source_file().file_name().clone()
            };
            let comparison = tsc_core::core::compare_booleans(
                is_fix_possibly_re_exporting_importing_file(
                    a,
                    &importing_file_name,
                    self.program.case_sensitivity(),
                ),
                is_fix_possibly_re_exporting_importing_file(
                    b,
                    &importing_file_name,
                    self.program.case_sensitivity(),
                ),
            );
            if comparison != 0 {
                return comparison;
            }
        }
        tspath::compare_number_of_directory_separators(
            &a.auto_import_fix.module_specifier,
            &b.auto_import_fix.module_specifier,
        )
    }

    /// `View.compareModuleSpecifiersForSorting`.
    fn compare_module_specifiers_for_sorting(&self, a: &Fix, b: &Fix) -> i32 {
        let res = self.compare_module_specifiers_for_ranking(a, b);
        if res != 0 {
            return res;
        }
        // Sort ./foo before ../foo for equal-length specifiers
        let a_relative = a.auto_import_fix.module_specifier.starts_with("./");
        let b_relative = b.auto_import_fix.module_specifier.starts_with("./");
        if a_relative && !b_relative {
            return -1;
        }
        if b_relative && !a_relative {
            return 1;
        }
        if let comparison @ (std::cmp::Ordering::Less | std::cmp::Ordering::Greater) = a
            .auto_import_fix
            .module_specifier
            .cmp(&b.auto_import_fix.module_specifier)
        {
            return comparison as i32;
        }
        a.auto_import_fix
            .import_kind
            .cmp(&b.auto_import_fix.import_kind) as i32
        // !!! further tie-breakers? In practice this is only called on fixes
        // with the same name
    }

    /// `View.compareNodeCoreModuleSpecifiers`.
    fn compare_node_core_module_specifiers(&self, a: &str, b: &str) -> i32 {
        if a.starts_with("node:") && !b.starts_with("node:") {
            if self.should_use_uri_style_node_core_modules.is_true() {
                return -1;
            } else if self.should_use_uri_style_node_core_modules.is_false() {
                return 1;
            }
            return 0;
        }
        if b.starts_with("node:") && !a.starts_with("node:") {
            if self.should_use_uri_style_node_core_modules.is_true() {
                return 1;
            } else if self.should_use_uri_style_node_core_modules.is_false() {
                return -1;
            }
        }
        0
    }
}

/// `getAddAsTypeOnly` determines if an import should be type-only based on
/// usage context.
fn get_add_as_type_only(
    is_valid_type_only_use_site: bool,
    export: &Export,
    compiler_options: &CompilerOptions,
) -> lsproto::AddAsTypeOnly {
    if !is_valid_type_only_use_site {
        // Can't use a type-only import if the usage is an emitting position
        return lsproto::AddAsTypeOnly::NotAllowed;
    }
    if compiler_options.verbatim_module_syntax.is_true()
        && (export.is_type_only || !export.flags.intersects(ast::SymbolFlags::VALUE))
        || export.is_type_only && export.flags.intersects(ast::SymbolFlags::VALUE)
    {
        // A type-only import is required for this symbol if under
        // verbatimModuleSyntax and it's purely a type
        return lsproto::AddAsTypeOnly::Required;
    }
    lsproto::AddAsTypeOnly::Allowed
}

/// `getNamespaceLikeImportText`.
fn get_namespace_like_import_text(nodes: &[Node], declaration: NodeId) -> String {
    match nodes[declaration].kind {
        Kind::VariableDeclaration => {
            let name = nodes[declaration].name();
            match name {
                Some(n) if nodes[n].kind == Kind::Identifier => nodes[n].text(nodes).into_owned(),
                _ => String::new(),
            }
        }
        Kind::ImportEqualsDeclaration => nodes[declaration]
            .name()
            .map(|n| nodes[n].text(nodes).into_owned())
            .unwrap_or_default(),
        Kind::JSDocImportTag | Kind::ImportDeclaration => {
            match nodes[declaration].import_clause() {
                Some(import_clause) => {
                    let named_bindings = nodes[import_clause].as_import_clause().named_bindings;
                    match named_bindings {
                        Some(nb) if nodes[nb].kind == Kind::NamespaceImport => nodes[nb]
                            .name()
                            .map(|n| nodes[n].text(nodes).into_owned())
                            .unwrap_or_default(),
                        _ => String::new(),
                    }
                }
                None => String::new(),
            }
        }
        _ => String::new(),
    }
}

/// `GetImportKindForImportStatement`.
pub fn get_import_kind_for_import_statement(
    importing_file: NodeId,
    export: &Export,
    program: &Program,
) -> lsproto::ImportKind {
    get_import_kind(
        importing_file,
        export,
        program,
        true, /*forceImportKeyword*/
    )
}

/// `getImportKind`.
fn get_import_kind(
    importing_file: NodeId,
    export: &Export,
    program: &Program,
    force_import_keyword: bool,
) -> lsproto::ImportKind {
    let importing_file_module_kind = {
        let nodes = program.nodes(importing_file.file_index());
        program.get_emit_module_format_of_file(nodes[importing_file].as_source_file())
    };
    if program.options().verbatim_module_syntax.is_true()
        && importing_file_module_kind == ModuleKind::CommonJS
    {
        return lsproto::ImportKind::CommonJS;
    }
    match export.syntax {
        ExportSyntax::DefaultModifier | ExportSyntax::DefaultDeclaration => {
            lsproto::ImportKind::Default
        }
        ExportSyntax::Named
            if export.export_id.export_name == tsc_ast::INTERNAL_SYMBOL_NAME_DEFAULT =>
        {
            lsproto::ImportKind::Default
        }
        ExportSyntax::Named
        | ExportSyntax::Modifier
        | ExportSyntax::Star
        | ExportSyntax::CommonJSExportsProperty => lsproto::ImportKind::Named,
        ExportSyntax::Equals | ExportSyntax::CommonJSModuleExports | ExportSyntax::Umd => {
            // `export.syntax` will be `ExportSyntax::Equals` for named
            // exports/properties of an export='s target.
            if export.export_id.export_name != tsc_ast::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS {
                return lsproto::ImportKind::Named;
            }
            // !!! cache this?
            let statements: Vec<NodeId> = {
                let nodes = program.nodes(importing_file.file_index());
                nodes[importing_file]
                    .as_source_file()
                    .statements
                    .as_ref()
                    .map(|s| s.nodes.to_vec())
                    .unwrap_or_default()
            };
            let nodes = program.nodes(importing_file.file_index());
            for statement in &statements {
                // `import foo` parses as an ImportEqualsDeclaration even though
                // it could be an ImportDeclaration
                if tsc_ast::is_import_equals_declaration(&nodes[*statement])
                    && !tsc_ast::node_is_missing(
                        nodes[*statement]
                            .as_import_equals_declaration()
                            .module_reference,
                        &nodes,
                    )
                {
                    return lsproto::ImportKind::CommonJS;
                }
            }
            // !!! this logic feels weird; we're basically trying to predict if
            //     shouldUseRequire is going to be true. The meaning of "default
            //     import" is different depending on whether we write it as a
            //     require or an es6 import. The latter, compiled to CJS, has
            //     interop built in that will avoid accessing .default, but if we
            //     write a require directly and call it a default import, we emit
            //     an unconditional .default access.
            let external_module_indicator = {
                nodes[importing_file]
                    .as_source_file()
                    .external_module_indicator
                    .is_some()
            };
            if external_module_indicator
                || force_import_keyword
                || !tsc_ast::is_source_file_js(nodes[importing_file].as_source_file())
            {
                return lsproto::ImportKind::Default;
            }
            lsproto::ImportKind::CommonJS
        }
        ExportSyntax::None => panic!("unhandled export syntax kind: {:?}", export.syntax),
    }
}

/// `type fileSyntaxKind int` — the detected module syntax of a source file.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FileSyntaxKind {
    /// `fileSyntaxKindAmbiguous`.
    Ambiguous,
    /// `fileSyntaxKindESM`.
    Esm,
    /// `fileSyntaxKindCJS`.
    Cjs,
}

/// `detectSyntax` returns whether a source file has unambiguous ESM or CJS
/// syntax. When moduleDetection is "force", ExternalModuleIndicator may be
/// set to the source file node itself rather than a genuine syntax indicator,
/// so we fall back to inspecting the file's `imports()` to find actual
/// import/export declarations.
fn detect_syntax(
    file: &ast::SourceFile,
    options: &CompilerOptions,
    nodes: &[Node],
) -> FileSyntaxKind {
    let (has_esm, has_cjs) = detect_syntax_indicators(file, options, nodes);
    match (has_esm, has_cjs) {
        (false, true) => FileSyntaxKind::Cjs,
        (true, false) => FileSyntaxKind::Esm,
        _ => FileSyntaxKind::Ambiguous,
    }
}

/// `detectSyntaxIndicators` checks whether a source file contains genuine ESM
/// and/or CJS syntax. Under moduleDetection "force", the cached
/// ExternalModuleIndicator may be the source file itself rather than a real
/// statement, so we look at `imports()` for actual import/export
/// declarations.
fn detect_syntax_indicators(
    file: &ast::SourceFile,
    options: &CompilerOptions,
    nodes: &[Node],
) -> (bool, bool) {
    let has_cjs = file.common_js_module_indicator.is_some();
    if options.get_emit_module_detection_kind() != ModuleDetectionKind::Force {
        // ExternalModuleIndicator is reliable when moduleDetection is not "force"
        return (file.external_module_indicator.is_some(), has_cjs);
    }
    // Under moduleDetection "force", ExternalModuleIndicator is set to
    // file.AsNode() when there is no genuine ESM syntax, so only trust it
    // when it points to a real statement node.
    if let Some(indicator) = file.external_module_indicator
        && indicator != NodeId::NONE
        && nodes[indicator].kind != Kind::SourceFile
    {
        return (true, has_cjs);
    }
    // Fall back to scanning `imports()` for actual import/export
    // declarations (not require() calls or dynamic imports).
    for &imp in file.imports() {
        if nodes[imp].flags.intersects(ast::NodeFlags::SYNTHESIZED) {
            continue;
        }
        let Some(parent) = nodes[imp].parent else {
            continue;
        };
        match nodes[parent].kind {
            Kind::ImportDeclaration | Kind::JSImportDeclaration | Kind::ExportDeclaration => {
                return (true, has_cjs);
            }
            // import x = require("...") — this is ESM-ish syntax
            Kind::ExternalModuleReference => return (true, has_cjs),
            _ => {}
        }
    }
    (false, has_cjs)
}

/// `needsTypeOnly`.
fn needs_type_only(add_as_type_only: lsproto::AddAsTypeOnly) -> bool {
    add_as_type_only == lsproto::AddAsTypeOnly::Required
}

/// `shouldUseTypeOnly`.
pub(crate) fn should_use_type_only(
    add_as_type_only: lsproto::AddAsTypeOnly,
    preferences: &UserPreferences,
) -> bool {
    needs_type_only(add_as_type_only)
        || add_as_type_only != lsproto::AddAsTypeOnly::NotAllowed
            && preferences.prefer_type_only_auto_imports.is_true()
}

/// `compareFixKinds`.
fn compare_fix_kinds(a: lsproto::AutoImportFixKind, b: lsproto::AutoImportFixKind) -> i32 {
    a.0 - b.0
}

/// `isFixPossiblyReExportingImportingFile` — a simple heuristic to try to
/// avoid creating an import cycle with a barrel re-export. E.g., do not
/// `import { Foo } from ".."` when you could `import { Foo } from "../Foo"`.
/// This can produce false positives or negatives if re-exports cross into
/// sibling directories (e.g. `export * from "../whatever"`) or are not named
/// "index". Technically this should do a `tspath.PathKey` comparison, but
/// it's not worth it to run a heuristic in such a hot path.
fn is_fix_possibly_re_exporting_importing_file(
    fix: &Fix,
    importing_file_name: &RootedFilePath,
    case_sensitivity: tspath::CaseSensitivity,
) -> bool {
    if fix.is_re_export && is_index_file_name(&fix.module_file_name) {
        return tspath::starts_with_directory(
            importing_file_name.as_string(),
            fix.module_file_name.directory().as_string(),
            case_sensitivity,
        );
    }
    false
}

/// `isIndexFileName`.
fn is_index_file_name(file_name: &RootedFilePath) -> bool {
    matches!(
        file_name.base_name(),
        "index.js" | "index.jsx" | "index.d.ts" | "index.ts" | "index.tsx"
    )
}

/// `promoteFromTypeOnly`.
fn promote_from_type_only(
    changes: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    alias_declaration: NodeId,
    compiler_options: &CompilerOptions,
    source_file: NodeId,
    preferences: &UserPreferences,
) -> NodeId {
    // See comment in `doAddExistingFix` on constant with the same name.
    let convert_existing_to_type_only = compiler_options.verbatim_module_syntax;

    match nodes.snapshot()[alias_declaration].kind {
        Kind::ImportSpecifier => {
            let (spec_is_type_only, spec_parent, spec_property_name, spec_name) = {
                let n = nodes.snapshot();
                let spec = n[alias_declaration].as_import_specifier();
                (
                    spec.is_type_only,
                    n[alias_declaration].parent,
                    spec.property_name,
                    spec.name,
                )
            };
            if spec_is_type_only {
                if let Some(parent) = spec_parent
                    && nodes.snapshot()[parent].kind == Kind::NamedImports
                {
                    let elements: Vec<NodeId> = {
                        nodes.snapshot()[parent]
                            .elements()
                            .map(|e| e.to_vec())
                            .unwrap_or_default()
                    };
                    if elements.len() > 1 {
                        // Create a synthetic specifier with isTypeOnly=false to
                        // compute sorted position
                        let (new_specifier, import_decl) = {
                            let mut n = nodes.cow();
                            let property_name = spec_property_name.map(|pn| {
                                let text = n[pn].text(&n).into_owned();
                                changes
                                    .node_factory(source_file)
                                    .new_identifier(&mut n, &text)
                            });
                            let name_text = spec_name
                                .map(|nm| n[nm].text(&n).into_owned())
                                .unwrap_or_default();
                            let name = changes
                                .node_factory(source_file)
                                .new_identifier(&mut n, &name_text);
                            let specifier = changes.node_factory(source_file).new_import_specifier(
                                &mut n,
                                false, // isTypeOnly = false
                                property_name,
                                Some(name),
                            );
                            let import_decl = n[parent].parent.and_then(|p| n[p].parent);
                            (specifier, import_decl)
                        };
                        let (specifier_comparer, _) = {
                            let n = nodes.snapshot();
                            lsutil::get_named_import_specifier_comparer_with_detection(
                                &n,
                                import_decl.expect("ImportDeclaration"),
                                Some(source_file),
                                preferences,
                            )
                        };
                        let insertion_index = {
                            let n = nodes.snapshot();
                            lsutil::get_import_specifier_insertion_index(
                                &n,
                                &elements,
                                new_specifier,
                                &*specifier_comparer,
                            )
                        };
                        let current_index = elements
                            .iter()
                            .position(|&e| e == alias_declaration)
                            .unwrap_or(usize::MAX);
                        if insertion_index != current_index {
                            changes.delete(nodes, source_file, alias_declaration);
                            changes.insert_import_specifier_at_index(
                                nodes,
                                source_file,
                                new_specifier,
                                parent,
                                insertion_index,
                            );
                            return alias_declaration;
                        }
                    }
                }
                // If no re-sorting needed, just remove the 'type' keyword
                let first_token = {
                    let mut n = nodes.cow();
                    lsutil::get_first_token(&mut n, alias_declaration, source_file)
                        .expect("import specifier should have a first token")
                };
                let type_keyword_pos = {
                    let n = nodes.snapshot();
                    scanner::get_token_pos_of_node(
                        first_token,
                        n[source_file].as_source_file(),
                        false,
                        &n,
                    )
                };
                let target_node = spec_property_name.or(spec_name).expect("specifier name");
                let target_pos = {
                    let n = nodes.snapshot();
                    scanner::get_token_pos_of_node(
                        target_node,
                        n[source_file].as_source_file(),
                        false,
                        &n,
                    )
                };
                changes.delete_range(
                    nodes,
                    source_file,
                    TextRange::new(type_keyword_pos, target_pos),
                );
            } else {
                // The parent import clause is type-only
                let (named_imports, import_clause) = {
                    let n = nodes.snapshot();
                    let named_imports = n[alias_declaration]
                        .parent
                        .filter(|&p| n[p].kind == Kind::NamedImports)
                        .expect("ImportSpecifier parent must be NamedImports");
                    let import_clause = n[named_imports]
                        .parent
                        .filter(|&p| n[p].kind == Kind::ImportClause)
                        .expect("NamedImports parent must be ImportClause");
                    (named_imports, import_clause)
                };
                let _ = named_imports;
                promote_import_clause(
                    changes,
                    nodes,
                    import_clause,
                    compiler_options,
                    source_file,
                    preferences,
                    convert_existing_to_type_only,
                    Some(alias_declaration),
                );
                return import_clause;
            }
            alias_declaration
        }
        Kind::ImportClause => {
            promote_import_clause(
                changes,
                nodes,
                alias_declaration,
                compiler_options,
                source_file,
                preferences,
                convert_existing_to_type_only,
                Some(alias_declaration),
            );
            alias_declaration
        }
        Kind::NamespaceImport => {
            // Promote the parent import clause
            let import_clause = {
                let n = nodes.snapshot();
                n[alias_declaration]
                    .parent
                    .filter(|&p| n[p].kind == Kind::ImportClause)
                    .expect("NamespaceImport parent must be ImportClause")
            };
            promote_import_clause(
                changes,
                nodes,
                import_clause,
                compiler_options,
                source_file,
                preferences,
                convert_existing_to_type_only,
                Some(alias_declaration),
            );
            import_clause
        }
        Kind::ImportEqualsDeclaration => {
            // Remove the 'type' keyword (which is the second token:
            // 'import' 'type' name '=' ...)
            let token_start = {
                let n = nodes.snapshot();
                let pos = n[alias_declaration].pos();
                let mut scan = scanner::get_scanner_for_source_file(
                    n[source_file].as_source_file(),
                    pos as usize,
                );
                // Skip 'import' keyword to get to 'type'
                scan.scan();
                scan.token_start()
            };
            delete_type_keyword(changes, nodes, source_file, token_start as i32);
            alias_declaration
        }
        k => panic!("Unexpected alias declaration kind: {:?}", k),
    }
}

/// `promoteImportClause` removes the type keyword from an import clause.
fn promote_import_clause(
    changes: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    import_clause: NodeId,
    compiler_options: &CompilerOptions,
    source_file: NodeId,
    preferences: &UserPreferences,
    convert_existing_to_type_only: Tristate,
    alias_declaration: Option<NodeId>,
) {
    // Delete the 'type' keyword
    if nodes.snapshot()[import_clause]
        .as_import_clause()
        .phase_modifier
        == Kind::TypeKeyword
    {
        let pos = nodes.snapshot()[import_clause].pos();
        delete_type_keyword(changes, nodes, source_file, pos);
    }

    // Handle .ts extension conversion to .js if necessary
    if compiler_options.allow_importing_ts_extensions.is_false() {
        let _module_specifier = {
            let n = nodes.snapshot();
            let parent = n[import_clause].parent;
            parent.and_then(|p| {
                tsc_checker::nodebuilderimpl::try_get_module_specifier_from_declaration(p, &n)
            })
        };
        // Note: We can't check ResolvedUsingTsExtension without program, so
        // we'll skip this optimization. The fix will still work, just might
        // not change .ts to .js extensions in all cases.
    }

    // Handle verbatimModuleSyntax conversion
    // If convertExistingToTypeOnly is true, we need to add 'type' to other
    // specifiers in the same import declaration
    if convert_existing_to_type_only.is_true() {
        let named_bindings = nodes.snapshot()[import_clause]
            .as_import_clause()
            .named_bindings;
        if let Some(named_imports) = named_bindings
            && nodes.snapshot()[named_imports].kind == Kind::NamedImports
        {
            let elements: Vec<NodeId> = nodes.snapshot()[named_imports]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default();
            if elements.len() > 1 {
                // Check if the list is sorted and if we need to reorder
                let import_decl = nodes.snapshot()[import_clause].parent;
                let (_, is_sorted) = {
                    let n = nodes.snapshot();
                    lsutil::get_named_import_specifier_comparer_with_detection(
                        &n,
                        import_decl.expect("import clause parent"),
                        Some(source_file),
                        preferences,
                    )
                };

                // If the alias declaration is an ImportSpecifier and the list is
                // sorted, move it to index 0 (since it will be the only
                // non-type-only import)
                if !is_sorted.is_false()
                    && let Some(alias) = alias_declaration
                    && nodes.snapshot()[alias].kind == Kind::ImportSpecifier
                {
                    // Find the index of the alias declaration
                    let alias_index = elements.iter().position(|&e| e == alias);
                    // If not already at index 0, move it there
                    if let Some(alias_index) = alias_index
                        && alias_index > 0
                    {
                        // Delete the specifier from its current position
                        changes.delete(nodes, source_file, alias);
                        // Insert it at index 0
                        changes.insert_import_specifier_at_index(
                            nodes,
                            source_file,
                            alias,
                            named_imports,
                            0,
                        );
                    }
                }

                // Add 'type' keyword to all other import specifiers that aren't
                // already type-only
                for &element in &elements {
                    // Skip the specifier being promoted (if aliasDeclaration is
                    // an ImportSpecifier)
                    if let Some(alias) = alias_declaration
                        && nodes.snapshot()[alias].kind == Kind::ImportSpecifier
                        && element == alias
                    {
                        continue;
                    }
                    // Skip if already type-only
                    if !nodes.snapshot()[element].as_import_specifier().is_type_only {
                        changes.insert_modifier_before(
                            nodes,
                            source_file,
                            Kind::TypeKeyword,
                            element,
                        );
                    }
                }
            }
        }
    }
}

/// `deleteTypeKeyword` deletes the 'type' keyword token starting at the given
/// position, including any trailing whitespace.
fn delete_type_keyword(
    changes: &mut Tracker<'_, '_>,
    nodes: &Rc<ArenaCell>,
    source_file: NodeId,
    start_pos: i32,
) {
    let (type_start, mut type_end) = {
        let n = nodes.snapshot();
        let mut scan = scanner::get_scanner_for_source_file(
            n[source_file].as_source_file(),
            start_pos as usize,
        );
        if scan.token() != Kind::TypeKeyword {
            return;
        }
        (scan.token_start(), scan.token_end())
    };
    // Skip trailing whitespace
    let text = {
        let n = nodes.snapshot();
        n[source_file].as_source_file().text().to_string()
    };
    let bytes = text.as_bytes();
    while type_end < bytes.len() && (bytes[type_end] == b' ' || bytes[type_end] == b'\t') {
        type_end += 1;
    }
    changes.delete_range(
        nodes,
        source_file,
        TextRange::new(type_start as i32, type_end as i32),
    );
}

/// `getModuleSpecifierText`.
fn get_module_specifier_text(nodes: &[Node], promoted_declaration: NodeId) -> String {
    if nodes[promoted_declaration].kind == Kind::ImportEqualsDeclaration {
        let module_reference = nodes[promoted_declaration]
            .as_import_equals_declaration()
            .module_reference;
        if let Some(mr) = module_reference
            && ast::is_external_module_reference(&nodes[mr])
        {
            if let Some(expr) = nodes[mr].as_external_module_reference().expression {
                if ast::is_string_literal_like(&nodes[expr]) {
                    return nodes[expr].text(nodes).into_owned();
                }
                return tsc_scanner::utilities::get_text_of_node(expr, nodes);
            }
        }
        return module_reference
            .map(|mr| tsc_scanner::utilities::get_text_of_node(mr, nodes))
            .unwrap_or_default();
    }
    let module_specifier = nodes[promoted_declaration]
        .parent
        .and_then(|p| nodes[p].module_specifier());
    match module_specifier {
        Some(ms) if ast::is_string_literal_like(&nodes[ms]) => nodes[ms].text(nodes).into_owned(),
        Some(ms) => tsc_scanner::utilities::get_text_of_node(ms, nodes),
        None => String::new(),
    }
}

/// `compareModuleSpecifierRelativity` — returns `-1` if `a` is better than `b`.
fn compare_module_specifier_relativity(a: &Fix, b: &Fix, preferences: &UserPreferences) -> i32 {
    match preferences.import_module_specifier_preference {
        modulespecifiers::ImportModuleSpecifierPreference::NON_RELATIVE
        | modulespecifiers::ImportModuleSpecifierPreference::PROJECT_RELATIVE => {
            tsc_core::core::compare_booleans(
                a.module_specifier_kind == ResultKind::Relative,
                b.module_specifier_kind == ResultKind::Relative,
            )
        }
        _ => 0,
    }
}
