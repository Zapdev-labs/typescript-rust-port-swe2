// Ported from tsc/internal/ls/codeactions_fixclassincorrectlyimplementsinterface.go
// @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` → `NodeId`; `*checker.Checker` → `Rc<RefCell<Checker>>`;
//   `*checker.Type` → `TypeId`; `*ast.Symbol` → `SymbolId`;
//   `ast.SymbolTable` → `FxHashMap<String, SymbolId>`;
//   `collections.Set[*ast.Node]` → `HashSet<NodeId>`.
// - `importAdder` is `Option<&mut dyn ImportAdder>`; `ImportAdderImpl`
//   borrows the auto-import `View`, so the `createImportAdder` helper is
//   inlined at each call site (the `Rc<View>` must live in the caller).
// - `getPreparedAutoImportView` returns `Err(ERR_NEEDS_AUTO_IMPORTS)`
//   instead of Go's `(nil, nil)`, so `?` keeps parity — a `None` adder is
//   only reachable if the view plumbing changes upstream.
// - `insertMemberAtStart`/`insertNodeAfter` take the arena handle
//   (`program.nodes_handle`); member nodes are minted by the fixer's
//   factory into the same arena.
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::LazyLock;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, ModifierFlags, NodeId, SymbolId};
use tsc_astnav as astnav;
use tsc_checker::checker_core::Checker;
use tsc_checker::types::TypeId;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_diagnostics as diagnostics;
use tsc_lsproto as lsproto;
use tsc_scanner as scanner;

use crate::api::Error;
use crate::autoimport::import_adder::{ImportAdder, new_import_adder};
use crate::change::tracker::{Tracker, new_tracker};
use crate::codeactions::{
    CodeAction, CodeFixContext, CodeFixProvider, CombinedCodeActions, get_all_diagnostics,
    is_fixable_diagnostic, short_converters,
};
use crate::codeactions_missingmemberfixer::{
    MissingMemberFixer, PRESERVE_OPTIONAL_FLAGS_ALL,
};

/// `fixClassIncorrectlyImplementsInterfaceFixID`.
const FIX_CLASS_INCORRECTLY_IMPLEMENTS_INTERFACE_FIX_ID: &str =
    "fixClassIncorrectlyImplementsInterface";

/// `fixClassIncorrectlyImplementsInterfaceErrorCodes`.
fn fix_class_incorrectly_implements_interface_error_codes() -> &'static [i32] {
    static CODES: LazyLock<Vec<i32>> = LazyLock::new(|| {
        vec![
            diagnostics::Class_0_incorrectly_implements_interface_1.code(),
            diagnostics::Class_0_incorrectly_implements_class_1_Did_you_mean_to_extend_1_and_inherit_its_members_as_a_subclass.code(),
        ]
    });
    &CODES
}

/// `FixClassIncorrectlyImplementsInterfaceProvider`.
pub static FIX_CLASS_INCORRECTLY_IMPLEMENTS_INTERFACE_PROVIDER: LazyLock<CodeFixProvider> =
    LazyLock::new(|| CodeFixProvider {
        error_codes: fix_class_incorrectly_implements_interface_error_codes(),
        get_code_actions:
            get_code_actions_to_fix_class_incorrectly_implements_interface,
        fix_ids: &[FIX_CLASS_INCORRECTLY_IMPLEMENTS_INTERFACE_FIX_ID],
        get_all_code_actions: Some(
            get_all_code_actions_to_fix_class_incorrectly_implements_interface,
        ),
    });

fn get_code_actions_to_fix_class_incorrectly_implements_interface(
    ctx: &Context,
    fix_context: &CodeFixContext<'_, '_>,
) -> Result<Vec<CodeAction>, Error> {
    let Some(class_declaration) = get_class(fix_context) else {
        return Ok(Vec::new());
    };

    let implements_types = {
        let nodes = fix_context
            .program
            .nodes(fix_context.source_file.file_index());
        ast::get_implements_heritage_clause_elements(&nodes[class_declaration], &nodes)
            .map(|s| s.to_vec())
            .unwrap_or_default()
    };
    let locale = tsc_locale::from_context(ctx);

    let (ch, done) = fix_context
        .program
        .get_type_checker_for_file(ctx.clone(), fix_context.source_file);

    let mut actions: Vec<CodeAction> = Vec::new();
    for implemented_type_node in implements_types {
        let mut change_tracker = new_tracker(
            ctx.clone(),
            &fix_context.program.options(),
            fix_context.ls.format_options(),
            &fix_context.ls.converters,
        );
        // `createImportAdder` inlined — the adder borrows `view`.
        let view = fix_context
            .ls
            .get_prepared_auto_import_view(fix_context.source_file, &ch)?;
        // PORT: `new_import_adder` takes `&'a Converters<'a>` where the
        // inner `'a` equals the borrow lifetime; a plain local
        // `Converters<'a>` can never satisfy that because its `Box<dyn Fn>`
        // destructor would need `'a` to outlive the value's own drop.
        // `ManuallyDrop` suppresses the destructor (and the dropck
        // requirement) — the tiny `Converters` allocation is simply
        // abandoned at scope end, which is semantically fine here.
        let converters = std::mem::ManuallyDrop::new(short_converters(fix_context.ls));
        let mut import_adder = new_import_adder(
            ctx.clone(),
            fix_context.program,
            &ch,
            fix_context.source_file,
            &view,
            fix_context.ls.format_options(),
            &converters,
            fix_context.ls.user_preferences(),
        );

        add_changes(
            ctx,
            fix_context,
            &mut change_tracker,
            Some(&mut import_adder),
            &ch,
            class_declaration,
            implemented_type_node,
        );
        let changes = get_changes(
            &mut change_tracker,
            Some(&mut import_adder),
            fix_context.source_file,
            fix_context.program,
        );
        if changes.is_empty() {
            continue;
        }

        let implemented_text = {
            let nodes = fix_context
                .program
                .nodes(fix_context.source_file.file_index());
            scanner::utilities::get_text_of_node(implemented_type_node, &nodes)
        };
        actions.push(CodeAction {
            description: diagnostics::Implement_interface_0
                .localize(&locale, &[implemented_text]),
            changes,
            fix_id: FIX_CLASS_INCORRECTLY_IMPLEMENTS_INTERFACE_FIX_ID,
            fix_all_description: diagnostics::Implement_all_unimplemented_interfaces
                .localize(&locale, &[""; 0]),
        });
    }
    done();
    Ok(actions)
}

fn get_all_code_actions_to_fix_class_incorrectly_implements_interface(
    ctx: &Context,
    fix_context: &CodeFixContext<'_, '_>,
) -> Result<Option<CombinedCodeActions>, Error> {
    let all_diags = get_all_diagnostics(ctx, fix_context.program, fix_context.source_file);

    let (ch, done) = fix_context
        .program
        .get_type_checker_for_file(ctx.clone(), fix_context.source_file);

    let mut change_tracker = new_tracker(
        ctx.clone(),
        &fix_context.program.options(),
        fix_context.ls.format_options(),
        &fix_context.ls.converters,
    );
    let view = fix_context
        .ls
        .get_prepared_auto_import_view(fix_context.source_file, &ch)?;
    // PORT: `ManuallyDrop` — see the note at the first call site.
    let converters = std::mem::ManuallyDrop::new(short_converters(fix_context.ls));
    let mut import_adder = new_import_adder(
        ctx.clone(),
        fix_context.program,
        &ch,
        fix_context.source_file,
        &view,
        fix_context.ls.format_options(),
        &converters,
        fix_context.ls.user_preferences(),
    );

    let mut seen_class_declarations: HashSet<NodeId> = HashSet::new();

    for diag in &all_diags {
        if is_fixable_diagnostic(
            diag,
            fix_class_incorrectly_implements_interface_error_codes(),
        ) {
            let loc = tsc_ast::diagnostic::lock_diagnostic(diag).loc();
            let span = TextRange::new(loc.pos(), loc.end());
            let class_declaration = {
                let token = {
                    let mut m = fix_context
                        .program
                        .nodes_mut(fix_context.source_file.file_index());
                    astnav::tokens::get_token_at_position(&mut m, fix_context.source_file, span.pos())
                };
                token.and_then(|t| {
                    let nodes = fix_context
                        .program
                        .nodes(fix_context.source_file.file_index());
                    ast::get_containing_class(t, &nodes)
                })
            };
            let Some(class_declaration) = class_declaration else {
                continue;
            };
            if seen_class_declarations.insert(class_declaration) {
                let implements_types = {
                    let nodes = fix_context
                        .program
                        .nodes(fix_context.source_file.file_index());
                    ast::get_implements_heritage_clause_elements(
                        &nodes[class_declaration],
                        &nodes,
                    )
                    .map(|s| s.to_vec())
                    .unwrap_or_default()
                };
                for implemented_type_node in implements_types {
                    add_changes(
                        ctx,
                        fix_context,
                        &mut change_tracker,
                        Some(&mut import_adder),
                        &ch,
                        class_declaration,
                        implemented_type_node,
                    );
                }
            }
        }
    }

    let changes = get_changes(
        &mut change_tracker,
        Some(&mut import_adder),
        fix_context.source_file,
        fix_context.program,
    );
    if changes.is_empty() {
        done();
        return Ok(None);
    }

    done();
    Ok(Some(CombinedCodeActions {
        description: diagnostics::Implement_all_unimplemented_interfaces
            .localize(&tsc_locale::from_context(ctx), &[""; 0]),
        changes,
    }))
}

/// `addChanges`.
///
/// `'a` is the `MissingMemberFixer`'s borrow lifetime — the `import_adder`'s
/// `&mut` is invariant over the trait-object bound, so every other argument
/// must be provably at least as long-lived as `'a`; the `where` clauses move
/// that obligation to the caller, where all these regions do outlive the
/// adder reborrow.
#[allow(clippy::too_many_arguments)]
fn add_changes<'a, 'b: 'a, 'h>(
    ctx: &Context,
    fix_context: &CodeFixContext<'b, 'h>,
    change_tracker: &'a mut Tracker<'_, '_>,
    import_adder: Option<&'a mut dyn ImportAdder>,
    type_checker: &'a Rc<RefCell<Checker>>,
    class_declaration: NodeId,
    implemented_type_node: NodeId,
) {
    let mut missing_member_fixer = MissingMemberFixer {
        change_tracker,
        checker: type_checker,
        program: fix_context.program,
        preferences: fix_context.ls.user_preferences(),
        import_adder,
        locale: tsc_locale::from_context(ctx),
    };
    let constructor = get_constructor(class_declaration, fix_context.program);
    let implemented_type = type_checker
        .borrow_mut()
        .get_type_at_location(implemented_type_node);
    let class_type = type_checker
        .borrow_mut()
        .get_type_at_location(class_declaration);

    if type_checker
        .borrow_mut()
        .get_number_index_type(class_type)
        .is_none()
    {
        let key_type = type_checker.borrow_mut().get_number_type();
        if let Some(member) = missing_member_fixer
            .create_index_signature_declaration_from_type(
                class_declaration,
                implemented_type,
                key_type,
            )
        {
            insert_interface_member_node(
                missing_member_fixer.change_tracker,
                fix_context.program,
                fix_context.source_file,
                class_declaration,
                constructor,
                member,
            );
        }
    }

    if type_checker
        .borrow_mut()
        .get_string_index_type(class_type)
        .is_none()
    {
        let key_type = type_checker.borrow_mut().get_string_type();
        if let Some(member) = missing_member_fixer
            .create_index_signature_declaration_from_type(
                class_declaration,
                implemented_type,
                key_type,
            )
        {
            insert_interface_member_node(
                missing_member_fixer.change_tracker,
                fix_context.program,
                fix_context.source_file,
                class_declaration,
                constructor,
                member,
            );
        }
    }

    let missing_members = get_missing_members(
        type_checker,
        class_declaration,
        &[implemented_type],
        fix_context.program,
    );
    for member in missing_members {
        let member_nodes = missing_member_fixer.create_member_from_symbol(
            member,
            class_declaration,
            fix_context.source_file,
            None, /* body */
            PRESERVE_OPTIONAL_FLAGS_ALL,
            false, /* abstract */
        );
        for member_node in member_nodes {
            insert_interface_member_node(
                missing_member_fixer.change_tracker,
                fix_context.program,
                fix_context.source_file,
                class_declaration,
                constructor,
                member_node,
            );
        }
    }
}

/// `getChanges`.
fn get_changes(
    change_tracker: &mut Tracker<'_, '_>,
    import_adder: Option<&mut dyn ImportAdder>,
    source_file: NodeId,
    program: &Rc<Program>,
) -> Vec<lsproto::TextEdit> {
    let (changes, unmappable) = change_tracker.get_changes();
    if !unmappable.is_empty() {
        return Vec::new();
    }
    let file_name = {
        let nodes = program.nodes(source_file.file_index());
        nodes[source_file]
            .as_source_file()
            .original_file_name(&nodes)
            .clone()
    };
    let mut file_changes = changes.get(&file_name).cloned().unwrap_or_default();
    if let Some(adder) = import_adder {
        if adder.has_fixes() {
            file_changes.extend(adder.edits());
        }
    }
    file_changes
}

/// `insertInterfaceMemberNode`.
fn insert_interface_member_node(
    change_tracker: &mut Tracker<'_, '_>,
    program: &Rc<Program>,
    source_file: NodeId,
    class_declaration: NodeId,
    constructor: Option<NodeId>,
    member: NodeId,
) {
    let nodes = program.nodes_handle(source_file.file_index());
    match constructor {
        None => {
            change_tracker.insert_member_at_start(&nodes, source_file, class_declaration, member)
        }
        Some(ctor) => {
            change_tracker.insert_node_after(&nodes, source_file, ctor, member)
        }
    }
}

/// `getClass`.
fn get_class(fix_context: &CodeFixContext<'_, '_>) -> Option<NodeId> {
    let token = {
        let mut m = fix_context
            .program
            .nodes_mut(fix_context.source_file.file_index());
        astnav::tokens::get_token_at_position(&mut m, fix_context.source_file, fix_context.span.pos())
    }?;
    let nodes = fix_context
        .program
        .nodes(fix_context.source_file.file_index());
    ast::get_containing_class(token, &nodes)
}

/// `getConstructor`.
fn get_constructor(class_declaration: NodeId, program: &Rc<Program>) -> Option<NodeId> {
    let nodes = program.nodes(class_declaration.file_index());
    let members = nodes[class_declaration].member_list()?;
    members.nodes().iter().copied().find(|&m| {
        !m.is_none() && ast::is_constructor_declaration(&nodes[m])
    })
}

/// `getMissingMembers`.
fn get_missing_members(
    type_checker: &Rc<RefCell<Checker>>,
    class_declaration: NodeId,
    implemented_types: &[TypeId],
    program: &Rc<Program>,
) -> Vec<SymbolId> {
    let inherited_members = get_inherited_members(type_checker, class_declaration, program);
    let mut seen_members: HashMap<String, SymbolId> = HashMap::new();

    let class_members: Option<FxHashMap<String, SymbolId>> = {
        let nodes = program.nodes(class_declaration.file_index());
        nodes[class_declaration].symbol().map(|s| {
            let members = &program.symbols.borrow()[s.index()].members;
            members.entries().map(|(k, &v)| (k.to_string(), v)).collect()
        })
    };

    let mut missing_members: Vec<SymbolId> = Vec::new();
    for &implemented_type in implemented_types {
        for symbol in type_checker
            .borrow_mut()
            .get_properties_of_type(implemented_type)
        {
            if symbol.is_none() {
                continue;
            }
            let name = program.symbols.borrow()[symbol.index()].name.clone();
            if let Some(members) = &class_members {
                if members.contains_key(&name) {
                    continue;
                }
            }
            if inherited_members.contains_key(&name) || seen_members.contains_key(&name) {
                continue;
            }
            let flags = tsc_checker::utilities::get_declaration_modifier_flags_from_symbol(
                &type_checker.borrow(),
                symbol,
            );
            if !flags.intersects(ModifierFlags::PRIVATE) {
                seen_members.insert(name, symbol);
                missing_members.push(symbol);
            }
        }
    }
    missing_members
}

/// `getInheritedMembers`.
fn get_inherited_members(
    type_checker: &Rc<RefCell<Checker>>,
    class_declaration: NodeId,
    program: &Rc<Program>,
) -> FxHashMap<String, SymbolId> {
    let mut inherited_members: FxHashMap<String, SymbolId> = FxHashMap::default();
    let type_node = {
        let nodes = program.nodes(class_declaration.file_index());
        ast::get_class_extends_heritage_element(&nodes[class_declaration], &nodes)
    };
    let Some(type_node) = type_node else {
        return inherited_members;
    };

    let base_type = type_checker.borrow_mut().get_type_at_location(type_node);
    if base_type.is_none() {
        return inherited_members;
    }

    for symbol in type_checker.borrow_mut().get_properties_of_type(base_type) {
        if symbol.is_none() {
            continue;
        }
        let flags = tsc_checker::utilities::get_declaration_modifier_flags_from_symbol(
            &type_checker.borrow(),
            symbol,
        );
        if !flags.intersects(ModifierFlags::PRIVATE) {
            let name = program.symbols.borrow()[symbol.index()].name.clone();
            inherited_members.insert(name, symbol);
        }
    }
    inherited_members
}
