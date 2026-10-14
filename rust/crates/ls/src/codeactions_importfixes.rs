// Ported from tsc/internal/ls/codeactions_importfixes.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` → `NodeId`; `*checker.Checker` → `Rc<RefCell<Checker>>`;
//   `*ast.Symbol` → `SymbolId`; `*autoimport.Fix` → `autoimport::Fix`.
// - Go's `[]*fixInfo` → `Vec<FixInfo>` (sorting a copy, not in place).
// - `fixContext.Diagnostic` is `Option<&lsproto::Diagnostic>`; the fix-all
//   path constructs a `CodeFixContext` with `diagnostic: None` like Go's
//   struct literal that leaves the field nil.
// - `slices.SortFunc` → `sort_unstable_by`.
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::LazyLock;

use tsc_ast::diagnostic::lock_diagnostic;
use tsc_ast::{self as ast, NodeId, SymbolId};
use tsc_astnav as astnav;
use tsc_checker::checker_core::Checker;
use tsc_core::context::Context;
use tsc_core::core::compare_booleans;
use tsc_core::options_generated::JsxEmit;
use tsc_core::text::{TextPos, TextRange};
use tsc_diagnostics as diagnostics;
use tsc_lsconv::converters::source_file_script;
use tsc_lsproto as lsproto;
use tsc_scanner as scanner;

use crate::api::Error;
use crate::autoimport::export::symbol_to_export;
use crate::autoimport::fix::Fix;
use crate::autoimport::import_adder::{ImportAdder, new_import_adder};
use crate::autoimport::view::{QueryKind, View};
use crate::codeactions::{
    CodeAction, CodeFixContext, CodeFixProvider, CombinedCodeActions,
    is_fixable_diagnostic, short_converters,
};

/// `importFixErrorCodes`.
fn import_fix_error_codes() -> &'static [i32] {
    static CODES: LazyLock<Vec<i32>> = LazyLock::new(|| {
        vec![
            diagnostics::Cannot_find_name_0.code(),
            diagnostics::Cannot_find_name_0_Did_you_mean_1.code(),
            diagnostics::Cannot_find_name_0_Did_you_mean_the_instance_member_this_0.code(),
            diagnostics::Cannot_find_name_0_Did_you_mean_the_static_member_1_0.code(),
            diagnostics::Cannot_find_namespace_0.code(),
            diagnostics::X_0_refers_to_a_UMD_global_but_the_current_file_is_a_module_Consider_adding_an_import_instead.code(),
            diagnostics::X_0_only_refers_to_a_type_but_is_being_used_as_a_value_here.code(),
            diagnostics::No_value_exists_in_scope_for_the_shorthand_property_0_Either_declare_one_or_provide_an_initializer.code(),
            diagnostics::X_0_cannot_be_used_as_a_value_because_it_was_imported_using_import_type.code(),
            diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_jQuery_Try_npm_i_save_dev_types_Slashjquery.code(),
            diagnostics::Cannot_find_name_0_Do_you_need_to_change_your_target_library_Try_changing_the_lib_compiler_option_to_1_or_later.code(),
            diagnostics::Cannot_find_name_0_Do_you_need_to_change_your_target_library_Try_changing_the_lib_compiler_option_to_include_dom.code(),
            diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_a_test_runner_Try_npm_i_save_dev_types_Slashjest_or_npm_i_save_dev_types_Slashmocha_and_then_add_jest_or_mocha_to_the_types_field_in_your_tsconfig.code(),
            diagnostics::Cannot_find_name_0_Did_you_mean_to_write_this_in_an_async_function.code(),
            diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_jQuery_Try_npm_i_save_dev_types_Slashjquery_and_then_add_jquery_to_the_types_field_in_your_tsconfig.code(),
            diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_a_test_runner_Try_npm_i_save_dev_types_Slashjest_or_npm_i_save_dev_types_Slashmocha.code(),
            diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_node_Try_npm_i_save_dev_types_Slashnode.code(),
            diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_node_Try_npm_i_save_dev_types_Slashnode_and_then_add_node_to_the_types_field_in_your_tsconfig.code(),
            diagnostics::Cannot_find_namespace_0_Did_you_mean_1.code(),
            diagnostics::Cannot_extend_an_interface_0_Did_you_mean_implements.code(),
            diagnostics::This_JSX_tag_requires_0_to_be_in_scope_but_it_could_not_be_found.code(),
        ]
    });
    &CODES
}

/// `importFixID`.
const IMPORT_FIX_ID: &str = "fixMissingImport";

/// `ImportFixProvider` is the CodeFixProvider for import-related fixes.
pub static IMPORT_FIX_PROVIDER: LazyLock<CodeFixProvider> =
    LazyLock::new(|| CodeFixProvider {
        error_codes: import_fix_error_codes(),
        get_code_actions: get_import_code_actions,
        fix_ids: &[IMPORT_FIX_ID],
        get_all_code_actions: Some(get_all_import_code_actions),
    });

/// `type fixInfo struct`.
struct FixInfo {
    /// `fix`.
    fix: Fix,
    /// `symbolName`.
    symbol_name: String,
    /// `errorIdentifierText`.
    #[allow(dead_code)]
    error_identifier_text: String,
    /// `isJsxNamespaceFix`.
    is_jsx_namespace_fix: bool,
}

fn get_import_code_actions(
    ctx: &Context,
    fix_context: &CodeFixContext<'_, '_>,
) -> Result<Vec<CodeAction>, Error> {
    let (ch, done) = fix_context.program.get_type_checker(ctx.clone());

    let info = get_fix_infos(
        &ch,
        fix_context,
        fix_context.error_code,
        fix_context.span.pos(),
    )?;
    if info.is_empty() {
        done();
        return Ok(Vec::new());
    }

    let mut actions: Vec<CodeAction> = Vec::new();
    for fix_info in info {
        let nodes_handle = fix_context
            .program
            .nodes_handle(fix_context.source_file.file_index());
        let (edits, description, ok) = fix_info.fix.edits(
            ctx,
            &nodes_handle,
            fix_context.source_file,
            &fix_context.program.options(),
            fix_context.ls.format_options(),
            &fix_context.ls.converters,
            fix_context.ls.user_preferences(),
        );

        if ok {
            actions.push(CodeAction {
                description,
                changes: edits,
                fix_id: IMPORT_FIX_ID,
                fix_all_description: diagnostics::Add_all_missing_imports
                    .localize(&tsc_locale::from_context(ctx), &[""; 0]),
            });
        }
    }
    done();
    Ok(actions)
}

fn get_all_import_code_actions(
    ctx: &Context,
    fix_context: &CodeFixContext<'_, '_>,
) -> Result<Option<CombinedCodeActions>, Error> {
    {
        let nodes = fix_context
            .program
            .nodes(fix_context.source_file.file_index());
        if nodes[fix_context.source_file]
            .as_source_file()
            .file_name()
            .is_dynamic()
        {
            return Ok(None);
        }
    }

    let all_diagnostics = fix_context
        .program
        .get_semantic_diagnostics(ctx.clone(), Some(fix_context.source_file));

    let mut import_diags: Vec<&tsc_ast::diagnostic::DiagnosticRef> = Vec::new();
    for diag in &all_diagnostics {
        if is_fixable_diagnostic(diag, import_fix_error_codes()) {
            import_diags.push(diag);
        }
    }

    if import_diags.is_empty() {
        return Ok(None);
    }

    let (ch, done) = fix_context.program.get_type_checker(ctx.clone());

    let view = fix_context
        .ls
        .get_prepared_auto_import_view(fix_context.source_file, &ch);
    let view = match view {
        Ok(view) => view,
        Err(e) => {
            done();
            return Err(e);
        }
    };
    // Go: `if view == nil { view = getCurrentAutoImportView(...) }` — the
    // Rust view getter returns `Result<Rc<View>, Error>` where `Ok` is
    // always a live view, so no nil fallback is needed here.

    // PORT: `new_import_adder` takes `&'a Converters<'a>` where the inner
    // `'a` equals the borrow lifetime; a plain local `Converters<'a>` can
    // never satisfy that because its `Box<dyn Fn>` destructor would need
    // `'a` to outlive the value's own drop. `ManuallyDrop` suppresses the
    // destructor (and the dropck requirement); `short_converters` (see
    // `codeactions.rs`) produces the `Converters<'a>` the adder needs.
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

    for &diag in &import_diags {
        if let Err(e) =
            add_import_from_diagnostic(&ch, &mut import_adder, diag, fix_context)
        {
            done();
            return Err(e);
        }
    }

    if !import_adder.has_fixes() {
        done();
        return Ok(None);
    }

    let result = CombinedCodeActions {
        description: diagnostics::Add_all_missing_imports
            .localize(&tsc_locale::from_context(ctx), &[""; 0]),
        changes: import_adder.edits(),
    };
    done();
    Ok(Some(result))
}

/// `addImportFromDiagnostic` finds the best import fix for a diagnostic and
/// adds it to the adder.
fn add_import_from_diagnostic(
    ch: &Rc<RefCell<Checker>>,
    import_adder: &mut impl ImportAdder,
    diag: &tsc_ast::diagnostic::DiagnosticRef,
    fix_context: &CodeFixContext<'_, '_>,
) -> Result<(), Error> {
    let (pos, end, code) = {
        let d = lock_diagnostic(diag);
        let loc = d.loc();
        (loc.pos(), loc.end(), d.code())
    };
    let diag_fix_context = CodeFixContext {
        source_file: fix_context.source_file,
        span: TextRange::new(pos, end),
        error_code: code,
        program: fix_context.program,
        ls: fix_context.ls,
        diagnostic: None,
        params: None,
    };

    let infos = get_fix_infos(ch, &diag_fix_context, code, pos)?;
    if let Some(first) = infos.into_iter().next() {
        import_adder.add_import_fix(first.fix);
    }
    Ok(())
}

fn get_fix_infos(
    ch: &Rc<RefCell<Checker>>,
    fix_context: &CodeFixContext<'_, '_>,
    error_code: i32,
    pos: TextPos,
) -> Result<Vec<FixInfo>, Error> {
    let program = fix_context.program;
    let source_file = fix_context.source_file;
    let file_index = source_file.file_index();

    // Can't compute import fixes for dynamic/untitled files since they don't
    // have real file paths
    {
        let nodes = program.nodes(file_index);
        if nodes[source_file]
            .as_source_file()
            .file_name()
            .is_dynamic()
        {
            return Ok(Vec::new());
        }
    }

    let symbol_token = {
        let mut m = program.nodes_mut(file_index);
        astnav::tokens::get_token_at_position(&mut m, source_file, pos)
    };

    let umd_code = diagnostics::X_0_refers_to_a_UMD_global_but_the_current_file_is_a_module_Consider_adding_an_import_instead.code();
    let type_only_code = diagnostics::X_0_cannot_be_used_as_a_value_because_it_was_imported_using_import_type.code();

    if error_code != umd_code
        && !symbol_token.is_some_and(|t| {
            let nodes = program.nodes(file_index);
            ast::is_identifier(&nodes[t])
        })
    {
        return Ok(Vec::new());
    }

    let mut view: Option<Rc<View>> = None;
    let mut info: Vec<FixInfo>;

    if error_code == umd_code {
        let v = fix_context
            .ls
            .get_current_auto_import_view(source_file, ch);
        info = match symbol_token {
            Some(token) => get_fixes_info_for_umd_import(token, &v, ch, program),
            None => Vec::new(),
        };
        view = Some(v);
    } else if error_code == type_only_code {
        let compiler_options = fix_context.program.options();
        let Some(symbol_token) = symbol_token else {
            return Ok(Vec::new());
        };
        let symbol_names =
            get_symbol_names_to_import(source_file, ch, symbol_token, &compiler_options, program);

        let mut all_type_only_fixes: Vec<FixInfo> = Vec::new();
        let token_text = {
            let nodes = program.nodes(file_index);
            nodes[symbol_token].text(&nodes).into_owned()
        };
        for sn in &symbol_names {
            if !sn.is_type_only {
                continue;
            }
            if let Some(fix) = get_type_only_promotion_fix(
                source_file,
                symbol_token,
                &sn.name,
                ch,
                program,
            ) {
                all_type_only_fixes.push(FixInfo {
                    fix,
                    symbol_name: sn.name.clone(),
                    error_identifier_text: token_text.clone(),
                    is_jsx_namespace_fix: false,
                });
            }
        }

        // For JSX opening tags, there can be separate type-only errors for both
        // the tag name identifier and the JSX namespace identifier. When both
        // produce valid fixes, we disambiguate using the diagnostic message,
        // which quotes the symbol name in single quotes (e.g., "'React' cannot
        // be used as a value..."). If filtering yields nothing (e.g., due to
        // localization), fall back to returning all candidates.
        let diagnostic_message = fix_context
            .diagnostic
            .map(|d| d.message.as_string().to_string())
            .unwrap_or_default();
        info = Vec::new();
        if all_type_only_fixes.len() > 1 && !diagnostic_message.is_empty() {
            for fi in all_type_only_fixes.iter() {
                // `filter` by quoted symbol name — collect matching fixes.
                if diagnostic_message.contains(&format!("'{}'", fi.symbol_name)) {
                    info.push(FixInfo {
                        fix: fi.fix.clone(),
                        symbol_name: fi.symbol_name.clone(),
                        error_identifier_text: fi.error_identifier_text.clone(),
                        is_jsx_namespace_fix: fi.is_jsx_namespace_fix,
                    });
                }
            }
        }
        if info.is_empty() {
            info = all_type_only_fixes;
        }
        return Ok(info);
    } else {
        let Some(symbol_token) = symbol_token else {
            return Ok(Vec::new());
        };
        match fix_context
            .ls
            .get_prepared_auto_import_view(source_file, ch)
        {
            Ok(v) => {
                info = get_fixes_info_for_non_umd_import(
                    fix_context,
                    symbol_token,
                    &v,
                    ch,
                );
                view = Some(v);
            }
            Err(e) => return Err(e),
        }
    }

    // Sort fixes by preference
    if view.is_none() {
        view = Some(
            fix_context
                .ls
                .get_current_auto_import_view(source_file, ch),
        );
    }
    Ok(sort_fix_info(info, fix_context, view.as_ref().unwrap()))
}

fn get_fixes_info_for_umd_import(
    token: NodeId,
    view: &Rc<View>,
    ch: &Rc<RefCell<Checker>>,
    program: &Rc<tsc_compiler::program::Program>,
) -> Vec<FixInfo> {
    let Some(umd_symbol) = get_umd_symbol(token, ch, program) else {
        return Vec::new();
    };

    let Some(export) = symbol_to_export(umd_symbol, ch) else {
        return Vec::new();
    };
    let is_valid_type_only_use_site = {
        let nodes = program.nodes(token.file_index());
        ast::is_valid_type_only_alias_use_site(token, &nodes)
    };

    let mut result: Vec<FixInfo> = Vec::new();
    let umd_symbol_name = {
        let symbols = program.symbols.borrow();
        symbols[umd_symbol.index()].name.clone()
    };
    let error_identifier_text = {
        let nodes = program.nodes(token.file_index());
        if ast::is_identifier(&nodes[token]) {
            nodes[token].text(&nodes).into_owned()
        } else {
            String::new()
        }
    };
    for fix in view.get_fixes(&export, false, is_valid_type_only_use_site, None) {
        result.push(FixInfo {
            fix,
            symbol_name: umd_symbol_name.to_string(),
            error_identifier_text: error_identifier_text.clone(),
            is_jsx_namespace_fix: false,
        });
    }
    result
}

fn get_umd_symbol(
    token: NodeId,
    ch: &Rc<RefCell<Checker>>,
    program: &Rc<tsc_compiler::program::Program>,
) -> Option<SymbolId> {
    // try the identifier to see if it is the umd symbol
    let mut umd_symbol = SymbolId::NONE;
    {
        let nodes = program.nodes(token.file_index());
        if ast::is_identifier(&nodes[token]) {
            drop(nodes);
            umd_symbol = ch.borrow_mut().get_resolved_symbol(token);
        }
    }
    if is_umd_export_symbol(umd_symbol, program) {
        return Some(umd_symbol);
    }

    // The error wasn't for the symbolAtLocation, it was for the JSX tag
    // itself, which needs access to e.g. `React`.
    let (parent_is_jsx_opening, parent_tag_matches, parent_is_opening_fragment, parent) = {
        let nodes = program.nodes(token.file_index());
        let parent = nodes[token].parent;
        let is_opening = parent.is_some_and(|p| {
            ast::is_jsx_opening_like_element(&nodes[p])
        });
        let tag_matches = parent.is_some_and(|p| {
            nodes[p].tag_name() == Some(token)
        });
        let is_fragment = parent.is_some_and(|p| {
            ast::is_jsx_opening_fragment(&nodes[p])
        });
        (is_opening, tag_matches, is_fragment, parent)
    };

    if (parent_is_jsx_opening && parent_tag_matches) || parent_is_opening_fragment {
        let location = if parent_is_jsx_opening {
            token
        } else {
            parent.unwrap()
        };
        let jsx_namespace = ch.borrow_mut().get_jsx_namespace(parent);
        let parent_symbol = ch.borrow_mut().resolve_name_api(
            &jsx_namespace,
            Some(location),
            ast::SymbolFlags::VALUE,
            false,
        );
        if let Some(parent_symbol) = parent_symbol {
            if is_umd_export_symbol(parent_symbol, program) {
                return Some(parent_symbol);
            }
        }
    }
    None
}

fn is_umd_export_symbol(
    symbol: SymbolId,
    program: &Rc<tsc_compiler::program::Program>,
) -> bool {
    if symbol.is_none() {
        return false;
    }
    let first_decl = {
        let symbols = program.symbols.borrow();
        symbols[symbol.index()].declarations.first().copied()
    };
    let Some(first_decl) = first_decl else {
        return false;
    };
    let nodes = program.nodes(first_decl.file_index());
    ast::is_namespace_export_declaration(&nodes[first_decl])
}

fn get_fixes_info_for_non_umd_import(
    fix_context: &CodeFixContext<'_, '_>,
    symbol_token: NodeId,
    view: &Rc<View>,
    ch: &Rc<RefCell<Checker>>,
) -> Vec<FixInfo> {
    let program = fix_context.program;
    let source_file = fix_context.source_file;
    let file_index = source_file.file_index();
    let compiler_options = fix_context.program.options();

    let is_valid_type_only_use_site = {
        let nodes = program.nodes(file_index);
        ast::is_valid_type_only_alias_use_site(symbol_token, &nodes)
    };
    let symbol_names = get_symbol_names_to_import(
        source_file,
        ch,
        symbol_token,
        &compiler_options,
        program,
    );
    let mut all_info: Vec<FixInfo> = Vec::new();

    // Compute usage position for JSDoc import type fixes
    let (usage_position, fidelity) = {
        let nodes = program.nodes(file_index);
        let pos = scanner::scanner::get_token_pos_of_node(
            symbol_token,
            nodes[source_file].as_source_file(),
            false,
            &nodes,
        );
        let script = source_file_script(source_file, &nodes);
        fix_context
            .ls
            .converters
            .to_lsp_position(&script, pos)
    };
    if !fidelity.is_exact() {
        return Vec::new();
    }

    let symbol_token_text = {
        let nodes = program.nodes(file_index);
        nodes[symbol_token].text(&nodes).into_owned()
    };
    let token_is_jsx_tag_name = {
        let nodes = program.nodes(file_index);
        ast::is_jsx_tag_name(symbol_token, &nodes)
    };

    for sn in &symbol_names {
        // Type-only imports are handled by the promotion code path, not the
        // auto-import path.
        if sn.is_type_only {
            continue;
        }

        let symbol_name = &sn.name;
        // "default" is a keyword and not a legal identifier for the import
        if symbol_name == "default" {
            continue;
        }

        let is_jsx_tag_name =
            *symbol_name == symbol_token_text && token_is_jsx_tag_name;
        let query_kind = if is_jsx_tag_name {
            QueryKind::CaseInsensitiveMatch
        } else {
            QueryKind::ExactMatch
        };

        let exports = view.search(symbol_name, query_kind);
        for export in &exports {
            if is_jsx_tag_name
                && !(export.name() == symbol_name.as_str() || export.is_renameable())
            {
                continue;
            }

            let fixes = view.get_fixes(
                export,
                is_jsx_tag_name,
                is_valid_type_only_use_site,
                Some(usage_position),
            );
            for fix in fixes {
                all_info.push(FixInfo {
                    fix,
                    symbol_name: symbol_name.clone(),
                    error_identifier_text: String::new(),
                    is_jsx_namespace_fix: *symbol_name != symbol_token_text,
                });
            }
        }
    }

    all_info
}

fn get_type_only_promotion_fix(
    source_file: NodeId,
    symbol_token: NodeId,
    symbol_name: &str,
    ch: &Rc<RefCell<Checker>>,
    program: &Rc<tsc_compiler::program::Program>,
) -> Option<Fix> {
    // Get the symbol at the token location
    let symbol = ch.borrow_mut().resolve_name_api(
        symbol_name,
        Some(symbol_token),
        ast::SymbolFlags::VALUE,
        true,
    )?;
    let Some(type_only_alias_declaration) = ch
        .borrow_mut()
        .get_type_only_alias_declaration(symbol)
    else {
        return None;
    };
    let decl_source_file = {
        let nodes = program.nodes(type_only_alias_declaration.file_index());
        ast::get_source_file_of_node(
            Some(type_only_alias_declaration),
            &nodes,
        )
    };
    if decl_source_file != Some(source_file) {
        return None;
    }

    Some(Fix {
        auto_import_fix: lsproto::AutoImportFix {
            kind: lsproto::AutoImportFixKind::PromoteTypeOnly,
            ..Default::default()
        },
        type_only_alias_declaration: Some(type_only_alias_declaration),
        ..Default::default()
    })
}

/// `type symbolNameInfo struct`.
struct SymbolNameInfo {
    /// `name`.
    name: String,
    /// `isTypeOnly` — whether the symbol currently resolves to a type-only
    /// import.
    is_type_only: bool,
}

fn get_symbol_names_to_import(
    source_file: NodeId,
    ch: &Rc<RefCell<Checker>>,
    symbol_token: NodeId,
    compiler_options: &tsc_core::options_generated::CompilerOptions,
    program: &Rc<tsc_compiler::program::Program>,
) -> Vec<SymbolNameInfo> {
    let file_index = source_file.file_index();
    let token_text = {
        let nodes = program.nodes(file_index);
        nodes[symbol_token].text(&nodes).into_owned()
    };
    let (is_jsx_tag, parent_is_closing, tag_matches) = {
        let nodes = program.nodes(file_index);
        let parent = nodes[symbol_token].parent;
        let is_jsx = parent.is_some_and(|p| {
            ast::is_jsx_opening_like_element(&nodes[p])
        });
        let is_closing = parent.is_some_and(|p| {
            ast::is_jsx_closing_element(&nodes[p])
        });
        let tag_matches = parent.is_some_and(|p| {
            nodes[p].tag_name() == Some(symbol_token)
        });
        (is_jsx, is_closing, tag_matches)
    };
    if (is_jsx_tag || parent_is_closing)
        && tag_matches
        && jsx_mode_needs_explicit_import(compiler_options.jsx)
    {
        let jsx_namespace = ch.borrow_mut().get_jsx_namespace(Some(source_file));
        if needs_jsx_namespace_fix(&jsx_namespace, symbol_token, ch, program) {
            let mut result: Vec<SymbolNameInfo> = Vec::new();
            if !scanner::utilities::is_intrinsic_jsx_name(&token_text) {
                let comp_symbol = ch.borrow_mut().resolve_name_api(
                    &token_text,
                    Some(symbol_token),
                    ast::SymbolFlags::VALUE,
                    false,
                );
                match comp_symbol {
                    None => {
                        result.push(SymbolNameInfo {
                            name: token_text.clone(),
                            is_type_only: false,
                        });
                    }
                    Some(sym)
                        if ch
                            .borrow_mut()
                            .get_type_only_alias_declaration(sym)
                            .is_some() =>
                    {
                        result.push(SymbolNameInfo {
                            name: token_text.clone(),
                            is_type_only: true,
                        });
                    }
                    _ => {}
                }
            }
            let mut ns_is_type_only = false;
            if let Some(ns_symbol) = ch.borrow_mut().resolve_name_api(
                &jsx_namespace,
                Some(symbol_token),
                ast::SymbolFlags::VALUE,
                true,
            ) {
                ns_is_type_only = ch
                    .borrow_mut()
                    .get_type_only_alias_declaration(ns_symbol)
                    .is_some();
            }
            result.push(SymbolNameInfo {
                name: jsx_namespace,
                is_type_only: ns_is_type_only,
            });
            return result;
        }
    }
    let mut token_is_type_only = false;
    if let Some(sym) = ch.borrow_mut().resolve_name_api(
        &token_text,
        Some(symbol_token),
        ast::SymbolFlags::VALUE,
        true,
    ) {
        token_is_type_only = ch
            .borrow_mut()
            .get_type_only_alias_declaration(sym)
            .is_some();
    }
    vec![SymbolNameInfo {
        name: token_text,
        is_type_only: token_is_type_only,
    }]
}

fn needs_jsx_namespace_fix(
    jsx_namespace: &str,
    symbol_token: NodeId,
    ch: &Rc<RefCell<Checker>>,
    program: &Rc<tsc_compiler::program::Program>,
) -> bool {
    if {
        let nodes = program.nodes(symbol_token.file_index());
        scanner::utilities::is_intrinsic_jsx_name(nodes[symbol_token].text(&nodes).as_ref())
    } {
        return true;
    }
    let Some(namespace_symbol) = ch.borrow_mut().resolve_name_api(
        jsx_namespace,
        Some(symbol_token),
        ast::SymbolFlags::VALUE,
        true,
    ) else {
        return true;
    };
    let (has_type_only_decl, no_value_flags) = {
        let symbols = program.symbols.borrow();
        let decls = symbols[namespace_symbol.index()].declarations.clone();
        let flags = symbols[namespace_symbol.index()].flags;
        let has_type_only = decls.iter().any(|&d| {
            let nodes = program.nodes(d.file_index());
            ast::is_type_only_import_or_export_declaration(d, &nodes)
        });
        (has_type_only, !flags.intersects(ast::SymbolFlags::VALUE))
    };
    if has_type_only_decl {
        return no_value_flags;
    }
    false
}

fn jsx_mode_needs_explicit_import(jsx: JsxEmit) -> bool {
    matches!(jsx, JsxEmit::React | JsxEmit::ReactNative)
}

fn sort_fix_info(
    fixes: Vec<FixInfo>,
    _fix_context: &CodeFixContext<'_, '_>,
    view: &Rc<View>,
) -> Vec<FixInfo> {
    if fixes.is_empty() {
        return fixes;
    }

    // Go copies before sorting; `fixes` is already owned here.
    let mut sorted = fixes;

    // Sort by:
    // 1. JSX namespace fixes last
    // 2. Fix comparison using view.CompareFixes
    sorted.sort_unstable_by(|a, b| {
        // JSX namespace fixes should come last
        let cmp = compare_booleans(a.is_jsx_namespace_fix, b.is_jsx_namespace_fix);
        if cmp != 0 {
            return cmp.cmp(&0);
        }
        view.compare_fixes_for_sorting(&a.fix, &b.fix).cmp(&0)
    });

    sorted
}
