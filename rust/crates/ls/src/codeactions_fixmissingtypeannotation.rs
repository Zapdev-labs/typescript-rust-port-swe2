// Ported from tsc/internal/ls/codeactions_fixmissingtypeannotation.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` → `NodeId`; `fixedNodes map[*ast.Node]bool` → `HashSet<NodeId>`.
// - `*checker.Checker` → `Rc<RefCell<Checker>>`; `*checker.Type` → `TypeId`;
//   `*ast.Symbol` → `SymbolId`; `*checker.Signature` → `SignatureId`.
// - Go's `f.changeTracker.NodeFactory` is `Tracker::node_factory(file)` here,
//   bound to the file arena. Factory calls run inside short `nodes_mut`
//   (`ArenaMut`) guard scopes minting into the file's arena — writes land
//   in place, visible to every `nodes` snapshot handle. Guards are always
//   dropped before tracker calls so the tracker reads a live arena (its
//   `borrow_nodes` snapshots the cell handle).
// - `Checker::type_to_type_node_ex` consumes the `id_to_symbol` map, so the
//   Go call that shares `idToSymbol` with
//   `autoimport.TryGetAutoImportableReferenceFromTypeNode` is reproduced by
//   `type_to_type_node_ex_with_map` (a local copy of the checker wrapper
//   that also hands the map back).
// - Go's `importAdder` is always nil in this file (the auto-import registry
//   is not consulted), so the `importAdder.Edits()` branch is dead — kept as
//   `None` for parity.
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;
use std::sync::LazyLock;

use rustc_hash::FxHashMap;
use tsc_ast::ast::{ArenaCheckout, Node};
use tsc_ast::{self as ast, Kind, NodeFlags, NodeId, SymbolId, TokenFlags};
use tsc_astnav as astnav;
use tsc_checker::checker_core::Checker;
use tsc_checker::types::{ObjectFlags, TypeFlags, TypeId};
use tsc_nodebuilder as nodebuilder;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::options_generated::NewLineKind;
use tsc_core::text::TextRange;
use tsc_diagnostics as diagnostics;
use tsc_locale::Locale;
use tsc_printer::{
    AutoGenerateOptions, EmitFlags, EmitTextWriter, GeneratedIdentifierFlags, PrintHandlers,
    Printer, PrinterOptions,
};
use tsc_scanner as scanner;

use crate::api::Error;
use crate::autoimport::import_adder::try_get_auto_importable_reference_from_type_node;
use crate::change::tracker::{
    LeadingTriviaOption, NodeOptions, Tracker, new_tracker,
};
use crate::codeactions::{
    CodeAction, CodeFixContext, CodeFixProvider, CombinedCodeActions, get_all_diagnostics,
    is_fixable_diagnostic,
};
/// `isolatedDeclarationsFixErrorCodes`.
fn isolated_declarations_fix_error_codes() -> &'static [i32] {
    static CODES: LazyLock<Vec<i32>> = LazyLock::new(|| {
        vec![
            diagnostics::Function_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations.code(),
            diagnostics::Method_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations.code(),
            diagnostics::At_least_one_accessor_must_have_an_explicit_type_annotation_with_isolatedDeclarations.code(),
            diagnostics::Variable_must_have_an_explicit_type_annotation_with_isolatedDeclarations.code(),
            diagnostics::Parameter_must_have_an_explicit_type_annotation_with_isolatedDeclarations.code(),
            diagnostics::Property_must_have_an_explicit_type_annotation_with_isolatedDeclarations.code(),
            diagnostics::Expression_type_can_t_be_inferred_with_isolatedDeclarations.code(),
            diagnostics::Binding_elements_with_initializers_can_t_be_exported_directly_with_isolatedDeclarations.code(),
            diagnostics::Computed_property_names_on_class_or_object_literals_cannot_be_inferred_with_isolatedDeclarations.code(),
            diagnostics::Computed_properties_must_be_number_or_string_literals_variables_or_dotted_expressions_with_isolatedDeclarations.code(),
            diagnostics::Enum_member_initializers_must_be_computable_without_references_to_external_symbols_with_isolatedDeclarations.code(),
            diagnostics::Extends_clause_can_t_contain_an_expression_with_isolatedDeclarations.code(),
            diagnostics::Objects_that_contain_shorthand_properties_can_t_be_inferred_with_isolatedDeclarations.code(),
            diagnostics::Objects_that_contain_spread_assignments_can_t_be_inferred_with_isolatedDeclarations.code(),
            diagnostics::Arrays_with_spread_elements_can_t_inferred_with_isolatedDeclarations.code(),
            diagnostics::Default_exports_can_t_be_inferred_with_isolatedDeclarations.code(),
            diagnostics::Only_const_arrays_can_be_inferred_with_isolatedDeclarations.code(),
            diagnostics::Assigning_properties_to_functions_without_declaring_them_is_not_supported_with_isolatedDeclarations_Add_an_explicit_declaration_for_the_properties_assigned_to_this_function.code(),
            diagnostics::Declaration_emit_for_this_parameter_requires_implicitly_adding_undefined_to_its_type_This_is_not_supported_with_isolatedDeclarations.code(),
            diagnostics::Type_containing_private_name_0_can_t_be_used_with_isolatedDeclarations.code(),
            diagnostics::Add_satisfies_and_a_type_assertion_to_this_expression_satisfies_T_as_T_to_make_the_type_explicit.code(),
        ]
    });
    &CODES
}

/// `fixMissingTypeAnnotationOnExportsFixID`.
const FIX_MISSING_TYPE_ANNOTATION_ON_EXPORTS_FIX_ID: &str =
    "fixMissingTypeAnnotationOnExports";

/// `IsolatedDeclarationsFixProvider` — the `CodeFixProvider` for
/// isolatedDeclarations-related type annotation fixes.
pub static ISOLATED_DECLARATIONS_FIX_PROVIDER: LazyLock<CodeFixProvider> =
    LazyLock::new(|| CodeFixProvider {
        error_codes: isolated_declarations_fix_error_codes(),
        get_code_actions: get_isolated_declarations_code_actions,
        fix_ids: &[FIX_MISSING_TYPE_ANNOTATION_ON_EXPORTS_FIX_ID],
        get_all_code_actions: Some(get_all_isolated_declarations_code_actions),
    });

/// `canHaveTypeAnnotationKinds` — node kinds that can have type annotations
/// added.
fn can_have_type_annotation(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::GetAccessor
            | Kind::MethodDeclaration
            | Kind::PropertyDeclaration
            | Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::ArrowFunction
            | Kind::VariableDeclaration
            | Kind::Parameter
            | Kind::ExportAssignment
            | Kind::ClassDeclaration
            | Kind::ObjectBindingPattern
            | Kind::ArrayBindingPattern
    )
}

/// `declarationEmitNodeBuilderFlags` — node builder flags used for
/// declaration emit.
fn declaration_emit_node_builder_flags() -> nodebuilder::Flags {
    nodebuilder::Flags::MULTILINE_OBJECT_LITERALS
        | nodebuilder::Flags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL
        | nodebuilder::Flags::USE_TYPE_OF_FUNCTION
        | nodebuilder::Flags::USE_STRUCTURAL_FALLBACK
        | nodebuilder::Flags::ALLOW_EMPTY_TUPLE
        | nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS
        | nodebuilder::Flags::NO_TRUNCATION
}

/// `typePrintMode`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum TypePrintMode {
    Full,
    Relative, // typeof X
    Widened,  // widened literal type
}

fn get_isolated_declarations_code_actions(
    ctx: &Context,
    fix_context: &CodeFixContext<'_, '_>,
) -> Result<Vec<CodeAction>, Error> {
    let (ch, done) = fix_context
        .program
        .get_type_checker_for_file(ctx.clone(), fix_context.source_file);

    let mut fixes: Vec<CodeAction> = Vec::new();

    // Match TS ordering: Full annotation, Relative annotation, Widened annotation,
    // Full inline, Relative inline, Widened inline, Full extract
    let modes = [
        TypePrintMode::Full,
        TypePrintMode::Relative,
        TypePrintMode::Widened,
    ];

    for mode in modes {
        if let Some(action) = try_code_action(ctx, fix_context, &ch, |f| {
            f.type_print_mode = mode;
            f.add_type_annotation(fix_context.span)
        }) {
            fixes.push(action);
        }
    }

    for mode in modes {
        if let Some(action) = try_code_action(ctx, fix_context, &ch, |f| {
            f.type_print_mode = mode;
            f.add_inline_assertion(fix_context.span)
        }) {
            fixes.push(action);
        }
    }

    // extractAsVariable only in Full mode
    if let Some(action) = try_code_action(ctx, fix_context, &ch, |f| {
        f.type_print_mode = TypePrintMode::Full;
        f.extract_as_variable(fix_context.span)
    }) {
        fixes.push(action);
    }

    done();
    Ok(fixes)
}

fn get_all_isolated_declarations_code_actions(
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

    let mut fixer = IsolatedDeclarationsFixer {
        ctx,
        source_file: fix_context.source_file,
        program: fix_context.program,
        nodes: fix_context.program.nodes(fix_context.source_file.file_index()),
        checker: &ch,
        change_tracker: &mut change_tracker,
        locale: tsc_locale::from_context(ctx),
        fixed_nodes: HashSet::new(),
        type_print_mode: TypePrintMode::Full,
        symbols_to_import: Vec::new(),
        mutated_target: false,
    };

    for diag in &all_diags {
        if is_fixable_diagnostic(diag, isolated_declarations_fix_error_codes()) {
            let loc = tsc_ast::diagnostic::lock_diagnostic(diag).loc();
            let span = TextRange::new(loc.pos(), loc.end());
            fixer.add_type_annotation(span);
        }
    }

    let syms = std::mem::take(&mut fixer.symbols_to_import);
    for sym in syms {
        fixer.add_symbol_to_existing_import(sym);
    }
    drop(fixer);

    let (changes, _unmappable) = change_tracker.get_changes();
    done();
    let nodes = fix_context.program.nodes(fix_context.source_file.file_index());
    let file_name = nodes[fix_context.source_file]
        .as_source_file()
        .original_file_name(&nodes)
        .clone();
    let file_changes = changes.get(&file_name).cloned().unwrap_or_default();
    if file_changes.is_empty() {
        return Ok(None);
    }

    Ok(Some(CombinedCodeActions {
        description: diagnostics::Add_all_missing_type_annotations
            .localize(&tsc_locale::from_context(ctx), &[""; 0]),
        changes: file_changes,
    }))
}

fn try_code_action(
    ctx: &Context,
    fix_context: &CodeFixContext<'_, '_>,
    ch: &Rc<RefCell<Checker>>,
    f: impl FnOnce(&mut IsolatedDeclarationsFixer<'_, '_, '_>) -> String,
) -> Option<CodeAction> {
    let mut change_tracker = new_tracker(
        ctx.clone(),
        &fix_context.program.options(),
        fix_context.ls.format_options(),
        &fix_context.ls.converters,
    );

    // PORT: Go's `importAdder` is nil here, so no import edits are ever
    // produced — the `importAdder.Edits()` branch below is dead in Go too.
    let import_adder: Option<()> = None;

    let mut fixer = IsolatedDeclarationsFixer {
        ctx,
        source_file: fix_context.source_file,
        program: fix_context.program,
        nodes: fix_context.program.nodes(fix_context.source_file.file_index()),
        checker: ch,
        change_tracker: &mut change_tracker,
        locale: tsc_locale::from_context(ctx),
        fixed_nodes: HashSet::new(),
        type_print_mode: TypePrintMode::Full,
        symbols_to_import: Vec::new(),
        mutated_target: false,
    };

    let description = f(&mut fixer);
    if description.is_empty() {
        return None;
    }

    // Add any symbols that need to be imported to existing import declarations
    let syms = std::mem::take(&mut fixer.symbols_to_import);
    for sym in syms {
        fixer.add_symbol_to_existing_import(sym);
    }
    drop(fixer);

    let (changes, _unmappable) = change_tracker.get_changes();
    let nodes = fix_context.program.nodes(fix_context.source_file.file_index());
    let file_name = nodes[fix_context.source_file]
        .as_source_file()
        .original_file_name(&nodes)
        .clone();
    let file_changes = changes.get(&file_name).cloned().unwrap_or_default();

    // Add import edits if import adder has fixes — dead while the adder is nil.
    if let Some(_adder) = import_adder {
        // importAdder.Edits()
    }

    if file_changes.is_empty() {
        return None;
    }

    Some(CodeAction {
        description,
        changes: file_changes,
        fix_id: FIX_MISSING_TYPE_ANNOTATION_ON_EXPORTS_FIX_ID,
        fix_all_description: diagnostics::Add_all_missing_type_annotations
            .localize(&tsc_locale::from_context(ctx), &[""; 0]),
    })
}

/// `isolatedDeclarationsFixer` encapsulates the state for fixing isolated
/// declarations errors.
struct IsolatedDeclarationsFixer<'a, 'c, 'h> {
    ctx: &'a Context,
    source_file: NodeId,
    program: &'a Rc<Program>,
    /// Held arena handle — aliases the shared buffer, so `nodes_mut`/
    /// `borrow_nodes` writes and incidental `program.nodes()` reads all
    /// observe the live arena (Go shared-heap semantics).
    #[allow(dead_code)]
    nodes: Rc<ast::NodeArenaBuf>,
    checker: &'a Rc<RefCell<Checker>>,
    change_tracker: &'a mut Tracker<'c, 'h>,
    locale: Locale,
    fixed_nodes: HashSet<NodeId>,
    type_print_mode: TypePrintMode,
    symbols_to_import: Vec<SymbolId>,
    /// Set by `infer_type`/`relative_type` when the target was mutated
    /// (e.g., spread decomposition).
    mutated_target: bool,
}

impl<'a, 'c, 'h> IsolatedDeclarationsFixer<'a, 'c, 'h> {
    /// Runs `f` with a mutable arena guard and the tracker's factory bound
    /// to this file, then flushes the guard so subsequent tracker calls see
    /// the minted nodes.
    fn with_factory<R>(
        &mut self,
        f: impl FnOnce(&mut Vec<Node>, &mut tsc_printer::NodeFactory) -> R,
    ) -> R {
        let mut m = self.program.nodes_mut(self.source_file.file_index());
        let r = {
            let factory = self.change_tracker.node_factory(self.source_file);
            f(&mut m, factory)
        };
        drop(m);
        r
    }

    /// `addTypeAnnotation`.
    fn add_type_annotation(&mut self, span: TextRange) -> String {
        let node_with_diag = {
            let mut m = self.program.nodes_mut(self.source_file.file_index());
            astnav::tokens::get_token_at_position(&mut m, self.source_file, span.pos())
        };

        let Some(node_with_diag) = node_with_diag else {
            return String::new();
        };

        let expando_function = find_expando_function(self.checker, self.program, node_with_diag);
        if let Some(expando_function) = expando_function {
            let nodes = self.program.nodes(self.source_file.file_index());
            if ast::is_function_declaration(&nodes[expando_function]) {
                drop(nodes);
                return self.create_namespace_for_expando_properties(expando_function);
            }
            drop(nodes);
            return self.fix_isolated_declaration_error(expando_function);
        }

        let nodes = self.program.nodes(self.source_file.file_index());
        let node_missing_type =
            find_ancestor_with_missing_type(&nodes, Some(node_with_diag));
        drop(nodes);
        if let Some(node_missing_type) = node_missing_type {
            return self.fix_isolated_declaration_error(node_missing_type);
        }
        String::new()
    }

    /// `createNamespaceForExpandoProperties`.
    fn create_namespace_for_expando_properties(&mut self, expando_func: NodeId) -> String {
        let nodes = self.program.nodes(self.source_file.file_index());
        let func_name = nodes[expando_func].name();
        let Some(func_name) = func_name else {
            return String::new();
        };
        let func_name_text = nodes[func_name].text(&nodes).into_owned();

        let t = self
            .checker
            .borrow_mut()
            .get_type_at_location(expando_func);
        let elements = self.checker.borrow_mut().get_properties_of_type(t);
        if elements.is_empty() {
            return String::new();
        }
        drop(nodes);

        let mut new_properties: Vec<NodeId> = Vec::new();
        for &symbol in &elements {
            let (sym_name, has_var_decl) = {
                let symbols = self.program.symbols.clone();
                let has_var_decl = symbols[symbol.index()]
                    .value_declaration
                    .is_some_and(|d| {
                        let nodes =
                            self.program.nodes(self.source_file.file_index());
                        ast::is_variable_declaration(&nodes[d])
                    });
                (symbols[symbol.index()].name.clone(), has_var_decl)
            };
            if !scanner::utilities::is_identifier_text(
                &sym_name,
                tsc_core::languagevariant::LanguageVariant::Standard,
            ) {
                continue;
            }
            // skip symbols that already have a variable declaration
            if has_var_decl {
                continue;
            }

            let sym_type = self.checker.borrow_mut().get_type_of_symbol(symbol);
            let type_node = self.type_to_minimized_reference_type(
                sym_type,
                Some(expando_func),
                declaration_emit_node_builder_flags(),
            );
            let Some(type_node) = type_node else {
                continue;
            };

            let var_stmt = self.with_factory(|m, factory| {
                let name = factory.new_identifier(m, &sym_name);
                let var_decl = factory.new_variable_declaration(
                    m,
                    Some(name),
                    None,
                    Some(type_node),
                    None,
                );
                let export_token = factory.new_token(m, Kind::ExportKeyword);
                let decls = factory.new_node_list([var_decl]);
                let var_decl_list = factory.new_variable_declaration_list(
                    m,
                    Some(decls),
                    NodeFlags::NONE,
                );
                let modifier_list = factory.new_modifier_list(m, [export_token]);
                factory.new_variable_statement(
                    m,
                    Some(modifier_list),
                    Some(var_decl_list),
                )
            });
            new_properties.push(var_stmt);
        }

        if new_properties.is_empty() {
            return String::new();
        }

        let nodes = self.program.nodes(self.source_file.file_index());
        let has_export_modifier = ast::has_syntactic_modifier(
            &nodes[expando_func],
            ast::ModifierFlags::EXPORT,
        );
        drop(nodes);

        let namespace = self.with_factory(|m, factory| {
            let mut modifiers: Vec<NodeId> = Vec::new();
            if has_export_modifier {
                modifiers.push(factory.new_token(m, Kind::ExportKeyword));
            }
            modifiers.push(factory.new_token(m, Kind::DeclareKeyword));

            let modifier_list = factory.new_modifier_list(m, modifiers);
            let name = factory.new_identifier(m, &func_name_text);
            let statements = factory.new_node_list(new_properties);
            let body = factory.new_module_block(m, Some(statements));
            let namespace = factory.new_module_declaration(
                m,
                Some(modifier_list),
                Kind::NamespaceKeyword,
                Some(name),
                None, /*attributes*/
                Some(body),
            );
            // Set the flags for namespace
            m[namespace].flags = NodeFlags::AMBIENT
                | NodeFlags::EXPORT_CONTEXT
                | NodeFlags::CONTEXT_FLAGS;
            namespace
        });

        let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
        self.change_tracker
            .insert_node_after(&nodes_handle, self.source_file, expando_func, namespace);
        diagnostics::Annotate_types_of_properties_expando_function_in_a_namespace
            .localize(&self.locale, &[""; 0])
    }

    /// `addInlineAssertion`.
    fn add_inline_assertion(&mut self, span: TextRange) -> String {
        let node_with_diag = {
            let mut m = self.program.nodes_mut(self.source_file.file_index());
            astnav::tokens::get_token_at_position(&mut m, self.source_file, span.pos())
        };
        let Some(node_with_diag) = node_with_diag else {
            return String::new();
        };

        // No inline assertions for expando members
        if find_expando_function(self.checker, self.program, node_with_diag).is_some() {
            return String::new();
        }

        let nodes = self.program.nodes(self.source_file.file_index());
        let target_node = find_best_fitting_node(&nodes, Some(node_with_diag), span);
        let Some(target_node) = target_node else {
            return String::new();
        };
        if is_value_signature_declaration(&nodes[target_node])
            || nodes[target_node]
                .parent
                .is_some_and(|p| is_value_signature_declaration(&nodes[p]))
        {
            return String::new();
        }

        let is_expression_target = ast::is_expression(&nodes[target_node], &nodes);
        let is_shorthand_property_assignment_target =
            ast::is_shorthand_property_assignment(&nodes[target_node]);

        // Go's IsDeclaration is broader than TS's isDeclaration (e.g. CallExpression has
        // DeclarationData in Go but is not a declaration kind in TS). Use
        // isNamedDeclarationKind to match TS behavior.
        if !is_shorthand_property_assignment_target
            && is_named_declaration_kind(&nodes[target_node])
        {
            return String::new();
        }
        // No inline assertions on binding patterns
        if ast::find_ancestor(Some(target_node), &nodes, &mut |n, _| {
            ast::is_binding_pattern(n)
        })
        .is_some()
        {
            return String::new();
        }
        // No inline assertions on enum members
        if ast::find_ancestor(Some(target_node), &nodes, &mut |n, _| {
            ast::is_enum_member(n)
        })
        .is_some()
        {
            return String::new();
        }
        // No support for typeof in extends clauses
        if is_expression_target
            && (ast::find_ancestor_kind(
                Some(target_node),
                Kind::HeritageClause,
                &nodes,
            )
            .is_some()
                || ast::find_ancestor(Some(target_node), &nodes, &mut |n, _| {
                    ast::is_type_node(n)
                })
                .is_some())
        {
            return String::new();
        }
        // Can't inline type spread elements
        if ast::is_spread_element(&nodes[target_node]) {
            return String::new();
        }

        let variable_declaration = ast::find_ancestor_kind(
            Some(target_node),
            Kind::VariableDeclaration,
            &nodes,
        );
        drop(nodes);
        let variable_type = variable_declaration.map(|vd| {
            self.checker.borrow_mut().get_type_at_location(vd)
        });
        // Can't use typeof on unique symbols
        if let Some(variable_type) = variable_type {
            if self
                .checker
                .borrow()
                .types
                .get(variable_type)
                .flags()
                .intersects(TypeFlags::UNIQUE_ES_SYMBOL)
            {
                return String::new();
            }
        }

        if !is_expression_target && !is_shorthand_property_assignment_target {
            return String::new();
        }

        let type_node = self.infer_type(target_node, variable_type);
        let Some(type_node) = type_node else {
            return String::new();
        };
        if self.mutated_target {
            return String::new();
        }

        if is_shorthand_property_assignment_target {
            // Insert `: expr as Type` after the shorthand property name
            let nodes = self.program.nodes(self.source_file.file_index());
            let shorthand_name = nodes[target_node]
                .as_shorthand_property_assignment()
                .named_member_base
                .name
                .unwrap();
            let end = nodes[target_node].end();
            drop(nodes);
            let as_expr = self.with_factory(|m, factory| {
                let cloned_name = factory
                    .deep_clone_node(m, shorthand_name)
                    .expect("DeepCloneNode");
                create_as_expression(m, factory, cloned_name, type_node)
            });
            let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
            self.change_tracker.insert_node_at(
                &nodes_handle,
                self.source_file,
                end,
                as_expr,
                NodeOptions {
                    prefix: ": ".to_string(),
                    ..Default::default()
                },
            );
        } else if is_expression_target {
            // Replace expression with `(expression) satisfies Type as Type` or
            // `expression satisfies Type as Type`
            let nodes = self.program.nodes(self.source_file.file_index());
            let needs_parens =
                needs_parenthesized_expression_for_assertion(&nodes[target_node], &nodes);
            drop(nodes);
            let satisfies_as_expr = self.with_factory(|m, factory| {
                let mut cloned_target = factory
                    .deep_clone_node(m, target_node)
                    .expect("DeepCloneNode");
                if needs_parens {
                    cloned_target =
                        factory.new_parenthesized_expression(m, Some(cloned_target));
                }
                let cloned_type = factory
                    .deep_clone_node(m, type_node)
                    .expect("DeepCloneNode");
                let satisfies_expr = factory.new_satisfies_expression(
                    m,
                    Some(cloned_target),
                    Some(cloned_type),
                );
                factory.new_as_expression(
                    m,
                    Some(satisfies_expr),
                    Some(type_node),
                )
            });
            let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
            self.change_tracker.replace_node(
                &nodes_handle,
                self.source_file,
                target_node,
                satisfies_as_expr,
                None,
            );
        } else {
            return String::new();
        }

        let type_str = {
            let mut m = self.program.nodes_mut(self.source_file.file_index());
            type_to_string_for_diag(
                self.checker,
                &mut m,
                type_node,
                Some(self.source_file),
                self.change_tracker,
            )
        };
        diagnostics::Add_satisfies_and_an_inline_type_assertion_with_0
            .localize(&self.locale, &[type_str])
    }

    /// `extractAsVariable`.
    fn extract_as_variable(&mut self, span: TextRange) -> String {
        let node_with_diag = {
            let mut m = self.program.nodes_mut(self.source_file.file_index());
            astnav::tokens::get_token_at_position(&mut m, self.source_file, span.pos())
        };
        let Some(node_with_diag) = node_with_diag else {
            return String::new();
        };
        let nodes = self.program.nodes(self.source_file.file_index());
        let target_node = find_best_fitting_node(&nodes, Some(node_with_diag), span);
        let Some(target_node) = target_node else {
            return String::new();
        };
        if is_value_signature_declaration(&nodes[target_node])
            || nodes[target_node]
                .parent
                .is_some_and(|p| is_value_signature_declaration(&nodes[p]))
        {
            return String::new();
        }

        if !ast::is_expression(&nodes[target_node], &nodes) {
            return String::new();
        }

        // Array literals should be marked as const
        if ast::is_array_literal_expression(&nodes[target_node]) {
            drop(nodes);
            let as_expr = self.with_factory(|m, factory| {
                let const_name = factory.new_identifier(m, "const");
                let const_ref = factory.new_type_reference_node(
                    m,
                    Some(const_name),
                    None,
                );
                let cloned = factory
                    .deep_clone_node(m, target_node)
                    .expect("DeepCloneNode");
                create_as_expression(m, factory, cloned, const_ref)
            });
            let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
            self.change_tracker.replace_node(
                &nodes_handle,
                self.source_file,
                target_node,
                as_expr,
                None,
            );
            return diagnostics::Mark_array_literal_as_const
                .localize(&self.locale, &[""; 0]);
        }

        let parent_property_assignment = ast::find_ancestor_kind(
            Some(target_node),
            Kind::PropertyAssignment,
            &nodes,
        );
        let Some(parent_property_assignment) = parent_property_assignment else {
            return String::new();
        };

        // Identifiers or entity names can already be typeof-ed
        if Some(parent_property_assignment) == nodes[target_node].parent
            && ast::is_entity_name_expression(&nodes[target_node], &nodes)
        {
            return String::new();
        }

        let name_text = get_identifier_name_for_node(&nodes, target_node);
        let mut replacement_target = target_node;
        let mut initialization_node = target_node;
        let mut needs_const_wrap = false;

        // Handle spread elements: walk up to the spread's parent and handle
        // const assertions
        if ast::is_spread_element(&nodes[replacement_target]) {
            let parent = nodes[replacement_target]
                .parent
                .expect("spread element without parent");
            replacement_target = ast::walk_up_parenthesized_expressions(parent, &nodes)
                .unwrap_or(parent);
            if let Some(p) = nodes[replacement_target].parent {
                if is_const_assertion(&nodes[p], &nodes) {
                    replacement_target = p;
                    initialization_node = replacement_target;
                } else {
                    needs_const_wrap = true;
                }
            } else {
                needs_const_wrap = true;
            }
        }

        if ast::is_entity_name_expression(&nodes[replacement_target], &nodes) {
            return String::new();
        }
        drop(nodes);

        let (temp_name, var_stmt, as_expr) = self.with_factory(|m, factory| {
            let temp_name = factory.new_unique_name_ex(
                m,
                &name_text,
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC,
                    ..Default::default()
                },
            );

            let initialization_node = if needs_const_wrap {
                let const_name = factory.new_identifier(m, "const");
                let const_ref = factory.new_type_reference_node(
                    m,
                    Some(const_name),
                    None,
                );
                let cloned = factory
                    .deep_clone_node(m, replacement_target)
                    .expect("DeepCloneNode");
                create_as_expression(m, factory, cloned, const_ref)
            } else {
                initialization_node
            };

            let cloned_init = factory
                .deep_clone_node(m, initialization_node)
                .expect("DeepCloneNode");
            let var_decl = factory.new_variable_declaration(
                m,
                Some(temp_name),
                None,
                None,
                Some(cloned_init),
            );
            let decls = factory.new_node_list([var_decl]);
            let var_decl_list = factory.new_variable_declaration_list(
                m,
                Some(decls),
                NodeFlags::CONST,
            );
            let var_stmt = factory.new_variable_statement(m, None, Some(var_decl_list));

            let type_query = factory.new_type_query_node(m, Some(temp_name), None);
            let as_expr = factory.new_as_expression(m, Some(temp_name), Some(type_query));

            (temp_name, var_stmt, as_expr)
        });

        let nodes = self.program.nodes(self.source_file.file_index());
        let statement = ast::find_ancestor(Some(target_node), &nodes, &mut |n, nodes| {
            ast::is_statement(n, nodes)
        });
        drop(nodes);
        let Some(statement) = statement else {
            return String::new();
        };

        let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
        self.change_tracker.insert_node_before(
            &nodes_handle,
            self.source_file,
            statement,
            var_stmt,
            false,
            LeadingTriviaOption::None,
        );

        self.change_tracker.replace_node(
            &nodes_handle,
            self.source_file,
            replacement_target,
            as_expr,
            None,
        );

        let id_text = {
            let mut m = self.program.nodes_mut(self.source_file.file_index());
            type_to_string_for_diag(
                self.checker,
                &mut m,
                temp_name,
                Some(self.source_file),
                self.change_tracker,
            )
        };
        diagnostics::Extract_to_variable_and_replace_with_0_as_typeof_0
            .localize(&self.locale, &[id_text])
    }

    /// `fixIsolatedDeclarationError`.
    fn fix_isolated_declaration_error(&mut self, node: NodeId) -> String {
        // Avoid creating duplicate fixes for the same node
        if !self.fixed_nodes.insert(node) {
            return String::new();
        }

        let nodes = self.program.nodes(self.source_file.file_index());
        let kind = nodes[node].kind;
        drop(nodes);
        match kind {
            Kind::Parameter | Kind::PropertyDeclaration | Kind::VariableDeclaration => {
                self.add_type_to_variable_like(node)
            }
            Kind::ArrowFunction
            | Kind::FunctionExpression
            | Kind::FunctionDeclaration
            | Kind::MethodDeclaration
            | Kind::GetAccessor => self.add_type_to_signature_declaration(node),
            Kind::ExportAssignment => self.transform_export_assignment(node),
            Kind::ClassDeclaration => self.transform_extends_clause_with_expression(node),
            Kind::ObjectBindingPattern | Kind::ArrayBindingPattern => {
                self.transform_destructuring_patterns(node)
            }
            _ => String::new(),
        }
    }

    /// `addTypeToSignatureDeclaration`.
    fn add_type_to_signature_declaration(&mut self, func_node: NodeId) -> String {
        let nodes = self.program.nodes(self.source_file.file_index());
        if nodes[func_node].type_().is_some() {
            return String::new();
        }
        drop(nodes);
        let Some(type_node) = self.infer_type(func_node, None) else {
            return String::new();
        };
        let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
        self.change_tracker.try_insert_type_annotation(
            &nodes_handle,
            self.source_file,
            func_node,
            type_node,
        );
        let type_str = {
            let mut m = self.program.nodes_mut(self.source_file.file_index());
            type_to_string_for_diag(
                self.checker,
                &mut m,
                type_node,
                Some(self.source_file),
                self.change_tracker,
            )
        };
        diagnostics::Add_return_type_0.localize(&self.locale, &[type_str])
    }

    /// `transformExportAssignment`.
    fn transform_export_assignment(&mut self, default_export: NodeId) -> String {
        let nodes = self.program.nodes(self.source_file.file_index());
        let export_assignment = nodes[default_export].as_export_assignment();
        if export_assignment.is_export_equals {
            return String::new();
        }

        let expression = export_assignment.expression;
        let Some(expression) = expression else {
            return String::new();
        };
        let modifiers = nodes[default_export].modifiers().cloned();
        drop(nodes);
        let Some(type_node) = self.infer_type(expression, None) else {
            return String::new();
        };

        let (var_stmt, new_export) = self.with_factory(|m, factory| {
            let default_identifier = factory.new_unique_name(m, "_default");

            // Deep clone the expression so synthesized nodes don't reference
            // original source positions
            let cloned_expression = factory
                .deep_clone_node(m, expression)
                .expect("DeepCloneNode");

            let var_decl = factory.new_variable_declaration(
                m,
                Some(default_identifier),
                None,
                Some(type_node),
                Some(cloned_expression),
            );
            let decls = factory.new_node_list([var_decl]);
            let var_decl_list = factory.new_variable_declaration_list(
                m,
                Some(decls),
                NodeFlags::CONST,
            );
            let var_stmt = factory.new_variable_statement(m, None, Some(var_decl_list));

            let new_export = factory
                .update_export_assignment(
                    m,
                    default_export,
                    modifiers,
                    false,
                    None,
                    Some(default_identifier),
                )
                .unwrap_or(default_export);

            (var_stmt, new_export)
        });

        let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
        self.change_tracker.replace_node_with_nodes(
            &nodes_handle,
            self.source_file,
            default_export,
            vec![var_stmt, new_export],
            None,
        );
        diagnostics::Extract_default_export_to_variable
            .localize(&self.locale, &[""; 0])
    }

    /// `transformExtendsClauseWithExpression`.
    fn transform_extends_clause_with_expression(&mut self, class_decl: NodeId) -> String {
        let nodes = self.program.nodes(self.source_file.file_index());
        let cd = nodes[class_decl].as_class_declaration();
        let mut extends_clause: Option<NodeId> = None;
        if let Some(heritage_clauses) = &cd.class_like_base.heritage_clauses {
            for &clause in heritage_clauses.nodes.iter() {
                if nodes[clause].as_heritage_clause().token == Kind::ExtendsKeyword {
                    extends_clause = Some(clause);
                    break;
                }
            }
        }
        let Some(extends_clause) = extends_clause else {
            return String::new();
        };

        let heritage_types = nodes[extends_clause].as_heritage_clause().types.clone();
        let Some(heritage_types) = heritage_types else {
            return String::new();
        };
        if heritage_types.nodes.is_empty() {
            return String::new();
        }
        let heritage_expression = heritage_types.nodes[0];
        let expression = nodes[heritage_expression]
            .as_expression_with_type_arguments()
            .expression;
        let Some(expression) = expression else {
            return String::new();
        };

        let base_name = if let Some(name) = cd.class_like_base.name {
            format!("{}Base", nodes[name].text(&nodes))
        } else {
            "Anonymous".to_string()
        };
        drop(nodes);

        let Some(heritage_type_node) = self.infer_type(expression, None) else {
            return String::new();
        };

        let (base_class_name, var_stmt, heritage_replacement) =
            self.with_factory(|m, factory| {
                let base_class_name = factory.new_unique_name_ex(
                    m,
                    &base_name,
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::OPTIMISTIC,
                        ..Default::default()
                    },
                );

                // Create: const <BaseName>: <type> = <expression>;
                let cloned_expression = factory
                    .deep_clone_node(m, expression)
                    .expect("DeepCloneNode");
                let var_decl = factory.new_variable_declaration(
                    m,
                    Some(base_class_name),
                    None,
                    Some(heritage_type_node),
                    Some(cloned_expression),
                );
                let decls = factory.new_node_list([var_decl]);
                let var_decl_list = factory.new_variable_declaration_list(
                    m,
                    Some(decls),
                    NodeFlags::CONST,
                );
                let var_stmt =
                    factory.new_variable_statement(m, None, Some(var_decl_list));
                let heritage_replacement = factory.new_expression_with_type_arguments(
                    m,
                    Some(base_class_name),
                    None,
                );
                (base_class_name, var_stmt, heritage_replacement)
            });

        let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
        self.change_tracker.insert_node_before(
            &nodes_handle,
            self.source_file,
            class_decl,
            var_stmt,
            false,
            LeadingTriviaOption::None,
        );

        // Replace the heritage expression with the base class name
        self.change_tracker.replace_node(
            &nodes_handle,
            self.source_file,
            heritage_expression,
            heritage_replacement,
            None,
        );
        let _ = base_class_name;

        diagnostics::Extract_base_class_to_variable
            .localize(&self.locale, &[""; 0])
    }

    /// `transformDestructuringPatterns`.
    fn transform_destructuring_patterns(&mut self, binding_pattern: NodeId) -> String {
        let nodes = self.program.nodes(self.source_file.file_index());
        let Some(enclosing_variable_declaration) = nodes[binding_pattern].parent else {
            return String::new();
        };
        if !ast::is_variable_declaration(&nodes[enclosing_variable_declaration]) {
            return String::new();
        }
        let Some(enclosing_var_stmt) = nodes[enclosing_variable_declaration]
            .parent
            .and_then(|p| nodes[p].parent)
        else {
            return String::new();
        };
        if !ast::is_variable_statement(&nodes[enclosing_var_stmt]) {
            return String::new();
        }

        let initializer = nodes[enclosing_variable_declaration].initializer();
        let Some(initializer) = initializer else {
            return String::new();
        };
        let initializer_is_identifier = ast::is_identifier(&nodes[initializer]);
        let initializer_text = if initializer_is_identifier {
            nodes[initializer].text(&nodes).into_owned()
        } else {
            String::new()
        };
        let enclosing_var_stmt_modifiers =
            nodes[enclosing_var_stmt].modifiers().cloned();
        let decl_list = nodes[enclosing_var_stmt]
            .as_variable_statement()
            .declaration_list;
        let declarations: Vec<NodeId> = decl_list
            .and_then(|dl| nodes[dl].as_variable_declaration_list().declarations.clone())
            .map_or_else(Vec::new, |d| d.nodes.to_vec());
        let decl_list_flags = decl_list.map(|dl| nodes[dl].flags);
        drop(nodes);

        let mut new_nodes: Vec<NodeId> = Vec::new();

        let base_expr_node = if !initializer_is_identifier {
            // Create a temporary variable for complex expressions
            self.with_factory(|m, factory| {
                let temp_name = factory.new_unique_name_ex(
                    m,
                    "dest",
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::OPTIMISTIC,
                        ..Default::default()
                    },
                );
                let cloned_initializer = factory
                    .deep_clone_node(m, initializer)
                    .expect("DeepCloneNode");
                let var_decl = factory.new_variable_declaration(
                    m,
                    Some(temp_name),
                    None,
                    None,
                    Some(cloned_initializer),
                );
                let decls = factory.new_node_list([var_decl]);
                let var_decl_list = factory.new_variable_declaration_list(
                    m,
                    Some(decls),
                    NodeFlags::CONST,
                );
                let var_stmt =
                    factory.new_variable_statement(m, None, Some(var_decl_list));
                new_nodes.push(var_stmt);
                temp_name
            })
        } else {
            // Use a new identifier to avoid referencing original source
            // positions
            self.with_factory(|m, factory| {
                factory.new_identifier(m, &initializer_text)
            })
        };

        // Extract each binding element as a separate variable with type
        // annotation
        self.extract_binding_elements(
            binding_pattern,
            base_expr_node,
            &mut new_nodes,
            enclosing_var_stmt,
        );

        if new_nodes.is_empty() {
            return String::new();
        }

        // If the enclosing variable statement has multiple declarations,
        // preserve the non-destructuring ones
        if declarations.len() > 1 {
            let remaining_decls: Vec<NodeId> = declarations
                .iter()
                .copied()
                .filter(|&d| d != enclosing_variable_declaration)
                .collect();
            if !remaining_decls.is_empty() {
                let updated_var_stmt = self.with_factory(|m, factory| {
                    let decls = factory.new_node_list(remaining_decls);
                    let updated_decl_list = factory
                        .update_variable_declaration_list(
                            m,
                            decl_list.unwrap(),
                            Some(decls),
                            decl_list_flags.unwrap_or(NodeFlags::NONE),
                        )
                        .unwrap_or(decl_list.unwrap());
                    factory
                        .update_variable_statement(
                            m,
                            enclosing_var_stmt,
                            enclosing_var_stmt_modifiers,
                            Some(updated_decl_list),
                        )
                        .unwrap_or(enclosing_var_stmt)
                });
                new_nodes.push(updated_var_stmt);
            }
        }

        let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
        self.change_tracker.replace_node_with_nodes(
            &nodes_handle,
            self.source_file,
            enclosing_var_stmt,
            new_nodes,
            None,
        );
        diagnostics::Extract_binding_expressions_to_variable
            .localize(&self.locale, &[""; 0])
    }

    /// `extractBindingElements`.
    fn extract_binding_elements(
        &mut self,
        binding_pattern: NodeId,
        base_expr: NodeId,
        new_nodes: &mut Vec<NodeId>,
        enclosing_var_stmt: NodeId,
    ) {
        let nodes = self.program.nodes(self.source_file.file_index());
        if ast::is_object_binding_pattern(&nodes[binding_pattern]) {
            let elements: Vec<NodeId> = nodes[binding_pattern]
                .as_binding_pattern()
                .elements
                .as_ref()
                .map_or_else(Vec::new, |e| e.nodes.to_vec());
            drop(nodes);
            for element in elements {
                let nodes = self.program.nodes(self.source_file.file_index());
                if ast::is_omitted_expression(&nodes[element]) {
                    continue;
                }
                let be = nodes[element].as_binding_element();
                let Some(name) = be.name else {
                    continue;
                };

                // Build property access expression
                enum PropAccess {
                    Computed(NodeId),
                    Named(String),
                    None,
                }
                let prop_access = if be.property_name.is_some_and(|p| {
                    ast::is_computed_property_name(&nodes[p])
                }) {
                    let expr = nodes[be.property_name.unwrap()]
                        .as_computed_property_name()
                        .expression;
                    match expr {
                        Some(e) => PropAccess::Computed(e),
                        None => {
                            drop(nodes);
                            continue;
                        }
                    }
                } else if let Some(property_name) = be.property_name {
                    // Use property name text (handles identifiers, string
                    // literals, numeric literals)
                    PropAccess::Named(
                        nodes[property_name].text(&nodes).into_owned(),
                    )
                } else if ast::is_identifier(&nodes[name]) {
                    PropAccess::Named(nodes[name].text(&nodes).into_owned())
                } else {
                    PropAccess::None
                };
                let name_is_binding_pattern = ast::is_binding_pattern(&nodes[name]);
                drop(nodes);

                let access_expr = match prop_access {
                    PropAccess::Computed(computed_expression) => {
                        // Handle computed property names: create a temp
                        // variable for the computed expression
                        let (comp_var_stmt, access_expr) =
                            self.with_factory(|m, factory| {
                                let identifier_for_computed_property = factory
                                    .new_generated_name_for_node(
                                        m,
                                        computed_expression,
                                    );
                                let comp_var_decl =
                                    factory.new_variable_declaration(
                                        m,
                                        Some(identifier_for_computed_property),
                                        None,
                                        None,
                                        Some(computed_expression),
                                    );
                                let comp_decls =
                                    factory.new_node_list([comp_var_decl]);
                                let comp_var_decl_list = factory
                                    .new_variable_declaration_list(
                                        m,
                                        Some(comp_decls),
                                        NodeFlags::CONST,
                                    );
                                let comp_var_stmt = factory
                                    .new_variable_statement(
                                        m,
                                        None,
                                        Some(comp_var_decl_list),
                                    );
                                let access_expr = factory
                                    .new_element_access_expression(
                                        m,
                                        Some(base_expr),
                                        None,
                                        Some(identifier_for_computed_property),
                                        NodeFlags::NONE,
                                    );
                                (comp_var_stmt, access_expr)
                            });
                        new_nodes.push(comp_var_stmt);
                        access_expr
                    }
                    PropAccess::Named(text) => {
                        self.with_factory(|m, factory| {
                            let ident = factory.new_identifier(m, &text);
                            factory.new_property_access_expression(
                                m,
                                Some(base_expr),
                                None,
                                Some(ident),
                                NodeFlags::NONE,
                            )
                        })
                    }
                    PropAccess::None => continue,
                };

                if name_is_binding_pattern {
                    self.extract_binding_elements(
                        name,
                        access_expr,
                        new_nodes,
                        enclosing_var_stmt,
                    );
                } else {
                    self.emit_binding_element_variable(
                        name,
                        element,
                        access_expr,
                        new_nodes,
                        enclosing_var_stmt,
                    );
                }
            }
        } else if ast::is_array_binding_pattern(&nodes[binding_pattern]) {
            let elements: Vec<NodeId> = nodes[binding_pattern]
                .as_binding_pattern()
                .elements
                .as_ref()
                .map_or_else(Vec::new, |e| e.nodes.to_vec());
            drop(nodes);
            for (i, element) in elements.into_iter().enumerate() {
                let nodes = self.program.nodes(self.source_file.file_index());
                if ast::is_omitted_expression(&nodes[element]) {
                    continue;
                }
                let be = nodes[element].as_binding_element();
                let Some(name) = be.name else {
                    continue;
                };
                let name_is_binding_pattern = ast::is_binding_pattern(&nodes[name]);
                drop(nodes);

                let access_expr = self.with_factory(|m, factory| {
                    let index_lit = factory.new_numeric_literal(
                        m,
                        &i.to_string(),
                        TokenFlags::NONE,
                    );
                    factory.new_element_access_expression(
                        m,
                        Some(base_expr),
                        None,
                        Some(index_lit),
                        NodeFlags::NONE,
                    )
                });

                if name_is_binding_pattern {
                    self.extract_binding_elements(
                        name,
                        access_expr,
                        new_nodes,
                        enclosing_var_stmt,
                    );
                } else {
                    self.emit_binding_element_variable(
                        name,
                        element,
                        access_expr,
                        new_nodes,
                        enclosing_var_stmt,
                    );
                }
            }
        }
    }

    /// `emitBindingElementVariable` creates a variable declaration for a
    /// single binding element, handling default initializers by creating a
    /// ternary `temp === undefined ? default : temp`.
    fn emit_binding_element_variable(
        &mut self,
        name: NodeId,
        be: NodeId,
        access_expr: NodeId,
        new_nodes: &mut Vec<NodeId>,
        enclosing_var_stmt: NodeId,
    ) {
        let type_node = self.infer_type(name, None);
        let mut variable_initializer = access_expr;

        let nodes = self.program.nodes(self.source_file.file_index());
        let be_data = nodes[be].as_binding_element();
        let be_initializer = be_data.initializer;
        let be_property_name = be_data.property_name;
        let name_text = nodes[name].text(&nodes).into_owned();
        let has_export = ast::has_syntactic_modifier(
            &nodes[enclosing_var_stmt],
            ast::ModifierFlags::EXPORT,
        );
        let temp_base_name = if be_property_name.is_some_and(|p| {
            ast::is_identifier(&nodes[p])
        }) {
            nodes[be_property_name.unwrap()].text(&nodes).into_owned()
        } else {
            "temp".to_string()
        };
        drop(nodes);

        if let Some(be_initializer) = be_initializer {
            // Create a temp variable to hold the accessed value, then use a
            // conditional expression to apply the default:
            // `temp === undefined ? defaultValue : temp`
            let (temp_var_stmt, conditional) = self.with_factory(|m, factory| {
                let temp_name = factory.new_unique_name_ex(
                    m,
                    &temp_base_name,
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::OPTIMISTIC,
                        ..Default::default()
                    },
                );
                let temp_var_decl = factory.new_variable_declaration(
                    m,
                    Some(temp_name),
                    None,
                    None,
                    Some(variable_initializer),
                );
                let temp_decls = factory.new_node_list([temp_var_decl]);
                let temp_var_decl_list = factory.new_variable_declaration_list(
                    m,
                    Some(temp_decls),
                    NodeFlags::CONST,
                );
                let temp_var_stmt = factory.new_variable_statement(
                    m,
                    None,
                    Some(temp_var_decl_list),
                );

                let eqeqeq_token = factory.new_token(m, Kind::EqualsEqualsEqualsToken);
                let undefined_ident = factory.new_identifier(m, "undefined");
                let condition = factory.new_binary_expression(
                    m,
                    None,
                    Some(temp_name),
                    None,
                    Some(eqeqeq_token),
                    Some(undefined_ident),
                );
                let question_token = factory.new_token(m, Kind::QuestionToken);
                let colon_token = factory.new_token(m, Kind::ColonToken);
                let conditional = factory.new_conditional_expression(
                    m,
                    Some(condition),
                    Some(question_token),
                    Some(be_initializer),
                    Some(colon_token),
                    Some(variable_initializer),
                );
                (temp_var_stmt, conditional)
            });
            new_nodes.push(temp_var_stmt);
            variable_initializer = conditional;
        }

        let export_modifier = self.with_factory(|m, factory| {
            if has_export {
                let export_token = factory.new_token(m, Kind::ExportKeyword);
                Some(factory.new_modifier_list(m, [export_token]))
            } else {
                None
            }
        });

        let var_stmt = self.with_factory(|m, factory| {
            let name_ident = factory.new_identifier(m, &name_text);
            let var_decl = factory.new_variable_declaration(
                m,
                Some(name_ident),
                None,
                type_node,
                Some(variable_initializer),
            );
            let decls = factory.new_node_list([var_decl]);
            let var_decl_list = factory.new_variable_declaration_list(
                m,
                Some(decls),
                NodeFlags::CONST,
            );
            factory.new_variable_statement(m, export_modifier, Some(var_decl_list))
        });
        new_nodes.push(var_stmt);
    }

    /// `getExportModifier` — folded into `emit_binding_element_variable`.

    /// `inferType`.
    fn infer_type(&mut self, node: NodeId, variable_type: Option<TypeId>) -> Option<NodeId> {
        self.mutated_target = false;

        // Handle Relative mode first: return typeof X for identifiers
        if self.type_print_mode == TypePrintMode::Relative {
            return self.relative_type(node);
        }

        let nodes = self.program.nodes(self.source_file.file_index());
        let is_value_sig_decl = is_value_signature_declaration(&nodes[node]);
        drop(nodes);

        let mut t: TypeId;
        if is_value_sig_decl {
            let signature = self
                .checker
                .borrow_mut()
                .get_signature_from_declaration(node);
            if signature.is_some() {
                let type_predicate = self
                    .checker
                    .borrow_mut()
                    .get_type_predicate_of_signature(signature);
                if let Some(type_predicate) = type_predicate {
                    let Some(predicate_type) = type_predicate.t else {
                        return None;
                    };
                    let nodes = self.program.nodes(self.source_file.file_index());
                    let enclosing_decl = ast::find_ancestor(
                        Some(node),
                        &nodes,
                        &mut |n, _| ast::is_declaration(n),
                    )
                    .unwrap_or(self.source_file);
                    drop(nodes);
                    let mut flags = declaration_emit_node_builder_flags();
                    if self
                        .checker
                        .borrow()
                        .types
                        .get(predicate_type)
                        .flags()
                        .intersects(TypeFlags::UNIQUE_ES_SYMBOL)
                    {
                        flags |= nodebuilder::Flags::ALLOW_UNIQUE_ES_SYMBOL_TYPE;
                    }
                    let result = self.checker.borrow_mut().type_predicate_to_type_predicate_node(
                        Some(&type_predicate),
                        Some(enclosing_decl),
                        flags,
                        FxHashMap::default(),
                    );
                    return result;
                }
                t = self
                    .checker
                    .borrow_mut()
                    .get_return_type_of_signature(signature);
            } else {
                return None;
            }
        } else {
            t = self.checker.borrow_mut().get_type_at_location(node);
        }

        if t.is_none() {
            return None;
        }

        // Handle Widened mode: return widened literal type if different
        if self.type_print_mode == TypePrintMode::Widened {
            if let Some(variable_type) = variable_type {
                t = variable_type;
            }
            let widened_type = self.checker.borrow_mut().get_widened_literal_type(t);
            if self
                .checker
                .borrow_mut()
                .is_type_assignable_to(widened_type, t)
            {
                return None; // widened type is same, no fix needed
            }
            t = widened_type;
        }

        let nodes = self.program.nodes(self.source_file.file_index());
        let enclosing_decl = ast::find_ancestor(Some(node), &nodes, &mut |n, _| {
            ast::is_declaration(n)
        })
        .unwrap_or(self.source_file);

        let is_param = ast::is_parameter_declaration(&nodes[node]);
        let extra_flags = self.get_extra_flags(&nodes, node, t);
        drop(nodes);

        let flags = declaration_emit_node_builder_flags() | extra_flags;

        // For parameters that require adding implicit undefined, add it to
        // the type
        if is_param
            && self
                .checker
                .borrow_mut()
                .requires_adding_implicit_undefined_api(node)
        {
            let undefined_type = self.checker.borrow().get_undefined_type();
            t = self.checker.borrow_mut().get_union_type_ex(
                &[undefined_type, t],
                tsc_checker::types::UnionReduction::NONE,
                None,
                None,
            );
        }

        self.type_to_minimized_reference_type(t, Some(enclosing_decl), flags)
    }

    /// `getExtraFlags`.
    fn get_extra_flags(&self, nodes: &[Node], node: NodeId, t: TypeId) -> nodebuilder::Flags {
        if (ast::is_variable_declaration(&nodes[node])
            || (ast::is_property_declaration(&nodes[node])
                && ast::has_syntactic_modifier(
                    &nodes[node],
                    ast::ModifierFlags::STATIC | ast::ModifierFlags::READONLY,
                )))
            && self
                .checker
                .borrow()
                .types
                .get(t)
                .flags()
                .intersects(TypeFlags::UNIQUE_ES_SYMBOL)
        {
            return nodebuilder::Flags::ALLOW_UNIQUE_ES_SYMBOL_TYPE;
        }
        nodebuilder::Flags::NONE
    }

    /// `createTypeOfFromEntityNameExpression` creates a `typeof X` type
    /// query node.
    fn create_type_of_from_entity_name_expression(&mut self, node: NodeId) -> NodeId {
        self.with_factory(|m, factory| {
            let cloned = factory
                .deep_clone_node(m, node)
                .expect("DeepCloneNode");
            factory.new_type_query_node(m, Some(cloned), None)
        })
    }

    /// `typeFromArraySpreadElements` decomposes an array literal with spread
    /// elements into separate variables, returning a tuple type of typeof
    /// references.
    fn type_from_array_spread_elements(
        &mut self,
        node: NodeId,
        name: &str,
    ) -> Option<NodeId> {
        let nodes = self.program.nodes(self.source_file.file_index());
        let is_in_const_context =
            ast::find_ancestor(Some(node), &nodes, &mut |n, nodes| {
                is_const_assertion(n, nodes)
            })
            .is_some();
        drop(nodes);
        if !is_in_const_context {
            return None;
        }
        let name = if name.is_empty() { "temp" } else { name };
        self.type_from_spreads(
            node,
            name,
            is_in_const_context,
            SpreadKind::Array,
        )
    }

    /// `typeFromObjectSpreadAssignment` decomposes an object literal with
    /// spread assignments into separate variables, returning an
    /// intersection type of typeof references.
    fn type_from_object_spread_assignment(
        &mut self,
        node: NodeId,
        name: &str,
    ) -> Option<NodeId> {
        let nodes = self.program.nodes(self.source_file.file_index());
        let is_in_const_context =
            ast::find_ancestor(Some(node), &nodes, &mut |n, nodes| {
                is_const_assertion(n, nodes)
            })
            .is_some();
        drop(nodes);
        let name = if name.is_empty() { "temp" } else { name };
        self.type_from_spreads(
            node,
            name,
            is_in_const_context,
            SpreadKind::Object,
        )
    }

    /// `typeFromSpreads` — the generic spread decomposition function, ported
    /// from TS's typeFromSpreads. It splits a literal with spread elements
    /// into separate const variables and returns a composed type.
    fn type_from_spreads(
        &mut self,
        node: NodeId,
        name: &str,
        is_in_const_context: bool,
        kind: SpreadKind,
    ) -> Option<NodeId> {
        let mut intersection_types: Vec<NodeId> = Vec::new();
        let mut new_spreads: Vec<NodeId> = Vec::new();
        let mut current_variable_properties: Vec<NodeId> = Vec::new();

        let nodes = self.program.nodes(self.source_file.file_index());
        let statement = ast::find_ancestor(Some(node), &nodes, &mut |n, nodes| {
            ast::is_statement(n, nodes)
        });
        let children: Vec<NodeId> = match kind {
            SpreadKind::Array => nodes[node]
                .as_array_literal_expression()
                .elements
                .as_ref()
                .map_or_else(Vec::new, |e| e.nodes.to_vec()),
            SpreadKind::Object => nodes[node]
                .as_object_literal_expression()
                .properties
                .as_ref()
                .map_or_else(Vec::new, |p| p.nodes.to_vec()),
        };
        drop(nodes);

        for &prop in &children {
            let (is_spread_prop, expr, expr_is_entity_name) = {
                let nodes = self.program.nodes(self.source_file.file_index());
                let is_spread_prop = match kind {
                    SpreadKind::Array => ast::is_spread_element(&nodes[prop]),
                    SpreadKind::Object => ast::is_spread_assignment(&nodes[prop]),
                };
                let expr = nodes[prop].expression();
                let is_entity = expr.is_some_and(|e| {
                    ast::is_entity_name_expression(&nodes[e], &nodes)
                });
                (is_spread_prop, expr, is_entity)
            };
            if is_spread_prop {
                self.finalizes_variable_part(
                    name,
                    is_in_const_context,
                    statement,
                    kind,
                    &mut current_variable_properties,
                    &mut intersection_types,
                    &mut new_spreads,
                );
                let Some(expr) = expr else {
                    continue;
                };
                if expr_is_entity_name {
                    let type_query =
                        self.create_type_of_from_entity_name_expression(expr);
                    intersection_types.push(type_query);
                    new_spreads.push(prop);
                } else {
                    self.make_spread_variable(
                        name,
                        is_in_const_context,
                        statement,
                        kind,
                        expr,
                        &mut intersection_types,
                        &mut new_spreads,
                    );
                }
            } else {
                current_variable_properties.push(prop);
            }
        }

        if new_spreads.is_empty() {
            return None;
        }

        self.finalizes_variable_part(
            name,
            is_in_const_context,
            statement,
            kind,
            &mut current_variable_properties,
            &mut intersection_types,
            &mut new_spreads,
        );

        let replacement = self.with_factory(|m, factory| {
            let elements = factory.new_node_list(new_spreads);
            match kind {
                SpreadKind::Array => factory.new_array_literal_expression(
                    m,
                    Some(elements),
                    true,
                ),
                SpreadKind::Object => factory.new_object_literal_expression(
                    m,
                    Some(elements),
                    true,
                ),
            }
        });
        let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
        self.change_tracker.replace_node(
            &nodes_handle,
            self.source_file,
            node,
            replacement,
            None,
        );
        self.mutated_target = true;

        self.with_factory(|m, factory| {
            match kind {
                SpreadKind::Array => {
                    let rest_types: Vec<NodeId> = intersection_types
                        .iter()
                        .map(|&t| factory.new_rest_type_node(m, Some(t)))
                        .collect();
                    let elems = factory.new_node_list(rest_types);
                    Some(factory.new_tuple_type_node(m, Some(elems)))
                }
                SpreadKind::Object => {
                    let elems = factory.new_node_list(intersection_types);
                    Some(factory.new_intersection_type_node(m, Some(elems)))
                }
            }
        })
    }

    /// `makeSpreadVariable` creates a const variable for a spread
    /// expression and adds it to the decomposition.
    #[allow(clippy::too_many_arguments)]
    fn make_spread_variable(
        &mut self,
        name: &str,
        is_in_const_context: bool,
        statement: Option<NodeId>,
        kind: SpreadKind,
        expression: NodeId,
        intersection_types: &mut Vec<NodeId>,
        new_spreads: &mut Vec<NodeId>,
    ) {
        let (temp_name, var_stmt, spread_node) = self.with_factory(|m, factory| {
            let temp_name = factory.new_unique_name_ex(
                m,
                &format!("{name}_Part{}", new_spreads.len() + 1),
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC,
                    ..Default::default()
                },
            );

            let initializer = if !is_in_const_context {
                factory
                    .deep_clone_node(m, expression)
                    .expect("DeepCloneNode")
            } else {
                let const_name = factory.new_identifier(m, "const");
                let const_ref = factory.new_type_reference_node(
                    m,
                    Some(const_name),
                    None,
                );
                let cloned = factory
                    .deep_clone_node(m, expression)
                    .expect("DeepCloneNode");
                factory.new_as_expression(m, Some(cloned), Some(const_ref))
            };

            let var_decl = factory.new_variable_declaration(
                m,
                Some(temp_name),
                None,
                None,
                Some(initializer),
            );
            let decls = factory.new_node_list([var_decl]);
            let var_decl_list = factory.new_variable_declaration_list(
                m,
                Some(decls),
                NodeFlags::CONST,
            );
            let var_stmt = factory.new_variable_statement(m, None, Some(var_decl_list));
            let spread_node = match kind {
                SpreadKind::Array => {
                    factory.new_spread_element(m, Some(temp_name))
                }
                SpreadKind::Object => {
                    factory.new_spread_assignment(m, Some(temp_name))
                }
            };
            (temp_name, var_stmt, spread_node)
        });

        if let Some(statement) = statement {
            let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
            self.change_tracker.insert_node_before(
                &nodes_handle,
                self.source_file,
                statement,
                var_stmt,
                false,
                LeadingTriviaOption::None,
            );
        }

        let type_query = self.create_type_of_from_entity_name_expression(temp_name);
        intersection_types.push(type_query);
        new_spreads.push(spread_node);
    }

    /// `finalizesVariablePart` finalizes accumulated non-spread properties
    /// into a variable.
    #[allow(clippy::too_many_arguments)]
    fn finalizes_variable_part(
        &mut self,
        name: &str,
        is_in_const_context: bool,
        statement: Option<NodeId>,
        kind: SpreadKind,
        current_variable_properties: &mut Vec<NodeId>,
        intersection_types: &mut Vec<NodeId>,
        new_spreads: &mut Vec<NodeId>,
    ) {
        if !current_variable_properties.is_empty() {
            let properties = std::mem::take(current_variable_properties);
            let node_of_kind = self.with_factory(|m, factory| {
                let elements = factory.new_node_list(properties);
                match kind {
                    SpreadKind::Array => factory.new_array_literal_expression(
                        m,
                        Some(elements),
                        true,
                    ),
                    SpreadKind::Object => factory.new_object_literal_expression(
                        m,
                        Some(elements),
                        true,
                    ),
                }
            });
            self.make_spread_variable(
                name,
                is_in_const_context,
                statement,
                kind,
                node_of_kind,
                intersection_types,
                new_spreads,
            );
        }
    }

    /// `relativeType` creates a typeof expression for a node, used in
    /// TypePrintMode.Relative. Instead of spelling out the full type,
    /// returns `typeof X` for identifiers. For object/array literals with
    /// spreads, decomposes into separate variables.
    fn relative_type(&mut self, node: NodeId) -> Option<NodeId> {
        let nodes = self.program.nodes(self.source_file.file_index());
        if ast::is_parameter_declaration(&nodes[node]) {
            return None;
        }
        if ast::is_shorthand_property_assignment(&nodes[node]) {
            let name = nodes[node]
                .as_shorthand_property_assignment()
                .named_member_base
                .name;
            drop(nodes);
            return Some(self.create_type_of_from_entity_name_expression(name?));
        }
        if ast::is_entity_name_expression(&nodes[node], &nodes) {
            drop(nodes);
            return Some(self.create_type_of_from_entity_name_expression(node));
        }
        if is_const_assertion(&nodes[node], &nodes) {
            let expr = nodes[node].expression();
            drop(nodes);
            return self.relative_type(expr?);
        }
        if ast::is_array_literal_expression(&nodes[node]) {
            let var_decl = ast::find_ancestor_kind(
                Some(node),
                Kind::VariableDeclaration,
                &nodes,
            );
            let part_name = var_decl
                .and_then(|vd| {
                    let name = nodes[vd].name()?;
                    if ast::is_identifier(&nodes[name]) {
                        Some(nodes[name].text(&nodes).into_owned())
                    } else {
                        None
                    }
                })
                .unwrap_or_default();
            drop(nodes);
            return self.type_from_array_spread_elements(node, &part_name);
        }
        if ast::is_object_literal_expression(&nodes[node]) {
            let var_decl = ast::find_ancestor_kind(
                Some(node),
                Kind::VariableDeclaration,
                &nodes,
            );
            let part_name = var_decl
                .and_then(|vd| {
                    let name = nodes[vd].name()?;
                    if ast::is_identifier(&nodes[name]) {
                        Some(nodes[name].text(&nodes).into_owned())
                    } else {
                        None
                    }
                })
                .unwrap_or_default();
            drop(nodes);
            return self.type_from_object_spread_assignment(node, &part_name);
        }
        if ast::is_variable_declaration(&nodes[node])
            && nodes[node].initializer().is_some()
        {
            let initializer = nodes[node].initializer().unwrap();
            drop(nodes);
            return self.relative_type(initializer);
        }
        if ast::is_conditional_expression(&nodes[node]) {
            let cond = nodes[node].as_conditional_expression();
            let when_true = cond.when_true;
            let when_false = cond.when_false;
            drop(nodes);
            let true_type = self.relative_type(when_true?);
            let true_type = true_type?;
            let true_mutated = self.mutated_target;
            let false_type = self.relative_type(when_false?);
            let false_type = false_type?;
            self.mutated_target = true_mutated || self.mutated_target;
            return self.with_factory(|m, factory| {
                let types = factory.new_node_list([true_type, false_type]);
                Some(factory.new_union_type_node(m, Some(types)))
            });
        }
        None
    }

    /// `typeToMinimizedReferenceType` converts a type to a type node, then
    /// trims trailing type arguments that match their defaults. Ported from
    /// TS's services/codefixes/helpers.ts typeToMinimizedReferenceType.
    fn type_to_minimized_reference_type(
        &mut self,
        t: TypeId,
        enclosing_decl: Option<NodeId>,
        flags: nodebuilder::Flags,
    ) -> Option<NodeId> {
        // !!! When truncation tracking is supported, check if the type was
        // truncated and return factory.NewKeywordTypeNode(ast.KindAnyKeyword)
        // instead of the truncated node.
        let (type_node, id_to_symbol) = type_to_type_node_ex_with_map(
            self.checker,
            t,
            enclosing_decl,
            flags,
            nodebuilder::InternalFlags::WRITE_COMPUTED_PROPS,
        );
        let mut type_node = type_node?;

        {
            let nodes = self.program.nodes(self.source_file.file_index());
            let node_type_args: Vec<NodeId> = nodes[type_node]
                .type_arguments()
                .map_or_else(Vec::new, |ta| ta.to_vec());
            let is_type_reference_node = ast::is_type_reference_node(&nodes[type_node]);
            drop(nodes);
            let is_object_reference_type = self
                .checker
                .borrow()
                .types
                .get(t)
                .object_flags()
                .intersects(ObjectFlags::REFERENCE);
            if is_type_reference_node && is_object_reference_type {
                let type_args = self.checker.borrow_mut().get_type_arguments(t);
                if !type_args.is_empty() && !node_type_args.is_empty() {
                    let cutoff = end_of_required_type_parameters(
                        &mut self.checker.borrow_mut(),
                        t,
                    );
                    if cutoff < node_type_args.len() {
                        // Trim trailing default type arguments
                        type_node = self.with_factory(|m, factory| {
                            let trimmed_args = factory
                                .new_node_list(node_type_args[..cutoff].to_vec());
                            let type_name = m[type_node].as_type_reference_node().type_name;
                            factory
                                .update_type_reference_node(
                                    m,
                                    type_node,
                                    type_name,
                                    Some(trimmed_args),
                                )
                                .unwrap_or(type_node)
                        });
                    }
                }
            }
        }

        // Convert import type references (e.g. import("./path").Name) to
        // simple type references and collect symbols that need to be imported
        let (reference_type_node, importable_symbols) =
            try_get_auto_importable_reference_from_type_node(
                self.checker,
                type_node,
                &id_to_symbol,
            );
        if let Some(reference_type_node) = reference_type_node {
            type_node = reference_type_node;
            self.symbols_to_import.extend(importable_symbols);
        }
        Some(type_node)
    }

    /// `addTypeToVariableLike`.
    fn add_type_to_variable_like(&mut self, decl: NodeId) -> String {
        let Some(type_node) = self.infer_type(decl, None) else {
            return String::new();
        };
        let nodes = self.program.nodes(self.source_file.file_index());
        let existing_type = nodes[decl].type_();
        let decl_parent = nodes[decl].parent;
        let parent_is_arrow =
            decl_parent.is_some_and(|p| ast::is_arrow_function(&nodes[p]));
        let decl_is_parameter = ast::is_parameter_declaration(&nodes[decl]);
        drop(nodes);
        let nodes_handle = self.program.nodes_handle(self.source_file.file_index());
        if let Some(existing_type) = existing_type {
            self.change_tracker.replace_node(
                &nodes_handle,
                self.source_file,
                existing_type,
                type_node,
                None,
            );
        } else {
            self.change_tracker.try_insert_type_annotation(
                &nodes_handle,
                self.source_file,
                decl,
                type_node,
            );
            // Parenthesize paren-less arrow function parameters (`x => ...`)
            // so the inserted `: T` produces `(x: T) => ...` instead of the
            // invalid `x: T => ...`. Queued after the type annotation so that
            // the `)` edit at param.End() sorts after the annotation
            // insertion.
            if decl_is_parameter && parent_is_arrow {
                self.change_tracker.parenthesize_arrow_parameters(
                    &nodes_handle,
                    self.source_file,
                    decl_parent.unwrap(),
                );
            }
        }
        let type_str = {
            let mut m = self.program.nodes_mut(self.source_file.file_index());
            type_to_string_for_diag(
                self.checker,
                &mut m,
                type_node,
                Some(self.source_file),
                self.change_tracker,
            )
        };
        diagnostics::Add_annotation_of_type_0.localize(&self.locale, &[type_str])
    }

    /// `addSymbolToExistingImport` finds the existing import declaration for
    /// the symbol's module and adds the symbol name to the named imports.
    fn add_symbol_to_existing_import(&mut self, sym: SymbolId) {
        if sym.is_none() {
            return;
        }
        let symbols = self.program.symbols.clone();
        let Some(module_symbol) = symbols[sym.index()].parent else {
            return;
        };
        let symbol_name = symbols[sym.index()].name.clone();
        drop(symbols);

        // Walk the source file's import declarations to find the one
        // importing from the same module. The arena guard must be
        // re-acquired per statement because it is dropped before the
        // checker calls below.
        let statements: Vec<NodeId> = {
            let nodes = self.program.nodes(self.source_file.file_index());
            nodes[self.source_file]
                .as_source_file()
                .statements
                .as_ref()
                .map_or_else(Vec::new, |s| s.nodes.to_vec())
        };
        for stmt in statements {
            let nodes = self.program.nodes(self.source_file.file_index());
            if !ast::is_import_declaration(&nodes[stmt]) {
                continue;
            }
            let import_decl = nodes[stmt].as_import_declaration();
            let Some(import_clause_id) = import_decl.import_clause else {
                continue;
            };
            let module_specifier = import_decl.module_specifier;
            let modifiers = nodes[stmt].modifiers().cloned();
            let attributes = import_decl.attributes;
            drop(nodes);

            // Check if this import is from the same module
            let Some(module_specifier) = module_specifier else {
                continue;
            };
            let Some(import_module_symbol) = self
                .checker
                .borrow_mut()
                .get_symbol_at_location_api(module_specifier)
            else {
                continue;
            };
            let merged_import = self
                .checker
                .borrow_mut()
                .get_merged_symbol(import_module_symbol);
            let merged_module = self
                .checker
                .borrow_mut()
                .get_merged_symbol(module_symbol);
            if merged_import != merged_module {
                continue;
            }
            let nodes = self.program.nodes(self.source_file.file_index());

            // Found the matching import - add the symbol to named imports
            let clause = nodes[import_clause_id].as_import_clause();
            if let Some(named_bindings) = clause.named_bindings {
                if ast::is_named_imports(&nodes[named_bindings]) {
                    // Add to existing named imports
                    let existing_elements: Vec<NodeId> = nodes[named_bindings]
                        .as_named_imports()
                        .elements
                        .as_ref()
                        .map_or_else(Vec::new, |e| e.nodes.to_vec());
                    let clause_name = clause.name;
                    let phase_modifier = clause.phase_modifier;
                    drop(nodes);
                    let new_import_decl = self.with_factory(|m, factory| {
                        let symbol_ident = factory.new_identifier(m, &symbol_name);
                        let new_specifier = factory.new_import_specifier(
                            m,
                            false,
                            None,
                            Some(symbol_ident),
                        );
                        let mut new_elements = existing_elements;
                        new_elements.push(new_specifier);
                        let elements = factory.new_node_list(new_elements);
                        let new_named_imports = factory.new_named_imports(
                            m,
                            Some(elements),
                        );
                        let new_import_clause = factory
                            .update_import_clause(
                                m,
                                import_clause_id,
                                phase_modifier,
                                clause_name,
                                Some(new_named_imports),
                            )
                            .unwrap_or(import_clause_id);
                        factory
                            .update_import_declaration(
                                m,
                                stmt,
                                modifiers,
                                Some(new_import_clause),
                                Some(module_specifier),
                                attributes,
                            )
                            .unwrap_or(stmt)
                    });
                    let nodes_handle =
                        self.program.nodes_handle(self.source_file.file_index());
                    self.change_tracker.replace_node(
                        &nodes_handle,
                        self.source_file,
                        stmt,
                        new_import_decl,
                        None,
                    );
                }
            }
            return;
        }
    }
}

/// `SpreadKind` — which of Go's two `typeFromSpreads` closures applies.
#[derive(Clone, Copy)]
enum SpreadKind {
    Array,
    Object,
}

/// `nodes_snapshot` — small helper for a fresh arena snapshot.
#[allow(dead_code)]
fn nodes_snapshot<'p>(program: &'p Rc<Program>, source_file: NodeId) -> Rc<ast::NodeArenaBuf> {
    program.nodes(source_file.file_index())
}

/// `endOfRequiredTypeParameters` finds the number of type arguments that
/// are actually required (i.e., differ from their defaults). Ported from
/// TS's services/codefixes/helpers.ts endOfRequiredTypeParameters.
fn end_of_required_type_parameters(ch: &mut Checker, t: TypeId) -> usize {
    let type_args = ch.get_type_arguments(t);
    if type_args.is_empty() {
        return 0;
    }
    let Some(target) = ch.types.get(t).target() else {
        return type_args.len();
    };
    let target_type = ch.types.get(target);
    let Some(interface_type) = target_type.as_interface_type() else {
        return type_args.len();
    };
    let type_params = interface_type.type_parameters().to_vec();
    let local_type_params = interface_type.local_type_parameters().to_vec();
    let outer_count = type_params.len().saturating_sub(local_type_params.len());
    for cutoff in 0..type_args.len() {
        // Skip cutoff positions where the local type parameter has no
        // default. This matches TS's check for constraint === undefined on
        // localTypeParameters, which in practice skips type parameters
        // without defaults (e.g. Set<T> where T has no default should not
        // have <unknown> elided).
        if cutoff < outer_count
            || cutoff - outer_count >= local_type_params.len()
            || !type_param_has_default(ch, local_type_params[cutoff - outer_count])
        {
            continue;
        }
        let filled_in = ch.fill_missing_type_arguments(
            &type_args[..cutoff],
            &type_params,
            cutoff,
            false,
        );
        let mut all_match = true;
        for (i, fill) in filled_in.iter().enumerate() {
            if *fill != type_args[i] {
                all_match = false;
                break;
            }
        }
        if all_match {
            return cutoff;
        }
    }
    type_args.len()
}

/// `typeParamHasDefault` checks if a type parameter has a default type
/// declaration.
fn type_param_has_default(ch: &Checker, tp: TypeId) -> bool {
    let Some(sym) = ch.types.get(tp).symbol() else {
        return false;
    };
    let symbol_arena = ch.program.as_ref().expect("program").symbols();
    let symbols = symbol_arena.clone();
    for &decl in &symbols[sym.index()].declarations {
        let nodes = ch.program.as_ref().expect("program").nodes(decl.file_index());
        if ast::is_type_parameter_declaration(&nodes[decl])
            && nodes[decl]
                .as_type_parameter_declaration()
                .default_type
                .is_some()
        {
            return true;
        }
    }
    false
}

/// `findExpandoFunction` finds the function declaration that has expando
/// properties assigned to it.
/// `isExpandoPropertyDeclarationForFix` matches TS's
/// isExpandoPropertyDeclaration which includes PropertyAccessExpression,
/// ElementAccessExpression, and BinaryExpression. The shared
/// ast.IsExpandoPropertyDeclaration was narrowed to BinaryExpression only
/// for checker purposes.
fn is_expando_property_declaration_for_fix(node: &Node) -> bool {
    ast::is_property_access_expression(node)
        || ast::is_element_access_expression(node)
        || ast::is_binary_expression(node)
}

fn find_expando_function(
    ch: &Rc<RefCell<Checker>>,
    program: &Rc<Program>,
    node: NodeId,
) -> Option<NodeId> {
    let nodes = program.nodes(node.file_index());
    let expando_declaration = ast::find_ancestor_or_quit(
        Some(node),
        &nodes,
        &mut |n, _| {
            if ast::is_statement(n, &nodes) {
                return ast::FindAncestorResult::Quit;
            }
            if is_expando_property_declaration_for_fix(n) {
                return ast::FindAncestorResult::True;
            }
            ast::FindAncestorResult::False
        },
    );

    let Some(expando_declaration) = expando_declaration else {
        return None;
    };
    if !is_expando_property_declaration_for_fix(&nodes[expando_declaration]) {
        return None;
    }

    let mut assignment_target = expando_declaration;
    // Some late bound expando members use the whole expression as the
    // declaration.
    if ast::is_binary_expression(&nodes[assignment_target]) {
        let Some(left) = nodes[assignment_target].as_binary_expression().left else {
            return None;
        };
        assignment_target = left;
        if !is_expando_property_declaration_for_fix(&nodes[assignment_target]) {
            return None;
        }
    }

    let expression = if ast::is_property_access_expression(&nodes[assignment_target]) {
        nodes[assignment_target].as_property_access_expression().expression
    } else if ast::is_element_access_expression(&nodes[assignment_target]) {
        nodes[assignment_target].as_element_access_expression().expression
    } else {
        return None;
    };
    let Some(expression) = expression else {
        return None;
    };
    drop(nodes);

    let target_type = ch.borrow_mut().get_type_at_location(expression);
    if target_type.is_none() {
        return None;
    }

    let properties = ch.borrow_mut().get_properties_of_type(target_type);
    let symbols = program.symbols.clone();
    let nodes = program.nodes(node.file_index());
    let mut found = false;
    for p in &properties {
        let vd = symbols[p.index()].value_declaration;
        if vd == Some(expando_declaration) || vd == nodes[expando_declaration].parent {
            found = true;
            break;
        }
    }
    if !found {
        return None;
    }

    let symbol = ch.borrow().types.get(target_type).symbol()?;
    let fn_decl = symbols[symbol.index()].value_declaration?;
    drop(symbols);
    drop(nodes);

    let nodes = program.nodes(node.file_index());
    if (ast::is_function_expression(&nodes[fn_decl])
        || ast::is_arrow_function(&nodes[fn_decl]))
        && nodes[fn_decl]
            .parent
            .is_some_and(|p| ast::is_variable_declaration(&nodes[p]))
    {
        return nodes[fn_decl].parent;
    }
    if ast::is_function_declaration(&nodes[fn_decl]) {
        return Some(fn_decl);
    }

    None
}

/// `needsParenthesizedExpressionForAssertion` checks if an expression needs
/// parentheses for an assertion.
fn needs_parenthesized_expression_for_assertion(node: &Node, nodes: &[Node]) -> bool {
    !ast::is_entity_name_expression(node, nodes)
        && !ast::is_call_expression(node)
        && !ast::is_object_literal_expression(node)
        && !ast::is_array_literal_expression(node)
}

/// `createAsExpression` creates an `expr as Type` expression,
/// parenthesizing if needed.
fn create_as_expression(
    nodes: &mut Vec<Node>,
    factory: &mut tsc_printer::NodeFactory,
    node: NodeId,
    type_node: NodeId,
) -> NodeId {
    let node = if needs_parenthesized_expression_for_assertion(&nodes[node], nodes) {
        factory.new_parenthesized_expression(nodes, Some(node))
    } else {
        node
    };
    factory.new_as_expression(nodes, Some(node), Some(type_node))
}

/// `isConstAssertion` checks if a node is an `as const` or `<const>`
/// assertion.
fn is_const_assertion(node: &Node, nodes: &[Node]) -> bool {
    if ast::is_assertion_expression(node) {
        if let Some(type_node) = node.type_() {
            return ast::is_const_type_reference(&nodes[type_node], nodes);
        }
    }
    false
}

/// `typeToStringForDiag` converts a type node to a string for use in
/// diagnostic descriptions. It reuses the change tracker's `EmitContext` so
/// that generated identifier names are resolved consistently with the
/// actual code edits, and passes the source file so that the printer's
/// name generator can check for conflicts with existing file-level
/// identifiers.
fn type_to_string_for_diag(
    c: &Rc<RefCell<Checker>>,
    nodes: &mut Vec<Node>,
    type_node: NodeId,
    source_file: Option<NodeId>,
    ct: &mut Tracker<'_, '_>,
) -> String {
    let saved_flags = ct.emit_context.emit_flags(type_node);
    ct.emit_context
        .set_emit_flags(type_node, saved_flags | EmitFlags::SINGLE_LINE);
    let symbol_arena = c.borrow().symbol_arena.clone();
    let symbols = symbol_arena.clone();
    let mut p = Printer::new(
        PrinterOptions {
            new_line: NewLineKind::LF,
            ..Default::default()
        },
        PrintHandlers::default(),
        &mut ct.emit_context,
        nodes,
        &symbols,
    );
    let mut writer = tsc_printer::get_single_line_string_writer();
    p.write(Some(type_node), source_file, &mut writer, None);
    // `p` holds `&mut ct.emit_context` and `&symbols` — drop it before
    // restoring emit flags and releasing the arena guard.
    drop(p);
    ct.emit_context.set_emit_flags(type_node, saved_flags);
    drop(symbols);
    let result = writer.get_text();
    if result.len() > 160 {
        // PORT: Go truncates at byte 157; floor at a char boundary to stay
        // valid UTF-8.
        let boundary = result
            .char_indices()
            .take_while(|(i, _)| *i <= 157)
            .last()
            .map_or(0, |(i, _)| i);
        return format!("{}...", &result[..boundary]);
    }
    result
}

/// `findAncestorWithMissingType` walks up the ancestor chain to find a node
/// that can have a type annotation and is missing one.
fn find_ancestor_with_missing_type(
    nodes: &[Node],
    node: Option<NodeId>,
) -> Option<NodeId> {
    ast::find_ancestor(node, nodes, &mut |n, nodes| {
        if !can_have_type_annotation(n.kind) {
            return false;
        }
        if ast::is_object_binding_pattern(n) || ast::is_array_binding_pattern(n) {
            return n
                .parent
                .is_some_and(|p| ast::is_variable_declaration(&nodes[p]));
        }
        true
    })
}

/// `findBestFittingNode` walks up from the token to find the node that best
/// fits the diagnostic span.
fn find_best_fitting_node(
    nodes: &[Node],
    node: Option<NodeId>,
    span: TextRange,
) -> Option<NodeId> {
    let mut node = node?;
    while nodes[node].end() < span.pos() + span.len() {
        node = nodes[node].parent?;
    }
    while let Some(parent) = nodes[node].parent {
        if nodes[parent].pos() == nodes[node].pos()
            && nodes[parent].end() == nodes[node].end()
        {
            node = parent;
        } else {
            break;
        }
    }
    if ast::is_identifier(&nodes[node])
        && nodes[node]
            .parent
            .is_some_and(|p| ast::has_initializer(&nodes[p]) && nodes[p].initializer().is_some())
    {
        return nodes[node].parent.and_then(|p| nodes[p].initializer());
    }
    if ast::is_identifier(&nodes[node])
        && nodes[node]
            .parent
            .is_some_and(|p| ast::is_shorthand_property_assignment(&nodes[p]))
    {
        return nodes[node].parent;
    }
    Some(node)
}

/// `isNamedDeclarationKind` matches TS's isDeclarationKind, which is
/// narrower than Go's IsDeclaration. Go's IsDeclaration returns true for
/// any node with DeclarationData (including CallExpression), while TS's
/// isDeclaration only returns true for specific named declaration kinds.
fn is_named_declaration_kind(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::ArrowFunction
            | Kind::BindingElement
            | Kind::ClassDeclaration
            | Kind::ClassExpression
            | Kind::ClassStaticBlockDeclaration
            | Kind::Constructor
            | Kind::EnumDeclaration
            | Kind::EnumMember
            | Kind::ExportSpecifier
            | Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::GetAccessor
            | Kind::ImportClause
            | Kind::ImportEqualsDeclaration
            | Kind::ImportSpecifier
            | Kind::InterfaceDeclaration
            | Kind::JsxAttribute
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::ModuleDeclaration
            | Kind::NamespaceExportDeclaration
            | Kind::NamespaceImport
            | Kind::NamespaceExport
            | Kind::Parameter
            | Kind::PropertyAssignment
            | Kind::PropertyDeclaration
            | Kind::PropertySignature
            | Kind::SetAccessor
            | Kind::ShorthandPropertyAssignment
            | Kind::TypeAliasDeclaration
            | Kind::TypeParameter
            | Kind::VariableDeclaration
            | Kind::JSDocTypedefTag
            | Kind::JSDocCallbackTag
            | Kind::JSDocPropertyTag
            | Kind::NamedTupleMember
    )
}

/// `isValueSignatureDeclaration` checks if a node is a function-like
/// declaration that produces a value.
fn is_value_signature_declaration(node: &Node) -> bool {
    ast::is_function_expression(node)
        || ast::is_arrow_function(node)
        || ast::is_method_declaration(node)
        || ast::is_accessor(node)
        || ast::is_function_declaration(node)
        || ast::is_constructor_declaration(node)
}

/// `getIdentifierNameForNode` derives a meaningful variable name from a
/// node expression. For property access expressions like `obj.foo`,
/// returns "foo". Otherwise returns "newLocal". Ported from TS's
/// getIdentifierForNode in services/refactors/helpers.ts.
fn get_identifier_name_for_node(nodes: &[Node], node: NodeId) -> String {
    if ast::is_property_access_expression(&nodes[node]) {
        if let Some(name) = nodes[node].as_property_access_expression().name {
            if ast::is_identifier(&nodes[name])
                && !ast::is_private_identifier(&nodes[name])
                && scanner::utilities::identifier_to_keyword_kind(nodes[name].as_identifier())
                    == Kind::Unknown
            {
                return nodes[name].text(nodes).into_owned();
            }
        }
    }
    "newLocal".to_string()
}

/// `(c *Checker) TypeToTypeNodeEx` variant that also returns the filled
/// `id_to_symbol` map — the public `type_to_type_node_ex` consumes the map,
/// so the Go pattern of sharing `idToSymbol` with
/// `autoimport.TryGetAutoImportableReferenceFromTypeNode` is reproduced by
/// mirroring `printer_util.rs` and taking the map back out of the builder.
fn type_to_type_node_ex_with_map(
    c: &Rc<RefCell<Checker>>,
    t: TypeId,
    enclosing_declaration: Option<NodeId>,
    flags: nodebuilder::Flags,
    internal_flags: nodebuilder::InternalFlags,
) -> (Option<NodeId>, FxHashMap<NodeId, SymbolId>) {
    let mut cb = c.borrow_mut();
    let mut node_builder = cb.get_node_builder_ex(FxHashMap::default());
    let file_index = enclosing_declaration
        .map(|d| d.file_index())
        .unwrap_or_else(|| {
            node_builder
                .impl_
                .as_ref()
                .expect("NodeBuilder without impl")
                .f
                .file_index()
        });
    let program = cb.program.clone().expect("program");
    let (file_index, arena_cell) = program.nodes_handle_or_fallback(file_index);
    node_builder
        .impl_
        .as_mut()
        .expect("NodeBuilder without impl")
        .f
        .set_file_index(file_index);
    let mut nodes = ArenaCheckout::new(arena_cell);
    let type_node = node_builder.type_to_type_node(
        &mut cb,
        &mut nodes,
        t,
        enclosing_declaration,
        flags,
        internal_flags,
        None,
    );
    let id_to_symbol = node_builder
        .impl_
        .as_mut()
        .map(|i| std::mem::take(&mut i.id_to_symbol))
        .unwrap_or_default();
    (type_node, id_to_symbol)
}
