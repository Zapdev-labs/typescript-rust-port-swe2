// Ported from tsc/internal/transformers/estransforms/using.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `newUsingDeclarationTransformer` — downlevels `using`/`await using`
// declarations (explicit resource management) for ES2025 and earlier.
//
// PORT notes: see `mod.rs` and `async.rs` — same `Rc<State>` + `txv`
// (synthesized `tx.Visitor()` equivalent) + `ec_visit_*` hook conventions.
// The `topLevelStatements *[]*ast.Statement` out-parameter of
// `transformUsingDeclarations` is modeled as `Option<&RefCell<Vec<NodeId>>>`.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeFlags, NodeId, SubtreeFacts};
use tsc_printer::{AutoGenerateOptions, EmitFlags, GeneratedIdentifierFlags};

use super::{Ec, make_transformer, subtree_facts};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;
use crate::utilities as transformer_utilities;

/// `type usingDeclarationTransformer struct`.
pub(crate) struct UsingDeclarationTransformer {
    export_bindings: RefCell<Option<HashMap<String, NodeId>>>,
    export_binding_names: RefCell<Vec<String>>,
    export_vars: RefCell<Vec<NodeId>>,
    default_export_binding: Cell<Option<NodeId>>,
    export_equals_binding: Cell<Option<NodeId>>,
}

/// `type usingKind uint` — ordering matters (`usingKind > result`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum UsingKind {
    None,
    Sync,
    Async,
}

impl UsingDeclarationTransformer {
    /// A `NodeVisitor` equivalent to `tx.Visitor()` (see `async.rs` PORT note).
    fn txv<'a>(self: &Rc<Self>, ec: &Ec) -> NodeVisitor<'a>
    where
        Self: 'a,
    {
        let state = self.clone();
        let ec2 = ec.clone();
        ec.borrow().new_node_visitor(Box::new(
            move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec2, _v, cx, node)
            },
        ))
    }

    /// `(tx *usingDeclarationTransformer) visit`.
    pub(crate) fn visit(
        self: &Rc<Self>,
        ec: &Ec,
        _v: &NodeVisitor<'_>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if subtree_facts(cx, node) & SubtreeFacts::CONTAINS_USING == SubtreeFacts::NONE {
            return Some(node);
        }

        let node = match cx.nodes[node].kind {
            Kind::SourceFile => self.visit_source_file(ec, cx, node),
            Kind::Block => self.visit_block(ec, cx, node),
            Kind::ForStatement => self.visit_for_statement(ec, cx, node),
            Kind::ForOfStatement => self.visit_for_of_statement(ec, cx, node),
            _ => self.txv(ec).visit_each_child(cx, node).unwrap_or(node),
        };
        Some(node)
    }

    /// `(tx *usingDeclarationTransformer) visitSourceFile`.
    fn visit_source_file(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if cx.nodes[node].as_source_file().is_declaration_file {
            return node;
        }

        let visited;
        let statements: Vec<NodeId> = cx.nodes[node]
            .as_source_file()
            .statements
            .as_ref()
            .map(|l| l.nodes.to_vec())
            .unwrap_or_default();
        let using_kind = get_using_kind_of_statements(cx, &statements);
        if using_kind != UsingKind::None {
            // Imports and exports must stay at the top level. This means we must hoist all imports, exports, and
            // top-level function declarations and bindings out of the `try` statements we generate. For example:
            //
            // given:
            //
            //  import { w } from "mod";
            //  const x = expr1;
            //  using y = expr2;
            //  const z = expr3;
            //  export function f() {
            //    console.log(z);
            //  }
            //
            // produces:
            //
            //  import { x } from "mod";        // <-- preserved
            //  const x = expr1;                // <-- preserved
            //  var y, z;                       // <-- hoisted
            //  export function f() {           // <-- hoisted
            //    console.log(z);
            //  }
            //  const env_1 = { stack: [], error: void 0, hasError: false };
            //  try {
            //    y = __addDisposableResource(env_1, expr2, false);
            //    z = expr3;
            //  }
            //  catch (e_1) {
            //    env_1.error = e_1;
            //    env_1.hasError = true;
            //  }
            //  finally {
            //    __disposeResource(env_1);
            //  }
            //
            // In this transformation, we hoist `y`, `z`, and `f` to a new outer statement list while moving all
            // other statements in the source file into the `try` block, which is the same approach we use for
            // System module emit. Unlike System module emit, we attempt to preserve all statements prior to the
            // first top-level `using` to isolate the complexity of the transformed output to only where it is
            // necessary.
            ec.borrow_mut().start_variable_environment();

            *self.export_bindings.borrow_mut() = Some(HashMap::new());
            *self.export_vars.borrow_mut() = Vec::new();

            let (prologue, rest) = ec
                .borrow()
                .factory
                .split_standard_prologue(cx.nodes, &statements);
            let (prologue, rest) = (prologue.to_vec(), rest.to_vec());
            let top_level_statements = RefCell::new(Vec::<NodeId>::new());
            let txv = self.txv(ec);
            let visited_prologue = txv
                .visit_slice(cx, &prologue)
                .unwrap_or_else(|| prologue.clone());
            top_level_statements.borrow_mut().extend(visited_prologue);

            // Collect and transform any leading statements up to the first `using` or `await using`. This preserves
            // the original statement order much as is possible.

            let mut pos = 0usize;
            while pos < rest.len() {
                let statement = rest[pos];
                if get_using_kind(cx, statement) != UsingKind::None {
                    if pos > 0 {
                        let visited = txv
                            .visit_slice(cx, &rest[..pos])
                            .unwrap_or_else(|| rest[..pos].to_vec());
                        top_level_statements.borrow_mut().extend(visited);
                    }
                    break;
                }
                pos += 1;
            }

            assert!(
                pos < rest.len(),
                "Should have encountered at least one 'using' statement."
            );

            // transform the rest of the body
            let env_binding = self.create_env_binding(ec, cx);
            let body_statements = self.transform_using_declarations(
                ec,
                cx,
                &rest[pos..],
                env_binding,
                Some(&top_level_statements),
            );

            // add `export {}` declarations for any hoisted bindings.
            if self
                .export_bindings
                .borrow()
                .as_ref()
                .is_some_and(|b| !b.is_empty())
            {
                let mut export_specifiers: Vec<NodeId> =
                    Vec::with_capacity(self.export_binding_names.borrow().len());
                for name in self.export_binding_names.borrow().iter() {
                    let specifier = self
                        .export_bindings
                        .borrow()
                        .as_ref()
                        .and_then(|b| b.get(name).copied())
                        .expect("Missing export binding for hoisted export name");
                    export_specifiers.push(specifier);
                }
                let specifier_list = ec.borrow_mut().factory.new_node_list(export_specifiers);
                let named_exports = ec
                    .borrow_mut()
                    .factory
                    .new_named_exports(cx.nodes, Some(specifier_list));
                let export_declaration = ec.borrow_mut().factory.new_export_declaration(
                    cx.nodes,
                    None,  /*modifiers*/
                    false, /*is_type_only*/
                    Some(named_exports),
                    None, /*module_specifier*/
                    None, /*attributes*/
                );
                top_level_statements.borrow_mut().push(export_declaration);
            }

            let env_statements = ec.borrow_mut().end_variable_environment(cx.nodes);
            top_level_statements.borrow_mut().extend(env_statements);
            let export_vars = self.export_vars.borrow().clone();
            if !export_vars.is_empty() {
                let export_modifier = ec
                    .borrow_mut()
                    .factory
                    .new_token(cx.nodes, Kind::ExportKeyword);
                let modifier_list = ec
                    .borrow()
                    .factory
                    .new_modifier_list(cx.nodes, [export_modifier]);
                let var_decls = ec.borrow_mut().factory.new_node_list(export_vars);
                let var_decl_list = ec.borrow_mut().factory.new_variable_declaration_list(
                    cx.nodes,
                    Some(var_decls),
                    NodeFlags::LET,
                );
                let var_statement = ec.borrow_mut().factory.new_variable_statement(
                    cx.nodes,
                    Some(modifier_list),
                    Some(var_decl_list),
                );
                top_level_statements.borrow_mut().push(var_statement);
            }
            let downlevel = self.create_downlevel_using_statements(
                ec,
                cx,
                body_statements,
                env_binding,
                using_kind == UsingKind::Async,
            );
            top_level_statements.borrow_mut().extend(downlevel);

            if let Some(export_equals_binding) = self.export_equals_binding.get() {
                let export_assignment = ec.borrow_mut().factory.new_export_assignment(
                    cx.nodes,
                    None, /*modifiers*/
                    true, /*is_export_equals*/
                    None, /*type_node*/
                    Some(export_equals_binding),
                );
                top_level_statements.borrow_mut().push(export_assignment);
            }

            let top_level = top_level_statements.into_inner();
            let statement_list = ec.borrow_mut().factory.new_node_list(top_level);
            let end_of_file_token = cx.nodes[node].as_source_file().end_of_file_token;
            visited = ec
                .borrow_mut()
                .factory
                .update_source_file(cx.nodes, node, Some(statement_list), end_of_file_token)
                .unwrap_or(node);
        } else {
            visited = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
        }
        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(visited, &helpers);
        *self.export_vars.borrow_mut() = Vec::new();
        *self.export_bindings.borrow_mut() = None;
        self.export_binding_names.borrow_mut().clear();
        self.default_export_binding.set(None);
        self.export_equals_binding.set(None);
        visited
    }

    /// `(tx *usingDeclarationTransformer) visitBlock`.
    fn visit_block(self: &Rc<Self>, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let statements: Vec<NodeId> = cx.nodes[node]
            .as_block()
            .statements
            .as_ref()
            .map(|l| l.nodes.to_vec())
            .unwrap_or_default();
        let using_kind = get_using_kind_of_statements(cx, &statements);
        if using_kind != UsingKind::None {
            let (prologue, rest) = ec
                .borrow()
                .factory
                .split_standard_prologue(cx.nodes, &statements);
            let (prologue, rest) = (prologue.to_vec(), rest.to_vec());
            let env_binding = self.create_env_binding(ec, cx);
            let mut statements = Vec::with_capacity(prologue.len() + 2);
            let visited_prologue = self
                .txv(ec)
                .visit_slice(cx, &prologue)
                .unwrap_or_else(|| prologue.clone());
            statements.extend(visited_prologue);
            let body_statements =
                self.transform_using_declarations(ec, cx, &rest, env_binding, None);
            statements.extend(self.create_downlevel_using_statements(
                ec,
                cx,
                body_statements,
                env_binding,
                using_kind == UsingKind::Async,
            ));
            let mut statement_list = ec.borrow_mut().factory.new_node_list(statements);
            statement_list.loc = cx.nodes[node]
                .as_block()
                .statements
                .as_ref()
                .map(|l| l.loc)
                .unwrap_or_default();
            let multi_line = cx.nodes[node].as_block().multi_line;
            return ec
                .borrow_mut()
                .factory
                .update_block(cx.nodes, node, Some(statement_list), multi_line)
                .unwrap_or(node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `(tx *usingDeclarationTransformer) visitForStatement`.
    fn visit_for_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (initializer, condition, incrementor, statement) = {
            let d = cx.nodes[node].as_for_statement();
            (
                d.initializer,
                d.condition,
                d.incrementor,
                d.iteration_statement_base.statement,
            )
        };
        if let Some(initializer) = initializer
            && is_using_variable_declaration_list(cx, initializer)
        {
            // given:
            //
            //  for (using x = expr; cond; incr) { ... }
            //
            // produces a shallow transformation to:
            //
            //  {
            //    using x = expr;
            //    for (; cond; incr) { ... }
            //  }
            //
            // before handing the shallow transformation back to the visitor for an in-depth transformation.
            let var_statement = ec.borrow_mut().factory.new_variable_statement(
                cx.nodes,
                None, /*modifiers*/
                Some(initializer),
            );
            let updated_for = ec
                .borrow_mut()
                .factory
                .update_for_statement(
                    cx.nodes,
                    node,
                    None, /*initializer*/
                    condition,
                    incrementor,
                    statement,
                )
                .unwrap_or(node);
            let stmt_list = ec
                .borrow_mut()
                .factory
                .new_node_list([var_statement, updated_for]);
            let block = ec.borrow_mut().factory.new_block(
                cx.nodes,
                Some(stmt_list),
                false, /*multi_line*/
            );
            return self.txv(ec).visit_node(cx, Some(block)).unwrap_or(block);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `(tx *usingDeclarationTransformer) visitForOfStatement`.
    fn visit_for_of_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (await_modifier, initializer, expression, statement) = {
            let d = cx.nodes[node].as_for_in_or_of_statement();
            (d.await_modifier, d.initializer, d.expression, d.statement)
        };
        if let Some(initializer) = initializer
            && is_using_variable_declaration_list(cx, initializer)
        {
            // given:
            //
            //  for (using x of y) { ... }
            //
            // produces a shallow transformation to:
            //
            //  for (const x_1 of y) {
            //    using x = x;
            //    ...
            //  }
            //
            // before handing the shallow transformation back to the visitor for an in-depth transformation.
            let declarations: Vec<NodeId> = cx.nodes[initializer]
                .as_variable_declaration_list()
                .declarations
                .as_ref()
                .map(|l| l.nodes.to_vec())
                .unwrap_or_default();
            let mut for_decl = declarations.first().copied();
            if for_decl.is_none() {
                let temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                for_decl = Some(ec.borrow_mut().factory.new_variable_declaration(
                    cx.nodes,
                    Some(temp),
                    None,
                    None,
                    None,
                ));
            }
            let for_decl = for_decl.expect("for declaration");

            let is_await_using =
                get_using_kind_of_variable_declaration_list(cx, initializer) == UsingKind::Async;
            let for_decl_name = cx.nodes[for_decl].name().expect("for declaration name");
            let temp = ec
                .borrow_mut()
                .factory
                .new_generated_name_for_node(cx.nodes, for_decl_name);
            let using_var = ec
                .borrow_mut()
                .factory
                .update_variable_declaration(
                    cx.nodes,
                    for_decl,
                    Some(for_decl_name),
                    None, /*exclamation_token*/
                    None, /*type*/
                    Some(temp),
                )
                .unwrap_or(for_decl);
            let using_var_decls = ec.borrow_mut().factory.new_node_list([using_var]);
            let using_var_list = ec.borrow_mut().factory.new_variable_declaration_list(
                cx.nodes,
                Some(using_var_decls),
                if is_await_using {
                    NodeFlags::AWAIT_USING
                } else {
                    NodeFlags::USING
                },
            );
            let using_var_statement = ec.borrow_mut().factory.new_variable_statement(
                cx.nodes,
                None, /*modifiers*/
                Some(using_var_list),
            );
            let new_statement = if ast::is_block(&cx.nodes[statement.expect("for-of body")]) {
                let body = statement.expect("for-of body");
                let mut statements: Vec<NodeId> = Vec::with_capacity(
                    cx.nodes[body].statements().map(|s| s.len()).unwrap_or(0) + 1,
                );
                statements.push(using_var_statement);
                if let Some(existing) = cx.nodes[body].statements() {
                    statements.extend(existing.iter().copied());
                }
                let stmt_list = ec.borrow_mut().factory.new_node_list(statements);
                let multi_line = cx.nodes[body].as_block().multi_line;
                ec.borrow_mut()
                    .factory
                    .update_block(cx.nodes, body, Some(stmt_list), multi_line)
                    .unwrap_or(body)
            } else {
                let stmt_list = ec
                    .borrow_mut()
                    .factory
                    .new_node_list([using_var_statement, statement.expect("for-of body")]);
                ec.borrow_mut().factory.new_block(
                    cx.nodes,
                    Some(stmt_list),
                    true, /*multi_line*/
                )
            };
            let temp_decl = ec.borrow_mut().factory.new_variable_declaration(
                cx.nodes,
                Some(temp),
                None, /*exclamation_token*/
                None, /*type*/
                None,
            );
            let temp_decls = ec.borrow_mut().factory.new_node_list([temp_decl]);
            let temp_list = ec.borrow_mut().factory.new_variable_declaration_list(
                cx.nodes,
                Some(temp_decls),
                NodeFlags::CONST,
            );
            let updated = ec
                .borrow_mut()
                .factory
                .update_for_in_or_of_statement(
                    cx.nodes,
                    node,
                    await_modifier,
                    Some(temp_list),
                    expression,
                    Some(new_statement),
                )
                .unwrap_or(node);
            return self
                .txv(ec)
                .visit_node(cx, Some(updated))
                .unwrap_or(updated);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `hoist` — the closure inside `transformUsingDeclarations`.
    fn hoist(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        top_level_statements: Option<&RefCell<Vec<NodeId>>>,
    ) -> Option<NodeId> {
        let Some(top_level_statements) = top_level_statements else {
            return Some(node);
        };

        match cx.nodes[node].kind {
            Kind::ImportDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::ExportDeclaration
            | Kind::FunctionDeclaration => {
                self.hoist_import_or_export_or_hoisted_declaration(node, top_level_statements);
                None
            }
            Kind::ExportAssignment => self.hoist_export_assignment(ec, cx, node),
            Kind::ClassDeclaration => self.hoist_class_declaration(ec, cx, node),
            Kind::VariableStatement => self.hoist_variable_statement(ec, cx, node),
            _ => Some(node),
        }
    }

    /// `(tx *usingDeclarationTransformer) transformUsingDeclarations`.
    fn transform_using_declarations(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        statements_in: &[NodeId],
        env_binding: NodeId,
        top_level_statements: Option<&RefCell<Vec<NodeId>>>,
    ) -> Vec<NodeId> {
        let mut statements: Vec<NodeId> = Vec::new();

        macro_rules! hoist_or_append_node {
            ($cx:expr, $node:expr) => {
                if let Some(node) = self.hoist(ec, $cx, $node, top_level_statements) {
                    statements.push(node);
                }
            };
        }

        for &statement in statements_in {
            let using_kind = get_using_kind(cx, statement);
            if using_kind != UsingKind::None {
                let declaration_list = cx.nodes[statement].as_variable_statement().declaration_list;
                let declaration_list = declaration_list.expect("variable statement decl list");
                let declaration_ids: Vec<NodeId> = cx.nodes[declaration_list]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .map(|l| l.nodes.to_vec())
                    .unwrap_or_default();
                let mut declarations: Vec<NodeId> = Vec::new();
                for &declaration in &declaration_ids {
                    let declaration = {
                        let name = cx.nodes[declaration].name();
                        if !name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
                            // Since binding patterns are a grammar error, we reset `declarations` so we don't
                            // process this as a `using`.
                            declarations.clear();
                            break;
                        }

                        // perform a shallow transform for any named evaluation
                        if super::namedevaluation::is_named_evaluation(
                            &ec.borrow(),
                            cx.nodes,
                            declaration,
                        ) {
                            super::namedevaluation::transform_named_evaluation(
                                ec,
                                cx,
                                declaration,
                                false, /*ignore_empty_string_literal*/
                                "",    /*assigned_name*/
                            )
                        } else {
                            declaration
                        }
                    };

                    let initializer = cx.nodes[declaration].initializer();
                    let initializer = match self.txv(ec).visit_node(cx, initializer) {
                        Some(i) => i,
                        None => ec.borrow_mut().factory.new_void_zero_expression(cx.nodes),
                    };
                    let decl_name = cx.nodes[declaration].name();
                    let helper = ec.borrow_mut().factory.new_add_disposable_resource_helper(
                        cx.nodes,
                        env_binding,
                        initializer,
                        using_kind == UsingKind::Async,
                    );
                    let updated = ec
                        .borrow_mut()
                        .factory
                        .update_variable_declaration(
                            cx.nodes,
                            declaration,
                            decl_name,
                            None, /*exclamation_token*/
                            None, /*type*/
                            Some(helper),
                        )
                        .unwrap_or(declaration);
                    declarations.push(updated);
                }

                // Only replace the statement if it was valid.
                if !declarations.is_empty() {
                    let decls = ec.borrow_mut().factory.new_node_list(declarations);
                    let var_list = ec.borrow_mut().factory.new_variable_declaration_list(
                        cx.nodes,
                        Some(decls),
                        NodeFlags::CONST,
                    );
                    ec.borrow().set_original(var_list, declaration_list);
                    cx.nodes[var_list].loc = cx.nodes[declaration_list].loc;
                    let updated_statement = ec
                        .borrow_mut()
                        .factory
                        .update_variable_statement(
                            cx.nodes,
                            statement,
                            None, /*modifiers*/
                            Some(var_list),
                        )
                        .unwrap_or(statement);
                    hoist_or_append_node!(cx, updated_statement);
                    continue;
                }
            }

            if let Some(result) = self.visit(ec, &self.txv(ec), cx, statement) {
                if cx.nodes[result].kind == Kind::SyntaxList {
                    for i in 0..cx.nodes[result].as_syntax_list().children.len() {
                        let child = cx.nodes[result].as_syntax_list().children[i];
                        hoist_or_append_node!(cx, child);
                    }
                } else {
                    hoist_or_append_node!(cx, result);
                }
            }
        }
        statements
    }

    /// `hoistImportOrExportOrHoistedDeclaration`.
    fn hoist_import_or_export_or_hoisted_declaration(
        &self,
        node: NodeId,
        top_level_statements: &RefCell<Vec<NodeId>>,
    ) {
        // NOTE: `node` has already been visited
        top_level_statements.borrow_mut().push(node);
    }

    /// `hoistExportAssignment`.
    fn hoist_export_assignment(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].as_export_assignment().is_export_equals {
            self.hoist_export_equals(ec, cx, node)
        } else {
            self.hoist_export_default(ec, cx, node)
        }
    }

    /// `hoistExportDefault`.
    fn hoist_export_default(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // NOTE: `node` has already been visited
        if self.default_export_binding.get().is_some() {
            // invalid case of multiple `export default` declarations. Don't assert here, just pass it through
            return Some(node);
        }

        // given:
        //
        //   export default expr;
        //
        // produces:
        //
        //   // top level
        //   var default_1;
        //   export { default_1 as default };
        //
        //   // body
        //   default_1 = expr;

        let options = AutoGenerateOptions {
            flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES
                | GeneratedIdentifierFlags::FILE_LEVEL
                | GeneratedIdentifierFlags::OPTIMISTIC,
            ..Default::default()
        };
        let default_binding = ec
            .borrow_mut()
            .factory
            .new_unique_name_ex(cx.nodes, "_default", &options);
        self.default_export_binding.set(Some(default_binding));
        let default_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "default");
        self.hoist_binding_identifier(
            ec,
            cx,
            default_binding,
            true, /*is_export*/
            Some(default_ident),
            Some(node),
        );

        // give a class or function expression an assigned name, if needed.
        let expression = cx.nodes[node].as_export_assignment().expression;
        let mut expression = expression.expect("export assignment expression");
        let mut inner_expression =
            ast::skip_outer_expressions(expression, ast::outer_expression_kinds::ALL, cx.nodes);
        if super::namedevaluation::is_named_evaluation(&ec.borrow(), cx.nodes, inner_expression) {
            inner_expression = super::namedevaluation::transform_named_evaluation(
                ec,
                cx,
                inner_expression,
                false, /*ignore_empty_string_literal*/
                "default",
            );
            expression = ec.borrow_mut().factory.restore_outer_expressions(
                cx.nodes,
                Some(expression),
                inner_expression,
                ast::outer_expression_kinds::ALL,
            );
        }

        let assignment = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            default_binding,
            expression,
        );
        Some(
            ec.borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, Some(assignment)),
        )
    }

    /// `hoistExportEquals`.
    fn hoist_export_equals(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // NOTE: `node` has already been visited
        if self.export_equals_binding.get().is_some() {
            // invalid case of multiple `export default` declarations. Don't assert here, just pass it through
            return Some(node);
        }

        // given:
        //
        //   export = expr;
        //
        // produces:
        //
        //   // top level
        //   var default_1;
        //
        //   try {
        //       // body
        //       default_1 = expr;
        //   } ...
        //
        //   // top level suffix
        //   export = default_1;

        let options = AutoGenerateOptions {
            flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES
                | GeneratedIdentifierFlags::FILE_LEVEL
                | GeneratedIdentifierFlags::OPTIMISTIC,
            ..Default::default()
        };
        let export_equals_binding = ec
            .borrow_mut()
            .factory
            .new_unique_name_ex(cx.nodes, "_default", &options);
        self.export_equals_binding.set(Some(export_equals_binding));
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, export_equals_binding);

        // give a class or function expression an assigned name, if needed.
        let expression = cx.nodes[node].as_export_assignment().expression;
        let assignment = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            export_equals_binding,
            expression.expect("export assignment expression"),
        );
        Some(
            ec.borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, Some(assignment)),
        )
    }

    /// `hoistClassDeclaration`.
    fn hoist_class_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // NOTE: `node` has already been visited
        if cx.nodes[node].name().is_none() && self.default_export_binding.get().is_some() {
            // invalid case of multiple `export default` declarations. Don't assert here, just pass it through
            return Some(node);
        }

        let is_exported = ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT);
        let is_default = ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::DEFAULT);

        // When hoisting a class declaration at the top level of a file containing a top-level `using` statement, we
        // must first convert it to a class expression so that we can hoist the binding outside of the `try`.
        let mut expression =
            super::utilities::convert_class_declaration_to_class_expression(ec, cx, node);
        if cx.nodes[node].name().is_some() {
            // given:
            //
            //  using x = expr;
            //  class C {}
            //
            // produces:
            //
            //  var x, C;
            //  const env_1 = { ... };
            //  try {
            //    x = __addDisposableResource(env_1, expr, false);
            //    C = class {};
            //  }
            //  catch (e_1) {
            //    env_1.error = e_1;
            //    env_1.hasError = true;
            //  }
            //  finally {
            //    __disposeResources(env_1);
            //  }
            //
            // If the class is exported, we also produce an `export { C };`
            let local_name = ec.borrow_mut().factory.get_local_name(cx.nodes, Some(node));
            self.hoist_binding_identifier(
                ec,
                cx,
                local_name,
                is_exported && !is_default,
                None, /*export_alias*/
                Some(node),
            );
            let declaration_name = ec
                .borrow_mut()
                .factory
                .get_declaration_name(cx.nodes, Some(node));
            expression = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                declaration_name,
                expression,
            );
            ec.borrow().set_original(expression, node);
            ec.borrow()
                .set_source_map_range(expression, cx.nodes[node].loc);
            ec.borrow()
                .set_comment_range(expression, cx.nodes[node].loc);
            if super::namedevaluation::is_named_evaluation(&ec.borrow(), cx.nodes, expression) {
                expression = super::namedevaluation::transform_named_evaluation(
                    ec, cx, expression, false, /*ignore_empty_string_literal*/
                    "",    /*assigned_name*/
                );
            }
        }

        if is_default && self.default_export_binding.get().is_none() {
            // In the case of a default export, we create a temporary variable that we export as the default and
            // then assign to that variable.
            //
            // given:
            //
            //  using x = expr;
            //  export default class C {}
            //
            // produces:
            //
            //  export { default_1 as default };
            //  var x, C, default_1;
            //  const env_1 = { ... };
            //  try {
            //    x = __addDisposableResource(env_1, expr, false);
            //    default_1 = C = class {};
            //  }
            //  catch (e_1) {
            //    env_1.error = e_1;
            //    env_1.hasError = true;
            //  }
            //  finally {
            //    __disposeResources(env_1);
            //  }
            //
            // Though we will never reassign `default_1`, this most closely matches the specified runtime
            // semantics.
            let options = AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES
                    | GeneratedIdentifierFlags::FILE_LEVEL
                    | GeneratedIdentifierFlags::OPTIMISTIC,
                ..Default::default()
            };
            let default_binding = ec
                .borrow_mut()
                .factory
                .new_unique_name_ex(cx.nodes, "_default", &options);
            self.default_export_binding.set(Some(default_binding));
            let default_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "default");
            self.hoist_binding_identifier(
                ec,
                cx,
                default_binding,
                true, /*is_export*/
                Some(default_ident),
                Some(node),
            );
            expression = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                default_binding,
                expression,
            );
            ec.borrow().set_original(expression, node);
            if super::namedevaluation::is_named_evaluation(&ec.borrow(), cx.nodes, expression) {
                expression = super::namedevaluation::transform_named_evaluation(
                    ec, cx, expression, false, /*ignore_empty_string_literal*/
                    "default",
                );
            }
        }

        Some(
            ec.borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, Some(expression)),
        )
    }

    /// `hoistVariableStatement`.
    fn hoist_variable_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // NOTE: `node` has already been visited
        let mut expressions: Vec<NodeId> = Vec::new();
        let is_exported = ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT);
        let declaration_list = cx.nodes[node].as_variable_statement().declaration_list;
        let variables: Vec<NodeId> = declaration_list
            .and_then(|l| {
                cx.nodes[l]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .map(|d| d.nodes.to_vec())
            })
            .unwrap_or_default();
        for variable in variables {
            self.hoist_binding_element(ec, cx, variable, is_exported, variable);
            if cx.nodes[variable].initializer().is_some() {
                expressions.push(self.hoist_initialized_variable(ec, cx, variable));
            }
        }
        if !expressions.is_empty() {
            let inlined = ec
                .borrow_mut()
                .factory
                .inline_expressions(cx.nodes, &expressions);
            let statement = ec
                .borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, inlined);
            ec.borrow().set_original(statement, node);
            ec.borrow().set_comment_range(statement, cx.nodes[node].loc);
            ec.borrow()
                .set_source_map_range(statement, cx.nodes[node].loc);
            return Some(statement);
        }
        None
    }

    /// `hoistInitializedVariable`.
    fn hoist_initialized_variable(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // NOTE: `node` has already been visited
        let initializer = cx.nodes[node]
            .as_variable_declaration()
            .initializer
            .expect("Expected initializer");
        let name = cx.nodes[node].name().expect("declaration name");
        let target = if ast::is_identifier(&cx.nodes[name]) {
            let target = ec.borrow_mut().factory.clone_node(cx.nodes, name);
            let flags =
                ec.borrow().emit_flags(target) & !(EmitFlags::LOCAL_NAME | EmitFlags::EXPORT_NAME);
            ec.borrow().set_emit_flags(target, flags);
            target
        } else {
            transformer_utilities::convert_binding_pattern_to_assignment_pattern(
                &mut ec.borrow_mut(),
                cx.nodes,
                name,
            )
        };

        let assignment =
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, target, initializer);
        ec.borrow().set_original(assignment, node);
        ec.borrow()
            .set_comment_range(assignment, cx.nodes[node].loc);
        ec.borrow()
            .set_source_map_range(assignment, cx.nodes[node].loc);
        assignment
    }

    /// `hoistBindingElement` — `node` is a `VariableDeclaration|BindingElement`.
    fn hoist_binding_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        is_exported_declaration: bool,
        original: NodeId,
    ) {
        // NOTE: `node` has already been visited
        let name = cx.nodes[node].name().expect("declaration name");
        if ast::is_binding_pattern(&cx.nodes[name]) {
            let elements: Vec<NodeId> = cx.nodes[name]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default();
            for element in elements {
                if cx.nodes[element].name().is_some() {
                    self.hoist_binding_element(ec, cx, element, is_exported_declaration, original);
                }
            }
        } else {
            self.hoist_binding_identifier(
                ec,
                cx,
                name,
                is_exported_declaration,
                None, /*export_alias*/
                Some(original),
            );
        }
    }

    /// `hoistBindingIdentifier` — `node` is an `Identifier`.
    fn hoist_binding_identifier(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        is_export: bool,
        export_alias: Option<NodeId>,
        original: Option<NodeId>,
    ) {
        // NOTE: `node` has already been visited
        let mut name = node;
        if !transformer_utilities::is_generated_identifier(&ec.borrow(), node) {
            name = ec.borrow_mut().factory.clone_node(cx.nodes, name);
        }
        if is_export {
            if export_alias.is_none() && !transformer_utilities::is_local_name(&ec.borrow(), name) {
                let var_decl = ec.borrow_mut().factory.new_variable_declaration(
                    cx.nodes,
                    Some(name),
                    None, /*exclamation_token*/
                    None, /*type*/
                    None, /*initializer*/
                );
                if let Some(original) = original {
                    ec.borrow().set_original(var_decl, original);
                }
                self.export_vars.borrow_mut().push(var_decl);
                return;
            }

            let (local_name, export_name) = if let Some(export_alias) = export_alias {
                (Some(name), Some(export_alias))
            } else {
                (None, Some(name))
            };
            let specifier = ec.borrow_mut().factory.new_export_specifier(
                cx.nodes,
                /*is_type_only*/ false,
                local_name,
                export_name,
            );
            if let Some(original) = original {
                ec.borrow().set_original(specifier, original);
            }
            if self.export_bindings.borrow().is_none() {
                *self.export_bindings.borrow_mut() = Some(HashMap::new());
            }
            let text = cx.nodes[name].as_identifier().text.clone();
            if !self
                .export_bindings
                .borrow()
                .as_ref()
                .is_some_and(|b| b.contains_key(&text))
            {
                self.export_binding_names.borrow_mut().push(text.clone());
            }
            self.export_bindings
                .borrow_mut()
                .as_mut()
                .expect("export bindings initialized")
                .insert(text, specifier);
        }
        ec.borrow_mut().add_variable_declaration(cx.nodes, name);
    }

    /// `createEnvBinding`.
    fn create_env_binding(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>) -> NodeId {
        ec.borrow_mut().factory.new_unique_name(cx.nodes, "env")
    }

    /// `createDownlevelUsingStatements`.
    fn create_downlevel_using_statements(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        body_statements: Vec<NodeId>,
        env_binding: NodeId,
        async_: bool,
    ) -> Vec<NodeId> {
        let mut statements: Vec<NodeId> = Vec::with_capacity(2);

        // produces:
        //
        //  const env_1 = { stack: [], error: void 0, hasError: false };
        //
        let stack_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "stack");
        let empty_array = ec
            .borrow_mut()
            .factory
            .new_array_literal_expression(cx.nodes, None, false /*multi_line*/);
        let stack_prop = ec.borrow_mut().factory.new_property_assignment(
            cx.nodes,
            None, /*modifiers*/
            Some(stack_ident),
            None, /*postfix_token*/
            None, /*type_node*/
            Some(empty_array),
        );
        let error_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "error");
        let void_zero = ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
        let error_prop = ec.borrow_mut().factory.new_property_assignment(
            cx.nodes,
            None,
            Some(error_ident),
            None,
            None,
            Some(void_zero),
        );
        let has_error_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "hasError");
        let false_expr = ec.borrow_mut().factory.new_false_expression(cx.nodes);
        let has_error_prop = ec.borrow_mut().factory.new_property_assignment(
            cx.nodes,
            None,
            Some(has_error_ident),
            None,
            None,
            Some(false_expr),
        );
        let props = ec
            .borrow_mut()
            .factory
            .new_node_list([stack_prop, error_prop, has_error_prop]);
        let env_object = ec.borrow_mut().factory.new_object_literal_expression(
            cx.nodes,
            Some(props),
            false, /*multi_line*/
        );
        let env_var = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(env_binding),
            None, /*exclamation_token*/
            None, /*type_node*/
            Some(env_object),
        );
        let env_decls = ec.borrow_mut().factory.new_node_list([env_var]);
        let env_var_list = ec.borrow_mut().factory.new_variable_declaration_list(
            cx.nodes,
            Some(env_decls),
            NodeFlags::CONST,
        );
        let env_var_statement = ec.borrow_mut().factory.new_variable_statement(
            cx.nodes,
            None, /*modifiers*/
            Some(env_var_list),
        );
        statements.push(env_var_statement);

        // when `async` is `false`, produces:
        //
        //  try {
        //    <bodyStatements>
        //  }
        //  catch (e_1) {
        //      env_1.error = e_1;
        //      env_1.hasError = true;
        //  }
        //  finally {
        //    __disposeResources(env_1);
        //  }

        // when `async` is `true`, produces:
        //
        //  try {
        //    <bodyStatements>
        //  }
        //  catch (e_1) {
        //      env_1.error = e_1;
        //      env_1.hasError = true;
        //  }
        //  finally {
        //    const result_1 = __disposeResources(env_1);
        //    if (result_1) {
        //      await result_1;
        //    }
        //  }

        // Unfortunately, it is necessary to use two properties to indicate an error because `throw undefined` is
        // legal JavaScript.
        let body_list = ec.borrow_mut().factory.new_node_list(body_statements);
        let try_block =
            ec.borrow_mut()
                .factory
                .new_block(cx.nodes, Some(body_list), true /*multi_line*/);
        let body_catch_binding = ec.borrow_mut().factory.new_unique_name(cx.nodes, "e");
        let error_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "error");
        let env_error = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(env_binding),
            None,
            Some(error_ident),
            NodeFlags::NONE,
        );
        let assign_error = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            env_error,
            body_catch_binding,
        );
        let error_stmt = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(assign_error));
        let has_error_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "hasError");
        let env_has_error = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(env_binding),
            None,
            Some(has_error_ident),
            NodeFlags::NONE,
        );
        let true_expr = ec.borrow_mut().factory.new_true_expression(cx.nodes);
        let assign_has_error =
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, env_has_error, true_expr);
        let has_error_stmt = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(assign_has_error));
        let catch_stmts = ec
            .borrow_mut()
            .factory
            .new_node_list([error_stmt, has_error_stmt]);
        let catch_block = ec.borrow_mut().factory.new_block(
            cx.nodes,
            Some(catch_stmts),
            true, /*multi_line*/
        );
        let catch_var_decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(body_catch_binding),
            None, /*exclamation_token*/
            None, /*type*/
            None, /*initializer*/
        );
        let catch_clause = ec.borrow_mut().factory.new_catch_clause(
            cx.nodes,
            Some(catch_var_decl),
            Some(catch_block),
        );

        let finally_block = if async_ {
            let result = ec.borrow_mut().factory.new_unique_name(cx.nodes, "result");
            let dispose = ec
                .borrow_mut()
                .factory
                .new_dispose_resources_helper(cx.nodes, env_binding);
            let result_decl = ec.borrow_mut().factory.new_variable_declaration(
                cx.nodes,
                Some(result),
                None, /*exclamation_token*/
                None, /*type*/
                Some(dispose),
            );
            let result_decls = ec.borrow_mut().factory.new_node_list([result_decl]);
            let result_list = ec.borrow_mut().factory.new_variable_declaration_list(
                cx.nodes,
                Some(result_decls),
                NodeFlags::CONST,
            );
            let result_stmt = ec.borrow_mut().factory.new_variable_statement(
                cx.nodes,
                None, /*modifiers*/
                Some(result_list),
            );
            let await_result = ec
                .borrow_mut()
                .factory
                .new_await_expression(cx.nodes, Some(result));
            let await_stmt = ec
                .borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, Some(await_result));
            let if_stmt = ec.borrow_mut().factory.new_if_statement(
                cx.nodes,
                Some(result),
                Some(await_stmt),
                None, /*else_statement*/
            );
            let stmts = ec
                .borrow_mut()
                .factory
                .new_node_list([result_stmt, if_stmt]);
            ec.borrow_mut()
                .factory
                .new_block(cx.nodes, Some(stmts), true /*multi_line*/)
        } else {
            let dispose = ec
                .borrow_mut()
                .factory
                .new_dispose_resources_helper(cx.nodes, env_binding);
            let dispose_stmt = ec
                .borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, Some(dispose));
            let stmts = ec.borrow_mut().factory.new_node_list([dispose_stmt]);
            ec.borrow_mut()
                .factory
                .new_block(cx.nodes, Some(stmts), true /*multi_line*/)
        };

        let try_statement = ec.borrow_mut().factory.new_try_statement(
            cx.nodes,
            Some(try_block),
            Some(catch_clause),
            Some(finally_block),
        );
        statements.push(try_statement);
        statements
    }
}

/// `isUsingVariableDeclarationList` — `node` is a `ForInitializer`.
fn is_using_variable_declaration_list(cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
    ast::is_variable_declaration_list(&cx.nodes[node])
        && get_using_kind_of_variable_declaration_list(cx, node) != UsingKind::None
}

/// `getUsingKindOfVariableDeclarationList`.
fn get_using_kind_of_variable_declaration_list(cx: &VisitorCx<'_, '_>, node: NodeId) -> UsingKind {
    match cx.nodes[node].flags & NodeFlags::BLOCK_SCOPED {
        NodeFlags::AWAIT_USING => UsingKind::Async,
        NodeFlags::USING => UsingKind::Sync,
        _ => UsingKind::None,
    }
}

/// `getUsingKindOfVariableStatement`.
fn get_using_kind_of_variable_statement(cx: &VisitorCx<'_, '_>, node: NodeId) -> UsingKind {
    let declaration_list = cx.nodes[node].as_variable_statement().declaration_list;
    match declaration_list {
        Some(list) => get_using_kind_of_variable_declaration_list(cx, list),
        None => UsingKind::None,
    }
}

/// `getUsingKind` — `statement` is a `*ast.Node`.
fn get_using_kind(cx: &VisitorCx<'_, '_>, statement: NodeId) -> UsingKind {
    if ast::is_variable_statement(&cx.nodes[statement]) {
        return get_using_kind_of_variable_statement(cx, statement);
    }
    UsingKind::None
}

/// `getUsingKindOfStatements`.
fn get_using_kind_of_statements(cx: &VisitorCx<'_, '_>, statements: &[NodeId]) -> UsingKind {
    let mut result = UsingKind::None;
    for &statement in statements {
        let using_kind = get_using_kind(cx, statement);
        if using_kind == UsingKind::Async {
            return UsingKind::Async;
        }
        if using_kind > result {
            result = using_kind;
        }
    }
    result
}

/// `newUsingDeclarationTransformer`.
pub(crate) fn new_using_declaration_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        let state = Rc::new(UsingDeclarationTransformer {
            export_bindings: RefCell::new(None),
            export_binding_names: RefCell::new(Vec::new()),
            export_vars: RefCell::new(Vec::new()),
            default_export_binding: Cell::new(None),
            export_equals_binding: Cell::new(None),
        });
        Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, v, cx, node)
            },
        )
    })
}
