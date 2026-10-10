// Ported from tsc/internal/transformers/moduletransforms/esmodule.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The ES module transform: module-specifier rewriting
// (`--rewriteRelativeImportExtensions`), `import x = require("mod")` →
// `const x = require("mod")` under node-flavored ES module kinds, `export =`
// elision, `export * as ns` namespace re-exports, and `tslib`/createRequire
// prologue injection.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_core::options_generated::{CompilerOptions, ModuleKind};
use tsc_printer::{AutoGenerateOptions, EmitFlags, GeneratedIdentifierFlags};

use super::externalmoduleinfo::create_external_helpers_import_declaration_if_needed;
use super::utilities::{
    create_empty_imports, get_external_module_name_literal, rewrite_module_specifier,
};
use crate::chain::{GetEmitModuleFormatOfFile, TransformOptions};
use crate::estransforms::{Ec, make_transformer, visit_each_child};
use crate::single_or_many;
use crate::transformer::Transformer;

/// `type importRequireStatements struct`
struct ImportRequireStatements {
    statements: Vec<NodeId>,
    require_helper_name: NodeId,
}

/// `type ESModuleTransformer struct`.
struct EsModuleTransformer<'a> {
    compiler_options: &'a CompilerOptions,
    /// `resolver` — stored for parity with Go's `ESModuleTransformer.resolver`;
    /// nothing in `esmodule.go` consults it.
    #[allow(dead_code)]
    resolver: Option<Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    get_emit_module_format_of_file: Option<&'a GetEmitModuleFormatOfFile<'a>>,
    /// `currentSourceFile`
    current_source_file: Cell<Option<NodeId>>,
    /// `importRequireStatements`
    import_require_statements: RefCell<Option<ImportRequireStatements>>,
    // `helperNameSubstitutions` is declared but never used in
    // `esmodule.go` — omitted.
}

/// `NewESModuleTransformer`.
pub fn new_es_module_transformer<'a>(opts: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    let compiler_options = opts
        .compiler_options
        .expect("NewESModuleTransformer requires opts.CompilerOptions");
    make_transformer(opts, |ec| {
        let tx = Rc::new(EsModuleTransformer {
            compiler_options,
            resolver: opts.resolver.clone(),
            get_emit_module_format_of_file: opts.get_emit_module_format_of_file,
            current_source_file: Cell::new(None),
            import_require_statements: RefCell::new(None),
        });
        Box::new(move |v, cx, node| tx.visit(&ec, v, cx, node))
    })
}

impl<'a> EsModuleTransformer<'a> {
    /// `tx.getEmitModuleFormatOfFile(node)` — `node` must be a `SourceFile`.
    fn emit_module_format(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> ModuleKind {
        (self
            .get_emit_module_format_of_file
            .expect("opts.GetEmitModuleFormatOfFile is required by the module transforms"))(
            cx.nodes[node].as_source_file(),
        )
    }

    /// `(tx *ESModuleTransformer) visit` — visits source elements that are
    /// not top-level or top-level nested statements.
    fn visit(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::SourceFile => Some(self.visit_source_file(ec, v, cx, node)),
            Kind::ImportDeclaration => self.visit_import_declaration(ec, v, cx, node),
            Kind::ImportEqualsDeclaration => self.visit_import_equals_declaration(ec, v, cx, node),
            Kind::ExportAssignment => self.visit_export_assignment(ec, v, cx, node),
            Kind::ExportDeclaration => self.visit_export_declaration(ec, v, cx, node),
            Kind::CallExpression => self.visit_call_expression(ec, v, cx, node),
            _ => Some(visit_each_child(v, cx, node)),
        }
    }

    /// `(tx *ESModuleTransformer) visitSourceFile` — `node` must be a
    /// `SourceFile`.
    fn visit_source_file(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (is_declaration_file, is_external_module) = {
            let sf = cx.nodes[node].as_source_file();
            (sf.is_declaration_file, ast::is_external_module(sf))
        };
        if is_declaration_file
            || !(is_external_module || self.compiler_options.get_isolated_modules())
        {
            return node;
        }

        self.current_source_file.set(Some(node));
        *self.import_require_statements.borrow_mut() = None;

        let mut result = visit_each_child(v, cx, node);
        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(result, &helpers);

        let external_helpers_import_declaration = {
            let file_module_kind = self.emit_module_format(cx, node);
            create_external_helpers_import_declaration_if_needed(
                &mut ec.borrow_mut(),
                cx.nodes,
                result,
                self.compiler_options,
                file_module_kind,
                false, /* hasExportStarsToExportValues */
                false, /* hasImportStar */
                false, /* hasImportDefault */
            )
        };
        let import_require_statements = self.import_require_statements.borrow_mut().take();
        if external_helpers_import_declaration.is_some() || import_require_statements.is_some() {
            let (source, result_statements_loc) = {
                let statements_list = &cx.nodes[result].as_source_file().statements;
                (
                    statements_list
                        .as_ref()
                        .map(|l| l.nodes.iter().copied().collect::<Vec<_>>())
                        .unwrap_or_default(),
                    statements_list.as_ref().map(|l| l.loc).unwrap_or_default(),
                )
            };
            let (prologue, rest) = ec
                .borrow()
                .factory
                .split_standard_prologue(cx.nodes, &source);
            let (custom, rest) = ec.borrow().factory.split_custom_prologue(cx.nodes, rest);
            let mut statements = prologue.to_vec();
            statements.extend_from_slice(custom);
            if let Some(decl) = external_helpers_import_declaration {
                // The helpers import must be visited so that `import x = require("tslib")`
                // (TypeScript-only syntax) is transformed to `const x = require("tslib")`
                // for CJS output files via visitImportEqualsDeclaration.
                if let Some(visited) = v.visit_node(cx, Some(decl)) {
                    statements.push(visited);
                }
            }
            if let Some(import_require_statements) = import_require_statements {
                statements.extend_from_slice(&import_require_statements.statements);
            }
            statements.extend_from_slice(rest);
            result = {
                let mut e = ec.borrow_mut();
                let mut statement_list = e.factory.new_node_list(statements);
                statement_list.loc = result_statements_loc;
                e.factory
                    .update_source_file(cx.nodes, result, Some(statement_list), {
                        cx.nodes[node].as_source_file().end_of_file_token
                    })
                    .unwrap_or(result)
            };
        }

        let end_of_file_token = cx.nodes[node].as_source_file().end_of_file_token;
        if ast::is_external_module(cx.nodes[result].as_source_file())
            && self.compiler_options.get_emit_module_kind() != ModuleKind::Preserve
            && !cx.nodes[result]
                .as_source_file()
                .statements
                .as_ref()
                .is_some_and(|l| {
                    l.nodes
                        .iter()
                        .any(|s| ast::is_external_module_indicator(&cx.nodes[*s]))
                })
        {
            let (mut statements, statements_loc): (Vec<NodeId>, _) = {
                let statements_list = &cx.nodes[result].as_source_file().statements;
                (
                    statements_list
                        .as_ref()
                        .map(|l| l.nodes.iter().copied().collect())
                        .unwrap_or_default(),
                    statements_list.as_ref().map(|l| l.loc).unwrap_or_default(),
                )
            };
            statements.push({
                let mut e = ec.borrow_mut();
                create_empty_imports(&mut e.factory, cx.nodes)
            });
            result = {
                let mut e = ec.borrow_mut();
                let mut statement_list = e.factory.new_node_list(statements);
                statement_list.loc = statements_loc;
                e.factory
                    .update_source_file(cx.nodes, result, Some(statement_list), end_of_file_token)
                    .unwrap_or(result)
            };
        }

        *self.import_require_statements.borrow_mut() = None;
        self.current_source_file.set(None);
        result
    }

    /// `(tx *ESModuleTransformer) visitImportDeclaration` — `node` must be an
    /// `ImportDeclaration`.
    fn visit_import_declaration(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if !self
            .compiler_options
            .rewrite_relative_import_extensions
            .is_true()
        {
            return Some(node);
        }
        let (import_clause, module_specifier, attributes) = {
            let d = cx.nodes[node].as_import_declaration();
            (d.import_clause, d.module_specifier, d.attributes)
        };
        let updated_module_specifier = rewrite_module_specifier(
            &mut ec.borrow_mut(),
            cx.nodes,
            module_specifier,
            self.compiler_options,
        );
        let import_clause = v.visit_node(cx, import_clause);
        let attributes = v.visit_node(cx, attributes);
        Some(
            ec.borrow_mut()
                .factory
                .update_import_declaration(
                    cx.nodes,
                    node,
                    None, /* modifiers */
                    import_clause,
                    updated_module_specifier,
                    attributes,
                )
                .unwrap_or(node),
        )
    }

    /// `(tx *ESModuleTransformer) visitImportEqualsDeclaration` — `node`
    /// must be an `ImportEqualsDeclaration`.
    fn visit_import_equals_declaration(
        &self,
        ec: &Ec,
        _v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // Though an error in es2020 modules, in node-flavor es2020 modules, we can helpfully transform this to a synthetic `require` call
        // To give easy access to a synchronous `require` in node-flavor esm. We do the transform even in scenarios where we error, but `import.meta.url`
        // is available, just because the output is reasonable for a node-like runtime.
        if self.compiler_options.get_emit_module_kind() < ModuleKind::Node16 {
            return None;
        }

        if !ast::is_external_module_import_equals_declaration(&cx.nodes[node], cx.nodes) {
            panic!(
                "import= for internal module references should be handled in an earlier transformer."
            )
        }

        let name = cx.nodes[node].name();
        let require_call = self.create_require_call(ec, cx, node);
        let var_statement = {
            let mut e = ec.borrow_mut();
            let f = &mut e.factory;
            let name = name.map(|n| f.clone_node(cx.nodes, n));
            let var_decl = f.new_variable_declaration(
                cx.nodes,
                name,
                None, /* exclamationToken */
                None, /* type */
                Some(require_call),
            );
            let decl_list = f.new_node_list(vec![var_decl]);
            let decl_list =
                f.new_variable_declaration_list(cx.nodes, Some(decl_list), ast::NodeFlags::CONST);
            f.new_variable_statement(cx.nodes, None /* modifiers */, Some(decl_list))
        };
        ec.borrow().set_original(var_statement, node);
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, var_statement, node);

        let mut statements = vec![var_statement];
        statements = self.append_exports_of_import_equals_declaration(ec, cx, statements, node);
        {
            let mut e = ec.borrow_mut();
            single_or_many(&mut e.factory, cx.nodes, Some(statements))
        }
    }

    /// `(tx *ESModuleTransformer) appendExportsOfImportEqualsDeclaration` —
    /// `node` must be an `ImportEqualsDeclaration`.
    fn append_exports_of_import_equals_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        node: NodeId,
    ) -> Vec<NodeId> {
        if ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT) {
            let name = cx.nodes[node].name();
            let export_decl = {
                let mut e = ec.borrow_mut();
                let f = &mut e.factory;
                let name = name.map(|n| f.clone_node(cx.nodes, n));
                let specifier = f.new_export_specifier(
                    cx.nodes, false, /* isTypeOnly */
                    None,  /* propertyName */
                    name,
                );
                let elements = f.new_node_list(vec![specifier]);
                let named_exports = f.new_named_exports(cx.nodes, Some(elements));
                f.new_export_declaration(
                    cx.nodes,
                    None,  /* modifiers */
                    false, /* isTypeOnly */
                    Some(named_exports),
                    None, /* moduleSpecifier */
                    None, /* attributes */
                )
            };
            statements.push(export_decl);
        }
        statements
    }

    /// `(tx *ESModuleTransformer) visitExportAssignment` — `node` must be an
    /// `ExportAssignment`.
    fn visit_export_assignment(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let (is_export_equals, expression) = {
            let d = cx.nodes[node].as_export_assignment();
            (d.is_export_equals, d.expression)
        };
        if !is_export_equals {
            return Some(visit_each_child(v, cx, node));
        }
        if self.compiler_options.get_emit_module_kind() != ModuleKind::Preserve {
            // Elide `export=` as it is not legal with --module ES6
            return None;
        }
        let expression = v.visit_node(cx, expression);
        let statement = {
            let mut e = ec.borrow_mut();
            let f = &mut e.factory;
            let module_ident = f.new_identifier(cx.nodes, "module");
            let exports_ident = f.new_identifier(cx.nodes, "exports");
            let left = f.new_property_access_expression(
                cx.nodes,
                Some(module_ident),
                None, /* questionDotToken */
                Some(exports_ident),
                ast::NodeFlags::NONE,
            );
            let assignment = f.new_assignment_expression(cx.nodes, left, expression.unwrap());
            f.new_expression_statement(cx.nodes, Some(assignment))
        };
        ec.borrow().set_original(statement, node);
        Some(statement)
    }

    /// `(tx *ESModuleTransformer) visitExportDeclaration` — `node` must be an
    /// `ExportDeclaration`.
    fn visit_export_declaration(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let (export_clause, module_specifier, attributes) = {
            let d = cx.nodes[node].as_export_declaration();
            (d.export_clause, d.module_specifier, d.attributes)
        };
        if module_specifier.is_none() {
            return Some(node);
        }

        let updated_module_specifier = rewrite_module_specifier(
            &mut ec.borrow_mut(),
            cx.nodes,
            module_specifier,
            self.compiler_options,
        );
        if self.compiler_options.module > ModuleKind::ES2015
            || export_clause.is_none()
            || !ast::is_namespace_export(&cx.nodes[export_clause.unwrap()])
        {
            // Either ill-formed or don't need to be transformed.
            let attributes = v.visit_node(cx, attributes);
            return Some(
                ec.borrow_mut()
                    .factory
                    .update_export_declaration(
                        cx.nodes,
                        node,
                        None,  /* modifiers */
                        false, /* isTypeOnly */
                        export_clause,
                        updated_module_specifier,
                        attributes,
                    )
                    .unwrap_or(node),
            );
        }

        let old_identifier = cx.nodes[export_clause.unwrap()].name();
        let attributes = v.visit_node(cx, attributes);
        let (import_decl, export_decl) = {
            let mut e = ec.borrow_mut();
            let f = &mut e.factory;
            let synth_name = f.new_generated_name_for_node(cx.nodes, old_identifier.unwrap());
            let namespace_import = f.new_namespace_import(cx.nodes, Some(synth_name));
            let import_clause = f.new_import_clause(
                cx.nodes,
                ast::Kind::Unknown, /* phaseModifier */
                None,               /* name */
                Some(namespace_import),
            );
            let import_decl = f.new_import_declaration(
                cx.nodes,
                None, /* modifiers */
                Some(import_clause),
                updated_module_specifier,
                attributes,
            );
            let export_decl =
                if ast::is_export_namespace_as_default_declaration(&cx.nodes[node], cx.nodes) {
                    f.new_export_assignment(
                        cx.nodes,
                        None,  /* modifiers */
                        false, /* isExportEquals */
                        None,  /* typeNode */
                        Some(synth_name),
                    )
                } else {
                    let specifier = f.new_export_specifier(
                        cx.nodes,
                        false, /* isTypeOnly */
                        Some(synth_name),
                        old_identifier,
                    );
                    let elements = f.new_node_list(vec![specifier]);
                    let named_exports = f.new_named_exports(cx.nodes, Some(elements));
                    f.new_export_declaration(
                        cx.nodes,
                        None,  /* modifiers */
                        false, /* isTypeOnly */
                        Some(named_exports),
                        None, /* moduleSpecifier */
                        None, /* attributes */
                    )
                };
            (import_decl, export_decl)
        };
        ec.borrow()
            .set_original(import_decl, export_clause.unwrap());
        ec.borrow().set_original(export_decl, node);
        {
            let mut e = ec.borrow_mut();
            single_or_many(
                &mut e.factory,
                cx.nodes,
                Some(vec![import_decl, export_decl]),
            )
        }
    }

    /// `(tx *ESModuleTransformer) visitCallExpression` — `node` must be a
    /// `CallExpression`.
    fn visit_call_expression(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if self
            .compiler_options
            .rewrite_relative_import_extensions
            .is_true()
            && ((ast::is_import_call(&cx.nodes[node], cx.nodes)
                && !cx.nodes[node].arguments().unwrap_or(&[]).is_empty())
                || (ast::is_in_js_file(Some(node), cx.nodes)
                    && ast::is_require_call(&cx.nodes[node], false, cx.nodes)))
        {
            return Some(self.visit_import_or_require_call(ec, v, cx, node));
        }
        Some(visit_each_child(v, cx, node))
    }

    /// `(tx *ESModuleTransformer) visitImportOrRequireCall` — `node` must be
    /// a `CallExpression`.
    fn visit_import_or_require_call(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, question_dot_token, arguments, arguments_loc, flags) = {
            let d = cx.nodes[node].as_call_expression();
            (
                d.expression,
                d.question_dot_token,
                d.arguments
                    .as_ref()
                    .map(|a| a.nodes.iter().copied().collect::<Vec<_>>()),
                d.arguments.as_ref().map(|a| a.loc).unwrap_or_default(),
                cx.nodes[node].flags,
            )
        };
        let arguments = arguments.unwrap_or_default();
        if arguments.is_empty() {
            return visit_each_child(v, cx, node);
        }

        let expression = v.visit_node(cx, expression);

        let argument = if ast::is_string_literal_like(&cx.nodes[arguments[0]]) {
            rewrite_module_specifier(
                &mut ec.borrow_mut(),
                cx.nodes,
                Some(arguments[0]),
                self.compiler_options,
            )
        } else {
            Some(
                ec.borrow_mut()
                    .factory
                    .new_rewrite_relative_import_extensions_helper(
                        cx.nodes,
                        arguments[0],
                        self.compiler_options.jsx == tsc_core::options_generated::JsxEmit::Preserve,
                    ),
            )
        };

        let mut visited_arguments: Vec<NodeId> = Vec::new();
        if let Some(argument) = argument {
            visited_arguments.push(argument);
        }
        let rest = v
            .visit_slice(cx, &arguments[1..])
            .unwrap_or_else(|| arguments[1..].to_vec());
        visited_arguments.extend_from_slice(&rest);

        let mut e = ec.borrow_mut();
        let mut argument_list = e.factory.new_node_list(visited_arguments);
        argument_list.loc = arguments_loc;
        e.factory
            .update_call_expression(
                cx.nodes,
                node,
                expression,
                question_dot_token,
                None, /* typeArguments */
                Some(argument_list),
                flags,
            )
            .unwrap_or(node)
    }

    /// `(tx *ESModuleTransformer) createRequireCall` — `node` must be an
    /// `ImportDeclaration`, `ImportEqualsDeclaration`, or
    /// `ExportDeclaration`.
    fn create_require_call(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let mut args: Vec<NodeId> = Vec::new();
        let module_name = {
            let mut e = ec.borrow_mut();
            get_external_module_name_literal(
                &mut e.factory,
                cx.nodes,
                node,
                self.current_source_file.get(),
                None, /* host */
                None, /* emitResolver */
                self.compiler_options,
            )
        };
        if let Some(module_name) = module_name {
            args.push(
                rewrite_module_specifier(
                    &mut ec.borrow_mut(),
                    cx.nodes,
                    Some(module_name),
                    self.compiler_options,
                )
                .unwrap(),
            );
        }

        if self.compiler_options.get_emit_module_kind() == ModuleKind::Preserve {
            let mut e = ec.borrow_mut();
            let f = &mut e.factory;
            let require_ident = f.new_identifier(cx.nodes, "require");
            let arg_list = f.new_node_list(args);
            return f.new_call_expression(
                cx.nodes,
                Some(require_ident),
                None, /* questionDotToken */
                None, /* typeArguments */
                Some(arg_list),
                ast::NodeFlags::NONE,
            );
        }

        if self.import_require_statements.borrow().is_none() {
            let (import_statement, require_statement, require_helper_name) = {
                let mut e = ec.borrow_mut();
                let f = &mut e.factory;
                let create_require_name = f.new_unique_name_ex(
                    cx.nodes,
                    "_createRequire",
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::OPTIMISTIC
                            | GeneratedIdentifierFlags::FILE_LEVEL,
                        ..Default::default()
                    },
                );
                let create_require_ident = f.new_identifier(cx.nodes, "createRequire");
                let specifier = f.new_import_specifier(
                    cx.nodes,
                    false, /* isTypeOnly */
                    Some(create_require_ident),
                    Some(create_require_name),
                );
                let elements = f.new_node_list(vec![specifier]);
                let named_imports = f.new_named_imports(cx.nodes, Some(elements));
                let import_clause = f.new_import_clause(
                    cx.nodes,
                    ast::Kind::Unknown, /* phaseModifier */
                    None,               /* name */
                    Some(named_imports),
                );
                let module_literal =
                    f.new_string_literal(cx.nodes, "module", ast::TokenFlags::NONE);
                let import_statement = f.new_import_declaration(
                    cx.nodes,
                    None, /* modifiers */
                    Some(import_clause),
                    Some(module_literal),
                    None, /* attributes */
                );

                let require_helper_name = f.new_unique_name_ex(
                    cx.nodes,
                    "__require",
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::OPTIMISTIC
                            | GeneratedIdentifierFlags::FILE_LEVEL,
                        ..Default::default()
                    },
                );
                let require_statement = {
                    let create_require_clone = f.clone_node(cx.nodes, create_require_name);
                    let meta_name = f.new_identifier(cx.nodes, "meta");
                    let meta =
                        f.new_meta_property(cx.nodes, ast::Kind::ImportKeyword, Some(meta_name));
                    let url_ident = f.new_identifier(cx.nodes, "url");
                    let meta_url = f.new_property_access_expression(
                        cx.nodes,
                        Some(meta),
                        None, /* questionDotToken */
                        Some(url_ident),
                        ast::NodeFlags::NONE,
                    );
                    let arg_list = f.new_node_list(vec![meta_url]);
                    let call = f.new_call_expression(
                        cx.nodes,
                        Some(create_require_clone),
                        None, /* questionDotToken */
                        None, /* typeArguments */
                        Some(arg_list),
                        ast::NodeFlags::NONE,
                    );
                    let var_decl = f.new_variable_declaration(
                        cx.nodes,
                        Some(require_helper_name),
                        None, /* exclamationToken */
                        None, /* type */
                        Some(call),
                    );
                    let decl_list = f.new_node_list(vec![var_decl]);
                    let decl_list = f.new_variable_declaration_list(
                        cx.nodes,
                        Some(decl_list),
                        ast::NodeFlags::CONST,
                    );
                    f.new_variable_statement(cx.nodes, None /* modifiers */, Some(decl_list))
                };
                (import_statement, require_statement, require_helper_name)
            };
            ec.borrow()
                .add_emit_flags(import_statement, EmitFlags::CUSTOM_PROLOGUE);
            ec.borrow()
                .add_emit_flags(require_statement, EmitFlags::CUSTOM_PROLOGUE);
            *self.import_require_statements.borrow_mut() = Some(ImportRequireStatements {
                statements: vec![import_statement, require_statement],
                require_helper_name,
            });
        }

        let require_helper_name = self
            .import_require_statements
            .borrow()
            .as_ref()
            .unwrap()
            .require_helper_name;
        let mut e = ec.borrow_mut();
        let f = &mut e.factory;
        let require_helper_name = f.clone_node(cx.nodes, require_helper_name);
        let arg_list = f.new_node_list(args);
        f.new_call_expression(
            cx.nodes,
            Some(require_helper_name),
            None, /* questionDotToken */
            None, /* typeArguments */
            Some(arg_list),
            ast::NodeFlags::NONE,
        )
    }
}
