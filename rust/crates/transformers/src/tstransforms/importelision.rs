// Ported from tsc/internal/transformers/tstransforms/importelision.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Import elision — removes unused/type-only import bindings (and unused
// export specifiers) driven by `printer::EmitResolver` reference marking.
//
// PORT: `emitResolver` is `Option<Rc<RefCell<dyn EmitResolver>>>` (Go's
// nilable interface). `currentSourceFile` is a `Cell<Option<NodeId>>` on the
// shared state. Resolver methods take the node arena explicitly (see the
// `EmitResolver` trait).

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId};
use tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::TS_TRUE;
use tsc_printer::EmitResolver;

use crate::chain::TransformOptions;
use crate::estransforms::{make_transformer, visit_each_child, Ec};
use crate::transformer::Transformer;

/// `type ImportElisionTransformer struct`.
pub struct ImportElisionTransformer<'a> {
    /// `compilerOptions *core.CompilerOptions`
    compiler_options: &'a CompilerOptions,
    /// `currentSourceFile *ast.SourceFile`
    current_source_file: Cell<Option<NodeId>>,
    /// `emitResolver printer.EmitResolver`
    emit_resolver: Option<Rc<RefCell<dyn EmitResolver + 'a>>>,
}

impl<'a> ImportElisionTransformer<'a> {
    /// `tx.visit`
    fn visit<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].kind == Kind::SourceFile {
            if let Some(resolver) = &self.emit_resolver {
                let original = ec.borrow().most_original(Some(node));
                if let Some(file) = original {
                    resolver
                        .borrow_mut()
                        .mark_linked_references_recursively(file, cx.nodes);
                }
            }
        }

        match cx.nodes[node].kind {
            Kind::ImportEqualsDeclaration => {
                if ast::is_external_module_import_equals_declaration(&cx.nodes[node], cx.nodes) {
                    if !self.should_emit_alias_declaration(ec, cx, node) {
                        return None;
                    }
                } else if !self.should_emit_import_equals_declaration(ec, cx, node) {
                    return None;
                }
                Some(visit_each_child(v, cx, node))
            }

            Kind::ImportDeclaration => {
                let d = cx.nodes[node].as_import_declaration();
                let (modifiers, import_clause, module_specifier, attributes) = (
                    d.modifiers_base.modifiers.clone(),
                    d.import_clause,
                    d.module_specifier,
                    d.attributes,
                );
                // Do not elide a side-effect only import declaration.
                //  import "foo";
                if import_clause.is_some() {
                    let import_clause = v.visit_node(cx, import_clause);
                    if import_clause.is_none() {
                        return None;
                    }
                    let attributes = v.visit_node(cx, attributes);
                    return ec
                        .borrow_mut()
                        .factory
                        .update_import_declaration(
                            cx.nodes,
                            node,
                            modifiers,
                            import_clause,
                            module_specifier,
                            attributes,
                        )
                        .unwrap_or(node)
                        .into();
                }
                Some(visit_each_child(v, cx, node))
            }

            Kind::ImportClause => {
                let d = cx.nodes[node].as_import_clause();
                let (phase_modifier, name_in, named_bindings_in) =
                    (d.phase_modifier, d.name, d.named_bindings);
                let name = if self.should_emit_alias_declaration(ec, cx, node) {
                    name_in
                } else {
                    None
                };
                let named_bindings = v.visit_node(cx, named_bindings_in);
                if name.is_none() && named_bindings.is_none() {
                    // all import bindings were elided
                    return None;
                }
                ec.borrow_mut()
                    .factory
                    .update_import_clause(cx.nodes, node, phase_modifier, name, named_bindings)
                    .unwrap_or(node)
                    .into()
            }

            Kind::NamespaceImport => {
                if !self.should_emit_alias_declaration(ec, cx, node) {
                    // elide unused imports
                    return None;
                }
                Some(node)
            }

            Kind::NamedImports => {
                let elements_in = cx.nodes[node].as_named_imports().elements.clone();
                let elements = v.visit_nodes(cx, elements_in);
                if elements.as_ref().is_none_or(|e| e.nodes.is_empty()) {
                    // all import specifiers were elided
                    return None;
                }
                ec.borrow_mut()
                    .factory
                    .update_named_imports(cx.nodes, node, elements)
                    .unwrap_or(node)
                    .into()
            }

            Kind::ImportSpecifier => {
                if !self.should_emit_alias_declaration(ec, cx, node) {
                    // elide type-only or unused imports
                    return None;
                }
                Some(node)
            }

            Kind::ExportAssignment => {
                if self.compiler_options.verbatim_module_syntax != TS_TRUE
                    && !self.is_value_alias_declaration(ec, cx, node)
                {
                    // elide unused import
                    return None;
                }
                Some(visit_each_child(v, cx, node))
            }

            Kind::ExportDeclaration => {
                let d = cx.nodes[node].as_export_declaration();
                let (export_clause_in, module_specifier_in, attributes_in) =
                    (d.export_clause, d.module_specifier, d.attributes);
                let mut export_clause = None;
                if export_clause_in.is_some() {
                    export_clause = v.visit_node(cx, export_clause_in);
                    if export_clause.is_none() {
                        // all export bindings were elided
                        return None;
                    }
                }
                let module_specifier = v.visit_node(cx, module_specifier_in);
                let attributes = v.visit_node(cx, attributes_in);
                ec.borrow_mut()
                    .factory
                    .update_export_declaration(
                        cx.nodes,
                        node,
                        None,
                        false,
                        export_clause,
                        module_specifier,
                        attributes,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::NamedExports => {
                let elements_in = cx.nodes[node].as_named_exports().elements.clone();
                let elements = v.visit_nodes(cx, elements_in);
                if elements.as_ref().is_none_or(|e| e.nodes.is_empty()) {
                    // all export specifiers were elided
                    return None;
                }
                ec.borrow_mut()
                    .factory
                    .update_named_exports(cx.nodes, node, elements)
                    .unwrap_or(node)
                    .into()
            }

            Kind::ExportSpecifier => {
                if !self.is_value_alias_declaration(ec, cx, node) {
                    // elide unused export
                    return None;
                }
                Some(node)
            }

            Kind::SourceFile => {
                let saved_current_source_file = self.current_source_file.get();
                self.current_source_file.set(Some(node));
                let result = visit_each_child(v, cx, node);
                self.current_source_file.set(saved_current_source_file);
                Some(result)
            }

            Kind::ModuleDeclaration | Kind::ModuleBlock => {
                Some(visit_each_child(v, cx, node))
            }

            _ => Some(node),
        }
    }

    /// `tx.shouldEmitAliasDeclaration`
    fn should_emit_alias_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        ast::is_in_js_file(Some(node), cx.nodes) || self.is_referenced_alias_declaration(ec, cx, node)
    }

    /// `tx.shouldEmitImportEqualsDeclaration`
    ///
    /// Preserve old compiler's behavior: emit import declaration (even if we
    /// do not consider them referenced) when
    /// - current file is not external module
    /// - import declaration is top level and target is value imported by
    ///   entity name
    fn should_emit_import_equals_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        self.should_emit_alias_declaration(ec, cx, node)
            || (!self
                .current_source_file
                .get()
                .is_some_and(|f| ast::is_external_module(cx.nodes[f].as_source_file()))
                && self.is_top_level_value_import_equals_with_entity_name(ec, cx, node))
    }

    /// `tx.isReferencedAliasDeclaration`
    fn is_referenced_alias_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        let node = ec.borrow().parse_node(cx.nodes, node);
        let Some(node) = node else {
            return true;
        };
        let Some(resolver) = &self.emit_resolver else {
            return false;
        };
        resolver.borrow().is_referenced_alias_declaration(node, cx.nodes)
    }

    /// `tx.isValueAliasDeclaration`
    fn is_value_alias_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        let node = ec.borrow().parse_node(cx.nodes, node);
        let Some(node) = node else {
            return true;
        };
        let Some(resolver) = &self.emit_resolver else {
            return false;
        };
        resolver.borrow().is_value_alias_declaration(node, cx.nodes)
    }

    /// `tx.isTopLevelValueImportEqualsWithEntityName`
    fn is_top_level_value_import_equals_with_entity_name(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        let node = ec.borrow().parse_node(cx.nodes, node);
        let Some(node) = node else {
            return false;
        };
        let Some(resolver) = &self.emit_resolver else {
            return false;
        };
        resolver
            .borrow()
            .is_top_level_value_import_equals_with_entity_name(node, cx.nodes)
    }
}

/// `NewImportElisionTransformer`.
pub fn new_import_elision_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    let compiler_options = opts.compiler_options.unwrap_or(&EMPTY_COMPILER_OPTIONS);
    if compiler_options.verbatim_module_syntax == TS_TRUE {
        panic!("ImportElisionTransformer should not be used with VerbatimModuleSyntax");
    }
    let emit_resolver = opts.emit_resolver.clone();
    make_transformer(opts, |ec| {
        let state = Rc::new(ImportElisionTransformer {
            compiler_options,
            current_source_file: Cell::new(None),
            emit_resolver,
        });
        let visit: Box<VisitFn<'a>> = Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, v, cx, node)
            },
        );
        visit
    })
}
