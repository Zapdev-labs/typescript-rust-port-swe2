// Ported from tsc/internal/checker/grammarchecks.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Grammar checks: all `func`s in grammarchecks.go are ported as `impl
// Checker` methods or `pub(crate)` free functions, in Go declaration order.
//
// Conventions follow `checker_core.rs`/`types.rs`:
//   `*ast.Node` → `NodeId` (`Option<NodeId>` when the Go pointer is
//   nil-able), `*ast.NodeList` → `Option<&NodeList>`,
//   `*diagnostics.Message` → `&'static tsc_diagnostics::Message`,
//   `*ast.Diagnostic` → `ast::diagnostic::DiagnosticRef`, and Go's variadic
//   diagnostic args → `&[String]` (a `String` per interpolated argument).
//
// Cross-file calls resolve to sibling files (`checker_a.rs`–`checker_d.rs`,
// `utilities.rs`) by snake_case name — unresolved symbols are expected until
// those land.

use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, NodeId};
use tsc_core::options_generated::{ModuleKind, ScriptTarget};
use tsc_core::text::TextRange;
use tsc_diagnostics as diagnostics;
use tsc_scanner::scanner;
use tsc_stringutil as stringutil;

use crate::checker_core::Checker;
use crate::checker_types::DeclarationMeaning;

impl Checker {
    /// `func (c *Checker) grammarErrorOnFirstToken` (grammarchecks.go:18).
    pub(crate) fn grammar_error_on_first_token(
        &mut self,
        node: NodeId,
        message: &'static diagnostics::Message,
        args: &[String],
    ) -> bool {
        let nodes = self.program_nodes(node);
        let Some(source_file) = ast::get_source_file_of_node(Some(node), &nodes) else {
            return false;
        };
        if !self.has_parse_diagnostics(source_file) {
            let sf = nodes[source_file].as_source_file();
            let span = scanner::get_range_of_token_at_position(sf, nodes[node].pos() as usize);
            let diagnostic = ast::diagnostic::new_diagnostic(
                Some(ast::diagnostic::DiagnosticFile::from_node(
                    source_file,
                    &nodes,
                )),
                span,
                message,
                args,
            );
            self.add_diagnostic(&diagnostic);
            return true;
        }
        false
    }

    /// `func (c *Checker) grammarErrorAtPos` (grammarchecks.go:29).
    pub(crate) fn grammar_error_at_pos(
        &mut self,
        node_for_source_file: NodeId,
        start: i32,
        length: i32,
        message: &'static diagnostics::Message,
        args: &[String],
    ) -> bool {
        let nodes = self.program_nodes(node_for_source_file);
        let Some(source_file) = ast::get_source_file_of_node(Some(node_for_source_file), &nodes)
        else {
            return false;
        };
        if !self.has_parse_diagnostics(source_file) {
            let diagnostic = ast::diagnostic::new_diagnostic(
                Some(ast::diagnostic::DiagnosticFile::from_node(
                    source_file,
                    &nodes,
                )),
                TextRange::new(start, start + length),
                message,
                args,
            );
            self.add_diagnostic(&diagnostic);
            return true;
        }
        false
    }

    /// `func (c *Checker) grammarErrorOnNode` (grammarchecks.go:38).
    pub(crate) fn grammar_error_on_node(
        &mut self,
        node: NodeId,
        message: &'static diagnostics::Message,
        args: &[String],
    ) -> bool {
        let nodes = self.program_nodes(node);
        let Some(source_file) = ast::get_source_file_of_node(Some(node), &nodes) else {
            return false;
        };
        if !self.has_parse_diagnostics(source_file) {
            self.error(Some(node), message, args);
            return true;
        }
        false
    }

    /// `func (c *Checker) grammarErrorOnNodeSkippedOnNoEmit` (grammarchecks.go:47).
    pub(crate) fn grammar_error_on_node_skipped_on_no_emit(
        &mut self,
        node: NodeId,
        message: &'static diagnostics::Message,
        args: &[String],
    ) -> bool {
        let nodes = self.program_nodes(node);
        let Some(source_file) = ast::get_source_file_of_node(Some(node), &nodes) else {
            return false;
        };
        if !self.has_parse_diagnostics(source_file) {
            let d = crate::utilities::new_diagnostic_for_node(Some(node), &nodes, message, args);
            ast::diagnostic::lock_diagnostic(&d).set_skipped_on_no_emit();
            self.add_diagnostic(&d);
            return true;
        }
        false
    }

    /// `func (c *Checker) checkGrammarRegularExpressionLiteral` (grammarchecks.go:64).
    ///
    /// PORT: `Scanner<'a>` borrows its text and the error callback borrows
    /// locals, so the scanner is a local value rather than the Go-reused
    /// `c.regExpScanner` field. Diagnostics are staged into `pending` inside
    /// the callback and flushed via `add_diagnostic` afterwards — preserving
    /// Go's emission order (`addDiagnostic` just appends).
    pub(crate) fn check_grammar_regular_expression_literal(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let Some(source_file) = ast::get_source_file_of_node(Some(node), &nodes) else {
            return false;
        };
        if self.has_parse_diagnostics(source_file) {
            return false;
        }
        let mut last_error: Option<ast::diagnostic::DiagnosticRef> = None;
        let mut pending: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
        {
            let sf = nodes[source_file].as_source_file();
            let mut s = scanner::Scanner::new();
            s.set_script_target(self.language_version);
            s.set_language_variant(sf.language_variant);
            let file = ast::diagnostic::DiagnosticFile::from_node(source_file, &nodes);
            s.set_on_error(Some(
                |message: &'static diagnostics::Message,
                 start: usize,
                 length: usize,
                 args: &[String]| {
                    if message.category() == diagnostics::Category::Message
                        && let Some(last) = &last_error
                    {
                        let (last_pos, last_len) = {
                            let l = ast::diagnostic::lock_diagnostic(last);
                            (l.loc().pos(), l.loc().end() - l.loc().pos())
                        };
                        if start as i32 == last_pos && length as i32 == last_len {
                            // For providing spelling suggestions.
                            let err = ast::diagnostic::new_diagnostic(
                                None,
                                TextRange::new(start as i32, start as i32 + length as i32),
                                message,
                                args,
                            );
                            ast::diagnostic::lock_diagnostic(last).add_related_info(Some(err));
                            return;
                        }
                    }
                    if last_error.is_none()
                        || start as i32
                            != ast::diagnostic::lock_diagnostic(last_error.as_ref().unwrap())
                                .loc()
                                .pos()
                    {
                        let err = ast::diagnostic::new_diagnostic(
                            Some(file.clone()),
                            TextRange::new(start as i32, start as i32 + length as i32),
                            message,
                            args,
                        );
                        last_error = Some(err.clone());
                        pending.push(err);
                    }
                },
            ));
            s.set_text(&sf.text);
            s.reset_token_state(nodes[node].pos() as usize);
            s.scan();
            let token_is_regular_expression_literal =
                s.rescan_slash_token(true) == ast::Kind::RegularExpressionLiteral;
            s.set_text("");
            s.set_on_error::<fn(&'static diagnostics::Message, usize, usize, &[String])>(None);
            debug_assert!(token_is_regular_expression_literal);
        }
        for d in &pending {
            self.add_diagnostic(d);
        }
        last_error.is_some()
    }

    /// `func (c *Checker) checkGrammarPrivateIdentifierExpression` (grammarchecks.go:96).
    pub(crate) fn check_grammar_private_identifier_expression(&mut self, priv_id: NodeId) -> bool {
        let nodes = self.program_nodes(priv_id);
        if ast::get_containing_class(priv_id, &nodes).is_none() {
            return self.grammar_error_on_node(
                priv_id,
                &diagnostics::Private_identifiers_are_not_allowed_outside_class_bodies,
                &[],
            );
        }

        if !ast::is_for_in_statement(&nodes[nodes[priv_id].parent.expect("parent")]) {
            if !ast::is_expression_node(priv_id, &nodes) {
                return self.grammar_error_on_node(
                    priv_id,
                    &diagnostics::Private_identifiers_are_only_allowed_in_class_bodies_and_may_only_be_used_as_part_of_a_class_member_declaration_property_access_or_on_the_left_hand_side_of_an_in_expression,
                    &[],
                );
            }

            let parent = nodes[priv_id].parent.expect("parent");
            let is_in_operation = ast::is_binary_expression(&nodes[parent])
                && nodes[parent].as_binary_expression().operator_token == ast::Kind::InKeyword;
            if self
                .get_symbol_for_private_identifier_expression(priv_id)
                .is_none()
                && !is_in_operation
            {
                return self.grammar_error_on_node(
                    priv_id,
                    &diagnostics::Cannot_find_name_0,
                    &[nodes[priv_id].text(&nodes).to_string()],
                );
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarMappedType` (grammarchecks.go:120).
    pub(crate) fn check_grammar_mapped_type(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if let Some(members) = nodes[node].member_list()
            && !members.nodes().is_empty()
        {
            let first = members.nodes()[0];
            return self.grammar_error_on_node(
                first,
                &diagnostics::A_mapped_type_may_not_declare_properties_or_methods,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarDecorator` (grammarchecks.go:127).
    pub(crate) fn check_grammar_decorator(&mut self, decorator: NodeId) -> bool {
        let nodes = self.program_nodes(decorator);
        let Some(source_file) = ast::get_source_file_of_node(Some(decorator), &nodes) else {
            return false;
        };
        if !self.has_parse_diagnostics(source_file) {
            let mut node = nodes[decorator].expression().expect("decorator expression");

            // DecoratorParenthesizedExpression :
            //   `(` Expression `)`

            if ast::is_parenthesized_expression(&nodes[node]) {
                return false;
            }

            let mut can_have_call_expression = true;
            let mut error_node: Option<NodeId> = None;
            loop {
                // Allow TS syntax such as non-null assertions and instantiation expressions
                if ast::is_expression_with_type_arguments(&nodes[node])
                    || ast::is_non_null_expression(&nodes[node])
                {
                    node = nodes[node].expression().expect("expression");
                    continue;
                }

                // DecoratorCallExpression :
                //   DecoratorMemberExpression Arguments

                if ast::is_call_expression(&nodes[node]) {
                    let call_expr = nodes[node].as_call_expression();
                    if !can_have_call_expression {
                        error_node = Some(node);
                    }
                    if call_expr.question_dot_token.is_some() {
                        // Even if we already have an error node, error at the `?.` token since it appears earlier.
                        error_node = call_expr.question_dot_token;
                    }
                    node = call_expr.expression.expect("call expression");
                    can_have_call_expression = false;
                    continue;
                }

                // DecoratorMemberExpression :
                //   IdentifierReference
                //   DecoratorMemberExpression `.` IdentifierName
                //   DecoratorMemberExpression `.` PrivateIdentifier

                if ast::is_property_access_expression(&nodes[node]) {
                    let property_access_expr = nodes[node].as_property_access_expression();
                    if property_access_expr.question_dot_token.is_some() {
                        // Even if we already have an error node, error at the `?.` token since it appears earlier.
                        error_node = property_access_expr.question_dot_token;
                    }
                    node = property_access_expr
                        .expression
                        .expect("property access expression");
                    can_have_call_expression = false;
                    continue;
                }

                if !ast::is_identifier(&nodes[node]) {
                    // Even if we already have an error node, error at this node since it appears earlier.
                    error_node = Some(node);
                }

                break;
            }

            if let Some(error_node) = error_node {
                let expr = nodes[decorator].expression().expect("decorator expression");
                let err = self.error(
                    Some(expr),
                    &diagnostics::Expression_must_be_enclosed_in_parentheses_to_be_used_as_a_decorator,
                    &[],
                );
                if let Some(err) = &err {
                    let related = crate::checker_b::create_diagnostic_for_node(
                        Some(error_node),
                        &nodes,
                        &diagnostics::Invalid_syntax_in_decorator,
                        &[],
                    );
                    ast::diagnostic::lock_diagnostic(err).add_related_info(Some(related));
                }
                return true;
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarExportDeclaration` (grammarchecks.go:199).
    pub(crate) fn check_grammar_export_declaration(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let data = nodes[node].as_export_declaration();
        if data.is_type_only
            && let Some(export_clause) = data.export_clause
            && nodes[export_clause].kind == ast::Kind::NamedExports
        {
            return self.check_grammar_type_only_named_imports_or_exports(export_clause);
        }
        false
    }

    /// `func (c *Checker) checkGrammarModuleElementContext` (grammarchecks.go:206).
    pub(crate) fn check_grammar_module_element_context(
        &mut self,
        node: NodeId,
        error_message: &'static diagnostics::Message,
    ) -> bool {
        let nodes = self.program_nodes(node);
        let is_in_appropriate_context = nodes[node].parent.is_some_and(|p| {
            matches!(
                nodes[p].kind,
                ast::Kind::SourceFile | ast::Kind::ModuleBlock | ast::Kind::ModuleDeclaration
            )
        });
        if !is_in_appropriate_context {
            self.grammar_error_on_first_token(node, error_message, &[]);
        }
        !is_in_appropriate_context
    }

    /// `func (c *Checker) checkGrammarModifiers` (grammarchecks.go:214).
    pub(crate) fn check_grammar_modifiers(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if nodes[node].modifiers().is_none() {
            return false;
        }
        if self.report_obvious_decorator_errors(node) || self.report_obvious_modifier_errors(node) {
            return true;
        }
        let nodes = self.program_nodes(node);
        if ast::is_this_parameter(&nodes[node], &nodes) {
            return self.grammar_error_on_first_token(
                node,
                &diagnostics::Neither_decorators_nor_modifiers_may_be_applied_to_this_parameters,
                &[],
            );
        }
        let mut block_scope_kind = ast::NodeFlags::NONE;
        if ast::is_variable_statement(&nodes[node]) {
            block_scope_kind = nodes[node]
                .as_variable_statement()
                .declaration_list
                .map(|d| nodes[d].flags)
                .unwrap_or_default()
                & ast::NodeFlags::BLOCK_SCOPED;
        }
        let mut last_static: Option<NodeId> = None;
        let mut last_declare: Option<NodeId> = None;
        let mut last_async: Option<NodeId> = None;
        let mut last_override: Option<NodeId> = None;
        let mut first_decorator: Option<NodeId> = None;
        let mut flags = ast::ModifierFlags::NONE;
        let mut saw_export_before_decorators = false;
        // We parse decorators and modifiers in four contiguous chunks:
        // [...leadingDecorators, ...leadingModifiers, ...trailingDecorators, ...trailingModifiers]. It is an error to
        // have both leading and trailing decorators.
        let mut has_leading_decorators = false;
        let modifiers: Vec<NodeId> = nodes[node]
            .modifier_nodes()
            .map(|m| m.to_vec())
            .unwrap_or_default();
        for modifier in modifiers {
            if ast::is_decorator(&nodes[modifier]) {
                if !ast::node_can_be_decorated(
                    self.legacy_decorators,
                    node,
                    nodes[node].parent,
                    nodes[node].parent.and_then(|p| nodes[p].parent),
                    &nodes,
                ) {
                    if nodes[node].kind == ast::Kind::MethodDeclaration
                        && !ast::node_is_present(nodes[node].body(), &nodes)
                    {
                        return self.grammar_error_on_first_token(
                            node,
                            &diagnostics::A_decorator_can_only_decorate_a_method_implementation_not_an_overload,
                            &[],
                        );
                    } else {
                        return self.grammar_error_on_first_token(
                            node,
                            &diagnostics::Decorators_are_not_valid_here,
                            &[],
                        );
                    }
                } else if self.legacy_decorators
                    && (nodes[node].kind == ast::Kind::GetAccessor
                        || nodes[node].kind == ast::Kind::SetAccessor)
                {
                    let declarations = self
                        .get_symbol_of_declaration(node)
                        .map(|s| self.sym(s).declarations.clone())
                        .unwrap_or_default();
                    let accessors = ast::get_all_accessor_declarations_for_declaration(
                        node,
                        &declarations,
                        &nodes,
                    );
                    if ast::has_decorators(&nodes[accessors.first_accessor])
                        && Some(node) == accessors.second_accessor
                    {
                        return self.grammar_error_on_first_token(
                            node,
                            &diagnostics::Decorators_cannot_be_applied_to_multiple_get_Slashset_accessors_of_the_same_name,
                            &[],
                        );
                    }
                }

                // if we've seen any modifiers aside from `export`, `default`, or another decorator, then this is an invalid position
                if flags.without(ast::ModifierFlags::EXPORT_DEFAULT | ast::ModifierFlags::DECORATOR)
                    != ast::ModifierFlags::NONE
                {
                    return self.grammar_error_on_node(
                        modifier,
                        &diagnostics::Decorators_are_not_valid_here,
                        &[],
                    );
                }

                // if we've already seen leading decorators and leading modifiers, then trailing decorators are an invalid position
                if has_leading_decorators && flags.intersects(ast::ModifierFlags::MODIFIER) {
                    if first_decorator.is_none() {
                        panic!("Expected firstDecorator to be set");
                    }
                    let source_file =
                        ast::get_source_file_of_node(Some(modifier), &nodes).expect("source file");
                    if !self.has_parse_diagnostics(source_file) {
                        let err = self.error(
                            Some(modifier),
                            &diagnostics::Decorators_may_not_appear_after_export_or_export_default_if_they_also_appear_before_export,
                            &[],
                        );
                        if let Some(err) = &err {
                            let related = crate::checker_b::create_diagnostic_for_node(
                                first_decorator,
                                &nodes,
                                &diagnostics::Decorator_used_before_export_here,
                                &[],
                            );
                            ast::diagnostic::lock_diagnostic(err).add_related_info(Some(related));
                        }
                        return true;
                    }
                    return false;
                }

                flags |= ast::ModifierFlags::DECORATOR;

                // if we have not yet seen a modifier, then these are leading decorators
                if !flags.intersects(ast::ModifierFlags::MODIFIER) {
                    has_leading_decorators = true;
                } else if flags.intersects(ast::ModifierFlags::EXPORT) {
                    saw_export_before_decorators = true;
                }

                if first_decorator.is_none() {
                    first_decorator = Some(modifier);
                }
            } else {
                if nodes[modifier].kind != ast::Kind::ReadonlyKeyword {
                    if matches!(
                        nodes[node].kind,
                        ast::Kind::PropertySignature | ast::Kind::MethodSignature
                    ) {
                        return self.grammar_error_on_node(
                            modifier,
                            &diagnostics::X_0_modifier_cannot_appear_on_a_type_member,
                            &[scanner::token_to_string(nodes[modifier].kind).to_string()],
                        );
                    }
                    if nodes[node].kind == ast::Kind::IndexSignature
                        && (nodes[modifier].kind != ast::Kind::StaticKeyword
                            || !nodes[node]
                                .parent
                                .is_some_and(|p| ast::is_class_like(Some(p), &nodes)))
                    {
                        return self.grammar_error_on_node(
                            modifier,
                            &diagnostics::X_0_modifier_cannot_appear_on_an_index_signature,
                            &[scanner::token_to_string(nodes[modifier].kind).to_string()],
                        );
                    }
                }
                if nodes[modifier].kind != ast::Kind::InKeyword
                    && nodes[modifier].kind != ast::Kind::OutKeyword
                    && nodes[modifier].kind != ast::Kind::ConstKeyword
                    && nodes[node].kind == ast::Kind::TypeParameter
                {
                    return self.grammar_error_on_node(
                        modifier,
                        &diagnostics::X_0_modifier_cannot_appear_on_a_type_parameter,
                        &[scanner::token_to_string(nodes[modifier].kind).to_string()],
                    );
                }
                match nodes[modifier].kind {
                    ast::Kind::ConstKeyword => {
                        if nodes[node].kind != ast::Kind::EnumDeclaration
                            && nodes[node].kind != ast::Kind::TypeParameter
                        {
                            return self.grammar_error_on_node(
                                node,
                                &diagnostics::A_class_member_cannot_have_the_0_keyword,
                                &[scanner::token_to_string(ast::Kind::ConstKeyword).to_string()],
                            );
                        }
                        let parent = nodes[node].parent;
                        if nodes[node].kind == ast::Kind::TypeParameter
                            && !(parent.is_some_and(|p| {
                                ast::is_function_like_declaration(&nodes[p])
                                    || ast::is_class_like(Some(p), &nodes)
                                    || ast::is_function_type_node(&nodes[p])
                                    || ast::is_constructor_type_node(&nodes[p])
                                    || ast::is_call_signature_declaration(&nodes[p])
                                    || ast::is_construct_signature_declaration(&nodes[p])
                                    || ast::is_method_signature_declaration(&nodes[p])
                            }))
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_can_only_appear_on_a_type_parameter_of_a_function_method_or_class,
                                &[scanner::token_to_string(nodes[modifier].kind).to_string()],
                            );
                        }
                    }
                    ast::Kind::OverrideKeyword => {
                        // If node.kind === SyntaxKind.Parameter, checkParameter reports an error if it's not a parameter property.
                        if flags.intersects(ast::ModifierFlags::OVERRIDE) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &["override".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::AMBIENT) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                &["override".to_string(), "declare".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::READONLY)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["override".to_string(), "readonly".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ACCESSOR)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["override".to_string(), "accessor".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ASYNC)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["override".to_string(), "async".to_string()],
                            );
                        }
                        flags |= ast::ModifierFlags::OVERRIDE;
                        last_override = Some(modifier);
                    }
                    ast::Kind::PublicKeyword
                    | ast::Kind::ProtectedKeyword
                    | ast::Kind::PrivateKeyword => {
                        let text = crate::relater::visibility_to_string(ast::modifier_to_flag(
                            nodes[modifier].kind,
                        ));

                        if flags.intersects(ast::ModifierFlags::ACCESSIBILITY_MODIFIER) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::Accessibility_modifier_already_seen,
                                &[],
                            );
                        } else if flags.intersects(ast::ModifierFlags::OVERRIDE)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &[text.to_string(), "override".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::STATIC)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &[text.to_string(), "static".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ACCESSOR)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &[text.to_string(), "accessor".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::READONLY)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &[text.to_string(), "readonly".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ASYNC)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &[text.to_string(), "async".to_string()],
                            );
                        } else if nodes[node].parent.is_some_and(|p| {
                            matches!(
                                nodes[p].kind,
                                ast::Kind::ModuleBlock | ast::Kind::SourceFile
                            )
                        }) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_module_or_namespace_element,
                                &[text.to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ABSTRACT) {
                            if nodes[modifier].kind == ast::Kind::PrivateKeyword {
                                return self.grammar_error_on_node(
                                    modifier,
                                    &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                    &[text.to_string(), "abstract".to_string()],
                                );
                            } else if !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED) {
                                return self.grammar_error_on_node(
                                    modifier,
                                    &diagnostics::X_0_modifier_must_precede_1_modifier,
                                    &[text.to_string(), "abstract".to_string()],
                                );
                            }
                        } else if ast::is_private_identifier_class_element_declaration(
                            &nodes[node],
                            &nodes,
                        ) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::An_accessibility_modifier_cannot_be_used_with_a_private_identifier,
                                &[],
                            );
                        }
                        flags |= ast::modifier_to_flag(nodes[modifier].kind);
                    }
                    ast::Kind::StaticKeyword => {
                        if flags.intersects(ast::ModifierFlags::STATIC) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &["static".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::READONLY)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["static".to_string(), "readonly".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ASYNC)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["static".to_string(), "async".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ACCESSOR)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["static".to_string(), "accessor".to_string()],
                            );
                        } else if nodes[node].parent.is_some_and(|p| {
                            matches!(
                                nodes[p].kind,
                                ast::Kind::ModuleBlock | ast::Kind::SourceFile
                            )
                        }) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_module_or_namespace_element,
                                &["static".to_string()],
                            );
                        } else if nodes[node].kind == ast::Kind::Parameter {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_parameter,
                                &["static".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ABSTRACT) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                &["static".to_string(), "abstract".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::OVERRIDE)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["static".to_string(), "override".to_string()],
                            );
                        }
                        flags |= ast::ModifierFlags::STATIC;
                        last_static = Some(modifier);
                    }
                    ast::Kind::AccessorKeyword => {
                        if flags.intersects(ast::ModifierFlags::ACCESSOR) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &["accessor".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::READONLY) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                &["accessor".to_string(), "readonly".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::AMBIENT) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                &["accessor".to_string(), "declare".to_string()],
                            );
                        } else if nodes[node].kind != ast::Kind::PropertyDeclaration {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_accessor_modifier_can_only_appear_on_a_property_declaration,
                                &[],
                            );
                        }
                        flags |= ast::ModifierFlags::ACCESSOR;
                    }
                    ast::Kind::ReadonlyKeyword => {
                        if flags.intersects(ast::ModifierFlags::READONLY) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &["readonly".to_string()],
                            );
                        } else if nodes[node].kind != ast::Kind::PropertyDeclaration
                            && nodes[node].kind != ast::Kind::PropertySignature
                            && nodes[node].kind != ast::Kind::IndexSignature
                            && nodes[node].kind != ast::Kind::Parameter
                        {
                            // If node.kind === SyntaxKind.Parameter, checkParameter reports an error if it's not a parameter property.
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_readonly_modifier_can_only_appear_on_a_property_declaration_or_index_signature,
                                &[],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ACCESSOR) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                &["readonly".to_string(), "accessor".to_string()],
                            );
                        }
                        flags |= ast::ModifierFlags::READONLY;
                    }
                    ast::Kind::ExportKeyword => {
                        if self.compiler_options.verbatim_module_syntax.is_true()
                            && !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                            && nodes[node].kind != ast::Kind::TypeAliasDeclaration
                            && nodes[node].kind != ast::Kind::InterfaceDeclaration
                            && nodes[node].kind != ast::Kind::ModuleDeclaration
                            && nodes[node]
                                .parent
                                .is_some_and(|p| nodes[p].kind == ast::Kind::SourceFile)
                        {
                            let source_file = ast::get_source_file_of_node(Some(node), &nodes)
                                .expect("source file");
                            if self
                                .program
                                .as_ref()
                                .expect("program")
                                .get_emit_module_format_of_file(nodes[source_file].as_source_file())
                                == ModuleKind::CommonJS
                            {
                                return self.grammar_error_on_node(
                                    modifier,
                                    &diagnostics::A_top_level_export_modifier_cannot_be_used_on_value_declarations_in_a_CommonJS_module_when_verbatimModuleSyntax_is_enabled,
                                    &[],
                                );
                            }
                        }
                        if flags.intersects(ast::ModifierFlags::EXPORT) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &["export".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::AMBIENT)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["export".to_string(), "declare".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ABSTRACT)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["export".to_string(), "abstract".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ASYNC)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["export".to_string(), "async".to_string()],
                            );
                        } else if nodes[node]
                            .parent
                            .is_some_and(|p| ast::is_class_like(Some(p), &nodes))
                            && !ast::is_js_type_alias_declaration(&nodes[node])
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_class_elements_of_this_kind,
                                &["export".to_string()],
                            );
                        } else if nodes[node].kind == ast::Kind::Parameter {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_parameter,
                                &["export".to_string()],
                            );
                        } else if block_scope_kind == ast::NodeFlags::USING {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_using_declaration,
                                &["export".to_string()],
                            );
                        } else if block_scope_kind == ast::NodeFlags::AWAIT_USING {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_an_await_using_declaration,
                                &["export".to_string()],
                            );
                        }
                        flags |= ast::ModifierFlags::EXPORT;
                    }
                    ast::Kind::DefaultKeyword => {
                        let container = if nodes[node]
                            .parent
                            .is_some_and(|p| nodes[p].kind == ast::Kind::SourceFile)
                        {
                            nodes[node].parent
                        } else {
                            nodes[node].parent.and_then(|p| nodes[p].parent)
                        };
                        if container.is_some_and(|c| {
                            nodes[c].kind == ast::Kind::ModuleDeclaration
                                && !ast::is_ambient_module(&nodes[c], &nodes)
                        }) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::A_default_export_can_only_be_used_in_an_ECMAScript_style_module,
                                &[],
                            );
                        } else if block_scope_kind == ast::NodeFlags::USING {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_using_declaration,
                                &["default".to_string()],
                            );
                        } else if block_scope_kind == ast::NodeFlags::AWAIT_USING {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_an_await_using_declaration,
                                &["default".to_string()],
                            );
                        } else if !flags.intersects(ast::ModifierFlags::EXPORT)
                            && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["export".to_string(), "default".to_string()],
                            );
                        } else if saw_export_before_decorators {
                            return self.grammar_error_on_node(
                                first_decorator.expect("firstDecorator"),
                                &diagnostics::Decorators_are_not_valid_here,
                                &[],
                            );
                        }
                        flags |= ast::ModifierFlags::DEFAULT;
                    }
                    ast::Kind::DeclareKeyword => {
                        if flags.intersects(ast::ModifierFlags::AMBIENT) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &["declare".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ASYNC) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_in_an_ambient_context,
                                &["async".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::OVERRIDE) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_in_an_ambient_context,
                                &["override".to_string()],
                            );
                        } else if nodes[node]
                            .parent
                            .is_some_and(|p| ast::is_class_like(Some(p), &nodes))
                            && !ast::is_property_declaration(&nodes[node])
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_class_elements_of_this_kind,
                                &["declare".to_string()],
                            );
                        } else if nodes[node].kind == ast::Kind::Parameter {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_parameter,
                                &["declare".to_string()],
                            );
                        } else if block_scope_kind == ast::NodeFlags::USING {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_using_declaration,
                                &["declare".to_string()],
                            );
                        } else if block_scope_kind == ast::NodeFlags::AWAIT_USING {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_an_await_using_declaration,
                                &["declare".to_string()],
                            );
                        } else if nodes[node].parent.is_some_and(|p| {
                            nodes[p].flags.intersects(ast::NodeFlags::AMBIENT)
                                && nodes[p].kind == ast::Kind::ModuleBlock
                        }) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::A_declare_modifier_cannot_be_used_in_an_already_ambient_context,
                                &[],
                            );
                        } else if ast::is_private_identifier_class_element_declaration(
                            &nodes[node],
                            &nodes,
                        ) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_a_private_identifier,
                                &["declare".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::ACCESSOR) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                &["declare".to_string(), "accessor".to_string()],
                            );
                        }
                        flags |= ast::ModifierFlags::AMBIENT;
                        last_declare = Some(modifier);
                    }
                    ast::Kind::AbstractKeyword => {
                        if flags.intersects(ast::ModifierFlags::ABSTRACT) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &["abstract".to_string()],
                            );
                        }
                        if nodes[node].kind != ast::Kind::ClassDeclaration
                            && nodes[node].kind != ast::Kind::ConstructorType
                        {
                            if !matches!(
                                nodes[node].kind,
                                ast::Kind::MethodDeclaration
                                    | ast::Kind::PropertyDeclaration
                                    | ast::Kind::GetAccessor
                                    | ast::Kind::SetAccessor
                            ) {
                                return self.grammar_error_on_node(
                                    modifier,
                                    &diagnostics::X_abstract_modifier_can_only_appear_on_a_class_method_or_property_declaration,
                                    &[],
                                );
                            }
                            if !(nodes[node].parent.is_some_and(|p| {
                                nodes[p].kind == ast::Kind::ClassDeclaration
                                    && ast::has_syntactic_modifier(
                                        &nodes[p],
                                        ast::ModifierFlags::ABSTRACT,
                                    )
                            })) {
                                let message: &'static diagnostics::Message = if nodes[node].kind
                                    == ast::Kind::PropertyDeclaration
                                {
                                    &diagnostics::Abstract_properties_can_only_appear_within_an_abstract_class
                                } else {
                                    &diagnostics::Abstract_methods_can_only_appear_within_an_abstract_class
                                };
                                return self.grammar_error_on_node(modifier, message, &[]);
                            }
                            if flags.intersects(ast::ModifierFlags::STATIC) {
                                return self.grammar_error_on_node(
                                    modifier,
                                    &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                    &["static".to_string(), "abstract".to_string()],
                                );
                            }
                            if flags.intersects(ast::ModifierFlags::PRIVATE) {
                                return self.grammar_error_on_node(
                                    modifier,
                                    &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                    &["private".to_string(), "abstract".to_string()],
                                );
                            }
                            if flags.intersects(ast::ModifierFlags::ASYNC)
                                && let Some(last_async) = last_async
                            {
                                return self.grammar_error_on_node(
                                    last_async,
                                    &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                    &["async".to_string(), "abstract".to_string()],
                                );
                            }
                            if flags.intersects(ast::ModifierFlags::OVERRIDE)
                                && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                            {
                                return self.grammar_error_on_node(
                                    modifier,
                                    &diagnostics::X_0_modifier_must_precede_1_modifier,
                                    &["abstract".to_string(), "override".to_string()],
                                );
                            }
                            if flags.intersects(ast::ModifierFlags::ACCESSOR)
                                && !nodes[modifier].flags.intersects(ast::NodeFlags::REPARSED)
                            {
                                return self.grammar_error_on_node(
                                    modifier,
                                    &diagnostics::X_0_modifier_must_precede_1_modifier,
                                    &["abstract".to_string(), "accessor".to_string()],
                                );
                            }
                        }
                        if let Some(name) = nodes[node].name()
                            && nodes[name].kind == ast::Kind::PrivateIdentifier
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_a_private_identifier,
                                &["abstract".to_string()],
                            );
                        }
                        flags |= ast::ModifierFlags::ABSTRACT;
                    }
                    ast::Kind::AsyncKeyword => {
                        if flags.intersects(ast::ModifierFlags::ASYNC) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &["async".to_string()],
                            );
                        } else if flags.intersects(ast::ModifierFlags::AMBIENT)
                            || nodes[node]
                                .parent
                                .is_some_and(|p| nodes[p].flags.intersects(ast::NodeFlags::AMBIENT))
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_in_an_ambient_context,
                                &["async".to_string()],
                            );
                        } else if nodes[node].kind == ast::Kind::Parameter {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_appear_on_a_parameter,
                                &["async".to_string()],
                            );
                        }
                        if flags.intersects(ast::ModifierFlags::ABSTRACT) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_cannot_be_used_with_1_modifier,
                                &["async".to_string(), "abstract".to_string()],
                            );
                        }
                        flags |= ast::ModifierFlags::ASYNC;
                        last_async = Some(modifier);
                    }
                    ast::Kind::InKeyword | ast::Kind::OutKeyword => {
                        let in_out_flag = if nodes[modifier].kind == ast::Kind::InKeyword {
                            ast::ModifierFlags::IN
                        } else {
                            ast::ModifierFlags::OUT
                        };
                        let in_out_text = if nodes[modifier].kind == ast::Kind::InKeyword {
                            "in"
                        } else {
                            "out"
                        };
                        let parent = nodes[node].parent;
                        if nodes[node].kind != ast::Kind::TypeParameter
                            || parent.is_some_and(|p| {
                                !(ast::is_interface_declaration(&nodes[p])
                                    || ast::is_class_like(Some(p), &nodes)
                                    || ast::is_type_or_js_type_alias_declaration(&nodes[p]))
                            })
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_can_only_appear_on_a_type_parameter_of_a_class_interface_or_type_alias,
                                &[in_out_text.to_string()],
                            );
                        }
                        if flags.intersects(in_out_flag) {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_already_seen,
                                &[in_out_text.to_string()],
                            );
                        }
                        if in_out_flag == ast::ModifierFlags::IN
                            && flags.intersects(ast::ModifierFlags::OUT)
                        {
                            return self.grammar_error_on_node(
                                modifier,
                                &diagnostics::X_0_modifier_must_precede_1_modifier,
                                &["in".to_string(), "out".to_string()],
                            );
                        }
                        flags |= in_out_flag;
                    }
                    _ => {}
                }
            }
        }

        if nodes[node].kind == ast::Kind::Constructor {
            if flags.intersects(ast::ModifierFlags::STATIC) {
                return self.grammar_error_on_node(
                    last_static.expect("lastStatic"),
                    &diagnostics::X_0_modifier_cannot_appear_on_a_constructor_declaration,
                    &["static".to_string()],
                );
            }
            if flags.intersects(ast::ModifierFlags::OVERRIDE) {
                return self.grammar_error_on_node(
                    last_override.expect("lastOverride"),
                    &diagnostics::X_0_modifier_cannot_appear_on_a_constructor_declaration,
                    &["override".to_string()],
                );
            }
            if flags.intersects(ast::ModifierFlags::ASYNC) {
                return self.grammar_error_on_node(
                    last_async.expect("lastAsync"),
                    &diagnostics::X_0_modifier_cannot_appear_on_a_constructor_declaration,
                    &["async".to_string()],
                );
            }
            return false;
        } else if matches!(
            nodes[node].kind,
            ast::Kind::ImportDeclaration
                | ast::Kind::JSImportDeclaration
                | ast::Kind::ImportEqualsDeclaration
        ) && flags.intersects(ast::ModifierFlags::AMBIENT)
        {
            return self.grammar_error_on_node(
                last_declare.expect("lastDeclare"),
                &diagnostics::A_0_modifier_cannot_be_used_with_an_import_declaration,
                &["declare".to_string()],
            );
        } else if nodes[node].kind == ast::Kind::Parameter
            && flags.intersects(ast::ModifierFlags::PARAMETER_PROPERTY_MODIFIER)
            && nodes[node]
                .name()
                .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
        {
            return self.grammar_error_on_node(
                node,
                &diagnostics::A_parameter_property_may_not_be_declared_using_a_binding_pattern,
                &[],
            );
        } else if nodes[node].kind == ast::Kind::Parameter
            && flags.intersects(ast::ModifierFlags::PARAMETER_PROPERTY_MODIFIER)
            && nodes[node]
                .as_parameter_declaration()
                .dot_dot_dot_token
                .is_some()
        {
            return self.grammar_error_on_node(
                node,
                &diagnostics::A_parameter_property_cannot_be_declared_using_a_rest_parameter,
                &[],
            );
        }
        if flags.intersects(ast::ModifierFlags::ASYNC) {
            return self.check_grammar_async_modifier(node, last_async);
        }
        false
    }

    /// `func (c *Checker) reportObviousModifierErrors` (grammarchecks.go:571).
    pub(crate) fn report_obvious_modifier_errors(&mut self, node: NodeId) -> bool {
        let Some(modifier) = self.find_first_illegal_modifier(node) else {
            return false;
        };
        self.grammar_error_on_first_token(modifier, &diagnostics::Modifiers_cannot_appear_here, &[])
    }

    /// `func (c *Checker) findFirstModifierExcept` (grammarchecks.go:579).
    pub(crate) fn find_first_modifier_except(
        &mut self,
        node: NodeId,
        allowed_modifier: ast::Kind,
    ) -> Option<NodeId> {
        let nodes = self.program_nodes(node);
        let modifier = nodes[node]
            .modifier_nodes()
            .and_then(|mods| mods.iter().copied().find(|&m| ast::is_modifier(&nodes[m])));
        if let Some(modifier) = modifier
            && nodes[modifier].kind != allowed_modifier
        {
            return Some(modifier);
        }
        None
    }

    /// `func (c *Checker) findFirstIllegalModifier` (grammarchecks.go:587).
    pub(crate) fn find_first_illegal_modifier(&mut self, node: NodeId) -> Option<NodeId> {
        let nodes = self.program_nodes(node);
        match nodes[node].kind {
            ast::Kind::GetAccessor
            | ast::Kind::SetAccessor
            | ast::Kind::Constructor
            | ast::Kind::PropertyDeclaration
            | ast::Kind::PropertySignature
            | ast::Kind::MethodDeclaration
            | ast::Kind::MethodSignature
            | ast::Kind::IndexSignature
            | ast::Kind::ModuleDeclaration
            | ast::Kind::ImportDeclaration
            | ast::Kind::JSImportDeclaration
            | ast::Kind::ImportEqualsDeclaration
            | ast::Kind::ExportDeclaration
            | ast::Kind::ExportAssignment
            | ast::Kind::FunctionExpression
            | ast::Kind::ArrowFunction
            | ast::Kind::Parameter
            | ast::Kind::TypeParameter
            | ast::Kind::JSTypeAliasDeclaration => None,
            ast::Kind::ClassStaticBlockDeclaration
            | ast::Kind::PropertyAssignment
            | ast::Kind::ShorthandPropertyAssignment
            | ast::Kind::NamespaceExportDeclaration
            | ast::Kind::MissingDeclaration => nodes[node]
                .modifier_nodes()
                .and_then(|mods| mods.iter().copied().find(|&m| ast::is_modifier(&nodes[m]))),
            _ => {
                if nodes[node].parent.is_some_and(|p| {
                    matches!(
                        nodes[p].kind,
                        ast::Kind::ModuleBlock | ast::Kind::SourceFile
                    )
                }) {
                    return None;
                }
                match nodes[node].kind {
                    ast::Kind::FunctionDeclaration => {
                        self.find_first_modifier_except(node, ast::Kind::AsyncKeyword)
                    }
                    ast::Kind::ClassDeclaration | ast::Kind::ConstructorType => {
                        self.find_first_modifier_except(node, ast::Kind::AbstractKeyword)
                    }
                    ast::Kind::ClassExpression
                    | ast::Kind::InterfaceDeclaration
                    | ast::Kind::TypeAliasDeclaration => {
                        nodes[node].modifier_nodes().and_then(|mods| {
                            mods.iter().copied().find(|&m| ast::is_modifier(&nodes[m]))
                        })
                    }
                    ast::Kind::VariableStatement => {
                        if nodes[node]
                            .as_variable_statement()
                            .declaration_list
                            .is_some_and(|d| nodes[d].flags.intersects(ast::NodeFlags::USING))
                        {
                            return self.find_first_modifier_except(node, ast::Kind::AwaitKeyword);
                        }
                        nodes[node].modifier_nodes().and_then(|mods| {
                            mods.iter().copied().find(|&m| ast::is_modifier(&nodes[m]))
                        })
                    }
                    ast::Kind::EnumDeclaration => {
                        self.find_first_modifier_except(node, ast::Kind::ConstKeyword)
                    }
                    _ => panic!("Unhandled case in findFirstIllegalModifier."),
                }
            }
        }
    }

    /// `func (c *Checker) reportObviousDecoratorErrors` (grammarchecks.go:642).
    pub(crate) fn report_obvious_decorator_errors(&mut self, node: NodeId) -> bool {
        let Some(decorator) = self.find_first_illegal_decorator(node) else {
            return false;
        };
        self.grammar_error_on_first_token(
            decorator,
            &diagnostics::Decorators_are_not_valid_here,
            &[],
        )
    }

    /// `func (c *Checker) findFirstIllegalDecorator` (grammarchecks.go:650).
    pub(crate) fn find_first_illegal_decorator(&mut self, node: NodeId) -> Option<NodeId> {
        let nodes = self.program_nodes(node);
        if ast::can_have_illegal_decorators(&nodes[node]) {
            return nodes[node]
                .modifier_nodes()
                .and_then(|mods| mods.iter().copied().find(|&m| ast::is_decorator(&nodes[m])));
        }
        None
    }

    /// `func (c *Checker) checkGrammarAsyncModifier` (grammarchecks.go:659).
    pub(crate) fn check_grammar_async_modifier(
        &mut self,
        node: NodeId,
        async_modifier: Option<NodeId>,
    ) -> bool {
        let nodes = self.program_nodes(node);
        match nodes[node].kind {
            ast::Kind::MethodDeclaration
            | ast::Kind::FunctionDeclaration
            | ast::Kind::FunctionExpression
            | ast::Kind::ArrowFunction => return false,
            _ => {}
        }
        self.grammar_error_on_node(
            async_modifier.expect("asyncModifier"),
            &diagnostics::X_0_modifier_cannot_be_used_here,
            &["async".to_string()],
        )
    }

    /// `func (c *Checker) checkGrammarForDisallowedTrailingComma` (grammarchecks.go:671).
    pub(crate) fn check_grammar_for_disallowed_trailing_comma(
        &mut self,
        list: Option<&ast::NodeList>,
        diag: &'static diagnostics::Message,
        nodes: &[ast::Node],
    ) -> bool {
        if let Some(list) = list
            && list.has_trailing_comma(nodes)
        {
            let first = list.nodes()[0];
            return self.grammar_error_at_pos(
                first,
                list.end() - ",".len() as i32,
                ",".len() as i32,
                diag,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarTypeParameterList` (grammarchecks.go:678).
    /// `file` is the source file node (`*ast.SourceFile` → `NodeId`).
    pub(crate) fn check_grammar_type_parameter_list(
        &mut self,
        type_parameters: Option<&ast::NodeList>,
        file: NodeId,
    ) -> bool {
        if let Some(type_parameters) = type_parameters
            && type_parameters.nodes().is_empty()
        {
            let nodes = self.program_nodes(file);
            let sf = nodes[file].as_source_file();
            let start = type_parameters.pos() - "<".len() as i32;
            let end = scanner::skip_trivia(&sf.text, type_parameters.end()) + ">".len() as i32;
            return self.grammar_error_at_pos(
                file,
                start,
                end - start,
                &diagnostics::Type_parameter_list_cannot_be_empty,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarParameterList` (grammarchecks.go:687).
    pub(crate) fn check_grammar_parameter_list(&mut self, parameters: &ast::NodeList) -> bool {
        if parameters.nodes().is_empty() {
            return false;
        }
        let nodes_rc = self.program_nodes(parameters.nodes()[0]);
        let nodes: &[ast::Node] = &nodes_rc;
        let mut seen_optional_parameter = false;
        let parameter_count = parameters.nodes().len();

        for i in 0..parameter_count {
            let parameter_id = parameters.nodes()[i];
            let parameter = nodes[parameter_id].as_parameter_declaration();
            let (dot_dot_dot_token, question_token, initializer, name, param_flags) = (
                parameter.dot_dot_dot_token,
                parameter.question_token,
                parameter.initializer,
                parameter.name,
                nodes[parameter_id].flags,
            );
            if dot_dot_dot_token.is_some() {
                if i != parameter_count - 1 {
                    return self.grammar_error_on_node(
                        dot_dot_dot_token.expect("dotDotDotToken"),
                        &diagnostics::A_rest_parameter_must_be_last_in_a_parameter_list,
                        &[],
                    );
                }
                if !param_flags.intersects(ast::NodeFlags::AMBIENT) {
                    self.check_grammar_for_disallowed_trailing_comma(
                        Some(parameters),
                        &diagnostics::A_rest_parameter_or_binding_pattern_may_not_have_a_trailing_comma,
                        nodes,
                    );
                }

                if question_token.is_some() {
                    return self.grammar_error_on_node(
                        question_token.expect("questionToken"),
                        &diagnostics::A_rest_parameter_cannot_be_optional,
                        &[],
                    );
                }

                if initializer.is_some() {
                    return self.grammar_error_on_node(
                        name.expect("name"),
                        &diagnostics::A_rest_parameter_cannot_have_an_initializer,
                        &[],
                    );
                }
            } else if crate::utilities::is_optional_declaration(&nodes[parameter_id], nodes) {
                seen_optional_parameter = true;
                // A reparsed '?' token indicates a bracketed name in @param tag
                if let Some(question_token) = question_token
                    && !nodes[question_token]
                        .flags
                        .intersects(ast::NodeFlags::REPARSED)
                    && initializer.is_some()
                {
                    return self.grammar_error_on_node(
                        name.expect("name"),
                        &diagnostics::Parameter_cannot_have_question_mark_and_initializer,
                        &[],
                    );
                }
            } else if seen_optional_parameter && initializer.is_none() {
                return self.grammar_error_on_node(
                    name.expect("name"),
                    &diagnostics::A_required_parameter_cannot_follow_an_optional_parameter,
                    &[],
                );
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarForUseStrictSimpleParameterList` (grammarchecks.go:722).
    pub(crate) fn check_grammar_for_use_strict_simple_parameter_list(
        &mut self,
        node: NodeId,
    ) -> bool {
        if self.language_version >= ScriptTarget::ES2016 {
            let nodes = self.program_nodes(node);
            let body = nodes[node].body();
            let mut use_strict_directive: Option<NodeId> = None;
            if let Some(body) = body
                && ast::is_block(&nodes[body])
            {
                let source_file =
                    ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
                let statements: Vec<NodeId> = nodes[body]
                    .statements()
                    .map(|s| s.to_vec())
                    .unwrap_or_default();
                use_strict_directive = tsc_binder::binder::find_use_strict_prologue(
                    nodes[source_file].as_source_file(),
                    &statements,
                    &nodes,
                );
            }
            if let Some(use_strict_directive) = use_strict_directive {
                let non_simple_parameters: Vec<NodeId> = nodes[node]
                    .parameters()
                    .map(|params| {
                        params
                            .iter()
                            .copied()
                            .filter(|&n| {
                                let parameter = nodes[n].as_parameter_declaration();
                                parameter.initializer.is_some()
                                    || parameter
                                        .name
                                        .is_some_and(|name| ast::is_binding_pattern(&nodes[name]))
                                    || parameter.dot_dot_dot_token.is_some()
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                if !non_simple_parameters.is_empty() {
                    for &parameter in &non_simple_parameters {
                        let err = self.error(
                            Some(parameter),
                            &diagnostics::This_parameter_is_not_allowed_with_use_strict_directive,
                            &[],
                        );
                        if let Some(err) = &err {
                            let related = crate::checker_b::create_diagnostic_for_node(
                                Some(use_strict_directive),
                                &nodes,
                                &diagnostics::X_use_strict_directive_used_here,
                                &[],
                            );
                            ast::diagnostic::lock_diagnostic(err).add_related_info(Some(related));
                        }
                    }

                    let err = self.error(
                        Some(use_strict_directive),
                        &diagnostics::X_use_strict_directive_cannot_be_used_with_non_simple_parameter_list,
                        &[],
                    );
                    if let Some(err) = &err {
                        for (index, &parameter) in non_simple_parameters.iter().enumerate() {
                            let related_message = if index == 0 {
                                &diagnostics::Non_simple_parameter_declared_here
                            } else {
                                &diagnostics::X_and_here
                            };
                            let related = crate::checker_b::create_diagnostic_for_node(
                                Some(parameter),
                                &nodes,
                                related_message,
                                &[],
                            );
                            ast::diagnostic::lock_diagnostic(err).add_related_info(Some(related));
                        }
                    }

                    return true;
                }
            }
        }
        false
    }

    /// `func (c *Checker) checkGrammarFunctionLikeDeclaration` (grammarchecks.go:758).
    pub(crate) fn check_grammar_function_like_declaration(&mut self, node: NodeId) -> bool {
        // Prevent cascading error by short-circuit
        let nodes = self.program_nodes(node);
        let file = ast::get_source_file_of_node(Some(node), &nodes);
        let (type_parameters, parameters) = nodes[node]
            .function_like_data()
            .map(|d| (d.type_parameters.clone(), d.parameters.clone()))
            .unwrap_or_default();
        self.check_grammar_modifiers(node)
            || self.check_grammar_type_parameter_list(type_parameters.as_ref(), file.expect("file"))
            || self.check_grammar_parameter_list(parameters.as_ref().expect("parameters"))
            || self.check_grammar_arrow_function(node, file.expect("file"))
            || (ast::is_function_like_declaration(&nodes[node])
                && self.check_grammar_for_use_strict_simple_parameter_list(node))
    }

    /// `func (c *Checker) checkGrammarClassLikeDeclaration` (grammarchecks.go:767).
    pub(crate) fn check_grammar_class_like_declaration(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let file = ast::get_source_file_of_node(Some(node), &nodes);
        let type_parameter_list = nodes[node].type_parameter_list().cloned();
        self.check_grammar_class_declaration_heritage_clauses(node, file.expect("file"))
            || self.check_grammar_type_parameter_list(
                type_parameter_list.as_ref(),
                file.expect("file"),
            )
    }

    /// `func (c *Checker) checkGrammarArrowFunction` (grammarchecks.go:772).
    /// `file` is the source file node (`*ast.SourceFile` → `NodeId`).
    pub(crate) fn check_grammar_arrow_function(&mut self, node: NodeId, file: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if !ast::is_arrow_function(&nodes[node]) {
            return false;
        }

        let arrow_func = nodes[node].as_arrow_function();
        if let Some(type_parameters) = arrow_func
            .function_like_with_body_base
            .function_like_base
            .type_parameters
            .as_ref()
        {
            let type_param_nodes = type_parameters.nodes();
            let has_constraint = !type_param_nodes.is_empty()
                && nodes[type_param_nodes[0]]
                    .as_type_parameter_declaration()
                    .constraint
                    .is_some();
            if !(type_param_nodes.len() > 1
                || type_parameters.has_trailing_comma(&nodes)
                || has_constraint)
            {
                let sf = nodes[file].as_source_file();
                if sf
                    .file_name()
                    .extension_is_one_of(&[tsc_tspath::EXTENSION_MTS, tsc_tspath::EXTENSION_CTS])
                {
                    // TODO(danielr): should we return early here?
                    self.grammar_error_on_node(
                        type_param_nodes[0],
                        &diagnostics::This_syntax_is_reserved_in_files_with_the_mts_or_cts_extension_Add_a_trailing_comma_or_explicit_constraint,
                        &[],
                    );
                }
            }
        }

        let equals_greater_than_token = arrow_func.equals_greater_than_token.expect("=>");
        let sf = nodes[file].as_source_file();
        let arrow_full_text = sf.text[nodes[equals_greater_than_token].pos() as usize
            ..nodes[equals_greater_than_token].end() as usize]
            .to_string();
        arrow_full_text.chars().any(stringutil::is_line_break)
            && self.grammar_error_on_node(
                equals_greater_than_token,
                &diagnostics::Line_terminator_not_permitted_before_arrow,
                &[],
            )
    }

    /// `func (c *Checker) checkGrammarIndexSignatureParameters` (grammarchecks.go:796).
    pub(crate) fn check_grammar_index_signature_parameters(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let sig = nodes[node].as_index_signature_declaration();
        let param_nodes: Vec<NodeId> = sig
            .parameter_list()
            .map(|p| p.nodes().to_vec())
            .unwrap_or_default();

        if param_nodes.is_empty() {
            return self.grammar_error_on_node(
                node,
                &diagnostics::An_index_signature_must_have_exactly_one_parameter,
                &[],
            );
        }

        let parameter_id = param_nodes[0];
        if param_nodes.len() != 1 {
            let name = nodes[parameter_id].name().expect("name");
            return self.grammar_error_on_node(
                name,
                &diagnostics::An_index_signature_must_have_exactly_one_parameter,
                &[],
            );
        }

        let parameter_list = nodes[node]
            .as_index_signature_declaration()
            .parameter_list()
            .cloned();
        self.check_grammar_for_disallowed_trailing_comma(
            parameter_list.as_ref(),
            &diagnostics::An_index_signature_cannot_have_a_trailing_comma,
            &nodes,
        );
        let parameter = nodes[parameter_id].as_parameter_declaration();
        let (dot_dot_dot_token, question_token, initializer, name, type_node) = (
            parameter.dot_dot_dot_token,
            parameter.question_token,
            parameter.initializer,
            parameter.name,
            parameter.type_,
        );
        if dot_dot_dot_token.is_some() {
            return self.grammar_error_on_node(
                dot_dot_dot_token.expect("dotDotDotToken"),
                &diagnostics::An_index_signature_cannot_have_a_rest_parameter,
                &[],
            );
        }
        if nodes[parameter_id].modifiers().is_some() {
            return self.grammar_error_on_node(
                name.expect("name"),
                &diagnostics::An_index_signature_parameter_cannot_have_an_accessibility_modifier,
                &[],
            );
        }
        if question_token.is_some() {
            return self.grammar_error_on_node(
                question_token.expect("questionToken"),
                &diagnostics::An_index_signature_parameter_cannot_have_a_question_mark,
                &[],
            );
        }
        if initializer.is_some() {
            return self.grammar_error_on_node(
                name.expect("name"),
                &diagnostics::An_index_signature_parameter_cannot_have_an_initializer,
                &[],
            );
        }
        let Some(type_node) = type_node else {
            return self.grammar_error_on_node(
                name.expect("name"),
                &diagnostics::An_index_signature_parameter_must_have_a_type_annotation,
                &[],
            );
        };
        let t = self.get_type_from_type_node(type_node);
        if crate::checker_d::some_type(self, t, |c, t| {
            c.types
                .get(t)
                .flags
                .intersects(crate::types::TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE)
        }) || self.is_generic_type(t)
        {
            return self.grammar_error_on_node(
                name.expect("name"),
                &diagnostics::An_index_signature_parameter_type_cannot_be_a_literal_type_or_generic_type_Consider_using_a_mapped_object_type_instead,
                &[],
            );
        }
        if !crate::checker_d::every_type(self, t, |c, t| c.is_valid_index_key_type(t)) {
            return self.grammar_error_on_node(
                name.expect("name"),
                &diagnostics::An_index_signature_parameter_type_must_be_string_number_symbol_or_a_template_literal_type,
                &[],
            );
        }
        if nodes[node]
            .as_index_signature_declaration()
            .function_like_base
            .type_
            .is_none()
        {
            return self.grammar_error_on_node(
                node,
                &diagnostics::An_index_signature_must_have_a_type_annotation,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarIndexSignature` (grammarchecks.go:840).
    pub(crate) fn check_grammar_index_signature(&mut self, node: NodeId) -> bool {
        // Prevent cascading error by short-circuit
        self.check_grammar_modifiers(node) || self.check_grammar_index_signature_parameters(node)
    }

    /// `func (c *Checker) checkGrammarForAtLeastOneTypeArgument` (grammarchecks.go:845).
    pub(crate) fn check_grammar_for_at_least_one_type_argument(
        &mut self,
        node: NodeId,
        type_arguments: Option<&ast::NodeList>,
    ) -> bool {
        if let Some(type_arguments) = type_arguments
            && type_arguments.nodes().is_empty()
        {
            let nodes = self.program_nodes(node);
            let source_file =
                ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
            let sf = nodes[source_file].as_source_file();
            let start = type_arguments.pos() - "<".len() as i32;
            let end = scanner::skip_trivia(&sf.text, type_arguments.end()) + ">".len() as i32;
            return self.grammar_error_at_pos(
                source_file,
                start,
                end - start,
                &diagnostics::Type_argument_list_cannot_be_empty,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarTypeArguments` (grammarchecks.go:855).
    pub(crate) fn check_grammar_type_arguments(
        &mut self,
        node: NodeId,
        type_arguments: Option<&ast::NodeList>,
    ) -> bool {
        let nodes = self.program_nodes(node);
        self.check_grammar_for_disallowed_trailing_comma(
            type_arguments,
            &diagnostics::Trailing_comma_not_allowed,
            &nodes,
        ) || self.check_grammar_for_at_least_one_type_argument(node, type_arguments)
    }

    /// `func (c *Checker) checkGrammarTaggedTemplateChain` (grammarchecks.go:859).
    pub(crate) fn check_grammar_tagged_template_chain(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let data = nodes[node].as_tagged_template_expression();
        if data.question_dot_token.is_some()
            || nodes[node].flags.intersects(ast::NodeFlags::OPTIONAL_CHAIN)
        {
            let template = data.template.expect("template");
            return self.grammar_error_on_node(
                template,
                &diagnostics::Tagged_template_expressions_are_not_permitted_in_an_optional_chain,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarHeritageClause` (grammarchecks.go:866).
    pub(crate) fn check_grammar_heritage_clause(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let types = nodes[node].as_heritage_clause().types.clone();
        if self.check_grammar_for_disallowed_trailing_comma(
            types.as_ref(),
            &diagnostics::Trailing_comma_not_allowed,
            &nodes,
        ) {
            return true;
        }
        if let Some(types) = &types
            && types.nodes().is_empty()
        {
            let list_type = scanner::token_to_string(nodes[node].as_heritage_clause().token);
            // TODO(danielr): why not error on the token?
            return self.grammar_error_at_pos(
                node,
                types.pos(),
                0,
                &diagnostics::X_0_list_cannot_be_empty,
                &[list_type.to_string()],
            );
        }

        if let Some(types) = &types {
            for &t in types.nodes() {
                if self.check_grammar_expression_with_type_arguments(t) {
                    return true;
                }
            }
        }
        false
    }

    /// `func (c *Checker) checkGrammarExpressionWithTypeArguments` (grammarchecks.go:885).
    pub(crate) fn check_grammar_expression_with_type_arguments(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if ast::is_expression_with_type_arguments(&nodes[node])
            && nodes[node]
                .expression()
                .is_some_and(|e| nodes[e].kind == ast::Kind::ImportKeyword)
            && nodes[node].type_argument_list().is_some()
        {
            return self.grammar_error_on_node(
                node,
                &diagnostics::This_use_of_import_is_invalid_import_calls_can_be_written_but_they_must_have_parentheses_and_cannot_have_type_arguments,
                &[],
            );
        }
        let type_argument_list = nodes[node].type_argument_list().cloned();
        self.check_grammar_type_arguments(node, type_argument_list.as_ref())
    }

    /// `func (c *Checker) checkGrammarClassDeclarationHeritageClauses` (grammarchecks.go:892).
    /// `file` is the source file node (`*ast.SourceFile` → `NodeId`).
    pub(crate) fn check_grammar_class_declaration_heritage_clauses(
        &mut self,
        node: NodeId,
        _file: NodeId,
    ) -> bool {
        let mut seen_extends_clause = false;
        let mut seen_implements_clause = false;

        let nodes = self.program_nodes(node);
        let heritage_clauses = nodes[node]
            .class_like_data()
            .and_then(|d| d.heritage_clauses.clone());

        if !self.check_grammar_modifiers(node)
            && let Some(heritage_clauses) = heritage_clauses
        {
            let nodes = self.program_nodes(node);
            for heritage_clause_node in heritage_clauses.nodes().to_vec() {
                let token = nodes[heritage_clause_node].as_heritage_clause().token;
                if token == ast::Kind::ExtendsKeyword {
                    if seen_extends_clause {
                        return self.grammar_error_on_first_token(
                            heritage_clause_node,
                            &diagnostics::X_extends_clause_already_seen,
                            &[],
                        );
                    }

                    if seen_implements_clause {
                        return self.grammar_error_on_first_token(
                            heritage_clause_node,
                            &diagnostics::X_extends_clause_must_precede_implements_clause,
                            &[],
                        );
                    }

                    let type_nodes = nodes[heritage_clause_node]
                        .as_heritage_clause()
                        .types
                        .as_ref()
                        .map(|t| t.nodes().to_vec())
                        .unwrap_or_default();
                    if type_nodes.len() > 1 {
                        return self.grammar_error_on_first_token(
                            type_nodes[1],
                            &diagnostics::Classes_can_only_extend_a_single_class,
                            &[],
                        );
                    }

                    seen_extends_clause = true;
                } else {
                    if token != ast::Kind::ImplementsKeyword {
                        panic!("Unexpected token {:?}", token);
                    }
                    if seen_implements_clause {
                        return self.grammar_error_on_first_token(
                            heritage_clause_node,
                            &diagnostics::X_implements_clause_already_seen,
                            &[],
                        );
                    }

                    seen_implements_clause = true;
                }

                // Grammar checking heritageClause inside class declaration
                self.check_grammar_heritage_clause(heritage_clause_node);
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarInterfaceDeclaration` (grammarchecks.go:935).
    pub(crate) fn check_grammar_interface_declaration(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let heritage_clauses = nodes[node]
            .class_like_data()
            .and_then(|d| d.heritage_clauses.clone());
        if let Some(heritage_clauses) = heritage_clauses {
            let mut seen_extends_clause = false;
            for heritage_clause_node in heritage_clauses.nodes().to_vec() {
                let token = nodes[heritage_clause_node].as_heritage_clause().token;

                match token {
                    ast::Kind::ExtendsKeyword => {
                        if seen_extends_clause {
                            return self.grammar_error_on_first_token(
                                heritage_clause_node,
                                &diagnostics::X_extends_clause_already_seen,
                                &[],
                            );
                        }
                        seen_extends_clause = true;
                    }
                    ast::Kind::ImplementsKeyword => {
                        return self.grammar_error_on_first_token(
                            heritage_clause_node,
                            &diagnostics::Interface_declaration_cannot_have_implements_clause,
                            &[],
                        );
                    }
                    _ => panic!("Unexpected token {:?}", token),
                }

                // Grammar checking heritageClause inside class declaration
                self.check_grammar_heritage_clause(heritage_clause_node);
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarComputedPropertyName` (grammarchecks.go:961).
    pub(crate) fn check_grammar_computed_property_name(&mut self, node: NodeId) -> bool {
        // If node is not a computedPropertyName, just skip the grammar checking
        let nodes = self.program_nodes(node);
        if nodes[node].kind != ast::Kind::ComputedPropertyName {
            return false;
        }

        let expression = nodes[node]
            .as_computed_property_name()
            .expression
            .expect("computed property name expression");
        if nodes[expression].kind == ast::Kind::BinaryExpression
            && nodes[expression].as_binary_expression().operator_token == ast::Kind::CommaToken
        {
            return self.grammar_error_on_node(
                expression,
                &diagnostics::A_comma_expression_is_not_allowed_in_a_computed_property_name,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarForGenerator` (grammarchecks.go:974).
    pub(crate) fn check_grammar_for_generator(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if let Some(body_data) = nodes[node].body_data()
            && let Some(asterisk_token) = body_data.asterisk_token
        {
            if !matches!(
                nodes[node].kind,
                ast::Kind::FunctionDeclaration
                    | ast::Kind::FunctionExpression
                    | ast::Kind::MethodDeclaration
            ) {
                panic!("Unexpected node kind {:?}", nodes[node].kind);
            }
            if nodes[node].flags.intersects(ast::NodeFlags::AMBIENT) {
                return self.grammar_error_on_node(
                    asterisk_token,
                    &diagnostics::Generators_are_not_allowed_in_an_ambient_context,
                    &[],
                );
            }
            if body_data.body.is_none() {
                return self.grammar_error_on_node(
                    asterisk_token,
                    &diagnostics::An_overload_signature_cannot_be_declared_as_a_generator,
                    &[],
                );
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarForInvalidQuestionMark` (grammarchecks.go:990).
    pub(crate) fn check_grammar_for_invalid_question_mark(
        &mut self,
        postfix_token: Option<NodeId>,
        message: &'static diagnostics::Message,
    ) -> bool {
        let nodes = match postfix_token {
            Some(t) => self.program_nodes(t),
            None => return false,
        };
        postfix_token.is_some()
            && nodes[postfix_token.unwrap()].kind == ast::Kind::QuestionToken
            && self.grammar_error_on_node(postfix_token.unwrap(), message, &[])
    }

    /// `func (c *Checker) checkGrammarForInvalidExclamationToken` (grammarchecks.go:994).
    pub(crate) fn check_grammar_for_invalid_exclamation_token(
        &mut self,
        postfix_token: Option<NodeId>,
        message: &'static diagnostics::Message,
    ) -> bool {
        let nodes = match postfix_token {
            Some(t) => self.program_nodes(t),
            None => return false,
        };
        postfix_token.is_some()
            && nodes[postfix_token.unwrap()].kind == ast::Kind::ExclamationToken
            && self.grammar_error_on_node(postfix_token.unwrap(), message, &[])
    }

    /// `func (c *Checker) checkGrammarObjectLiteralExpression` (grammarchecks.go:998).
    pub(crate) fn check_grammar_object_literal_expression(
        &mut self,
        node: NodeId,
        in_destructuring: bool,
    ) -> bool {
        let mut seen: FxHashMap<String, DeclarationMeaning> = FxHashMap::default();

        let nodes = self.program_nodes(node);
        let properties: Vec<NodeId> = nodes[node]
            .properties()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        for prop in properties {
            if nodes[prop].kind == ast::Kind::SpreadAssignment {
                if in_destructuring {
                    // a rest property cannot be destructured any further
                    let spread_expr = nodes[prop]
                        .as_spread_assignment()
                        .expression
                        .expect("spread expression");
                    let expression = ast::skip_parentheses(spread_expr, &nodes);
                    if ast::is_array_literal_expression(&nodes[expression])
                        || ast::is_object_literal_expression(&nodes[expression])
                    {
                        return self.grammar_error_on_node(
                            spread_expr,
                            &diagnostics::A_rest_element_cannot_contain_a_binding_pattern,
                            &[],
                        );
                    }
                }
                continue;
            }
            let Some(name) = nodes[prop].name() else {
                panic!("prop must have a name");
            };
            if nodes[name].kind == ast::Kind::ComputedPropertyName {
                // If the name is not a ComputedPropertyName, the grammar checking will skip it
                self.check_grammar_computed_property_name(name);
            }

            if nodes[prop].kind == ast::Kind::ShorthandPropertyAssignment && !in_destructuring {
                let shorthand_prop = nodes[prop].as_shorthand_property_assignment();
                if let Some(object_assignment_initializer) =
                    shorthand_prop.object_assignment_initializer
                {
                    // having objectAssignmentInitializer is only valid in an ObjectAssignmentPattern.
                    // Outside of destructuring, it is a syntax error.

                    // Try to grab the last node prior to the initializer,
                    // then error on the first token following (which should be the `=` token).
                    let mut last_node_before_initializer: Option<NodeId> = None;
                    nodes[prop].for_each_child(&nodes, &mut |child: NodeId| {
                        if child != object_assignment_initializer {
                            last_node_before_initializer = Some(child);
                            return false;
                        }
                        true
                    });

                    self.grammar_error_on_first_token(
                        last_node_before_initializer.expect("lastNodeBeforeInitializer"),
                        &diagnostics::Did_you_mean_to_use_a_Colon_An_can_only_follow_a_property_name_when_the_containing_object_literal_is_part_of_a_destructuring_pattern,
                        &[],
                    );
                }
            }

            if nodes[name].kind == ast::Kind::PrivateIdentifier {
                self.grammar_error_on_node(
                    name,
                    &diagnostics::Private_identifiers_are_not_allowed_outside_class_bodies,
                    &[],
                );
            }

            // Modifiers are never allowed on properties except for 'async' on a method declaration
            if let Some(modifiers) = nodes[prop].modifier_nodes()
                && !modifiers.is_empty()
            {
                let modifiers = modifiers.to_vec();
                if ast::can_have_modifiers(&nodes[prop]) {
                    for m in modifiers {
                        if ast::is_modifier(&nodes[m])
                            && (nodes[m].kind != ast::Kind::AsyncKeyword
                                || nodes[prop].kind != ast::Kind::MethodDeclaration)
                        {
                            let text = scanner::get_text_of_node(m, &nodes);
                            self.grammar_error_on_node(
                                m,
                                &diagnostics::X_0_modifier_cannot_be_used_here,
                                &[text],
                            );
                        }
                    }
                } else if ast::can_have_illegal_modifiers(&nodes[prop]) {
                    for m in modifiers {
                        if ast::is_modifier(&nodes[m]) {
                            let text = scanner::get_text_of_node(m, &nodes);
                            self.grammar_error_on_node(
                                m,
                                &diagnostics::X_0_modifier_cannot_be_used_here,
                                &[text],
                            );
                        }
                    }
                }
            }

            // ECMA-262 11.1.5 Object Initializer
            // If previous is not undefined then throw a SyntaxError exception if any of the following conditions are true
            // a.This production is contained in strict code and IsDataDescriptor(previous) is true and
            // IsDataDescriptor(propId.descriptor) is true.
            //    b.IsDataDescriptor(previous) is true and IsAccessorDescriptor(propId.descriptor) is true.
            //    c.IsAccessorDescriptor(previous) is true and IsDataDescriptor(propId.descriptor) is true.
            //    d.IsAccessorDescriptor(previous) is true and IsAccessorDescriptor(propId.descriptor) is true
            // and either both previous and propId.descriptor have[[Get]] fields or both previous and propId.descriptor have[[Set]] fields
            let current_kind: DeclarationMeaning;
            match nodes[prop].kind {
                ast::Kind::ShorthandPropertyAssignment | ast::Kind::PropertyAssignment => {
                    let postfix_token =
                        if nodes[prop].kind == ast::Kind::ShorthandPropertyAssignment {
                            nodes[prop]
                                .as_shorthand_property_assignment()
                                .named_member_base
                                .postfix_token
                        } else {
                            nodes[prop]
                                .as_property_assignment()
                                .named_member_base
                                .postfix_token
                        };

                    // Grammar checking for computedPropertyName and shorthandPropertyAssignment
                    self.check_grammar_for_invalid_exclamation_token(
                        postfix_token,
                        &diagnostics::A_definite_assignment_assertion_is_not_permitted_in_this_context,
                    );
                    self.check_grammar_for_invalid_question_mark(
                        postfix_token,
                        &diagnostics::An_object_member_cannot_be_declared_optional,
                    );

                    if nodes[name].kind == ast::Kind::NumericLiteral {
                        self.check_grammar_numeric_literal(name);
                    }

                    if nodes[name].kind == ast::Kind::BigIntLiteral {
                        let diagnostic = crate::checker_b::create_diagnostic_for_node(
                            Some(name),
                            &nodes,
                            &diagnostics::A_bigint_literal_cannot_be_used_as_a_property_name,
                            &[],
                        );
                        self.add_error_or_suggestion(true, &diagnostic);
                    }

                    current_kind = DeclarationMeaning::PROPERTY_ASSIGNMENT;
                }
                ast::Kind::MethodDeclaration => {
                    current_kind = DeclarationMeaning::METHOD;
                }
                ast::Kind::GetAccessor => {
                    current_kind = DeclarationMeaning::GET_ACCESSOR;
                }
                ast::Kind::SetAccessor => {
                    current_kind = DeclarationMeaning::SET_ACCESSOR;
                }
                _ => panic!("Unexpected node kind {:?}", nodes[prop].kind),
            }

            if !in_destructuring {
                let (effective_name, ok) =
                    self.get_effective_property_name_for_property_name_node(name);
                if !ok {
                    continue;
                }

                let existing_kind = *seen
                    .get(&effective_name)
                    .unwrap_or(&DeclarationMeaning::NONE);
                if existing_kind == DeclarationMeaning::NONE {
                    seen.insert(effective_name, current_kind);
                } else {
                    if current_kind.intersects(DeclarationMeaning::METHOD)
                        && existing_kind.intersects(DeclarationMeaning::METHOD)
                    {
                        let text = scanner::get_text_of_node(name, &nodes);
                        self.grammar_error_on_node(
                            name,
                            &diagnostics::Duplicate_identifier_0,
                            &[text],
                        );
                    } else if current_kind.intersects(DeclarationMeaning::PROPERTY_ASSIGNMENT)
                        && existing_kind.intersects(DeclarationMeaning::PROPERTY_ASSIGNMENT)
                    {
                        let text = scanner::get_text_of_node(name, &nodes);
                        self.grammar_error_on_node(
                            name,
                            &diagnostics::An_object_literal_cannot_have_multiple_properties_with_the_same_name,
                            &[text],
                        );
                    } else if current_kind.intersects(DeclarationMeaning::GET_OR_SET_ACCESSOR)
                        && existing_kind.intersects(DeclarationMeaning::GET_OR_SET_ACCESSOR)
                    {
                        if existing_kind != DeclarationMeaning::GET_OR_SET_ACCESSOR
                            && current_kind != existing_kind
                        {
                            seen.insert(effective_name, current_kind | existing_kind);
                        } else {
                            return self.grammar_error_on_node(
                                name,
                                &diagnostics::An_object_literal_cannot_have_multiple_get_Slashset_accessors_with_the_same_name,
                                &[],
                            );
                        }
                    } else {
                        return self.grammar_error_on_node(
                            name,
                            &diagnostics::An_object_literal_cannot_have_property_and_accessor_with_the_same_name,
                            &[],
                        );
                    }
                }
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarJsxElement` (grammarchecks.go:1138).
    pub(crate) fn check_grammar_jsx_element(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if let Some(tag_name) = nodes[node].tag_name() {
            self.check_grammar_jsx_name(tag_name);
        }
        let type_argument_list = nodes[node].type_argument_list().cloned();
        self.check_grammar_type_arguments(node, type_argument_list.as_ref());
        let mut seen = tsc_collections::Set::<String>::new();
        let nodes = self.program_nodes(node);
        let attributes = nodes[node].attributes();
        let properties: Vec<NodeId> = attributes
            .and_then(|a| nodes[a].properties().map(|p| p.to_vec()))
            .unwrap_or_default();
        for attr_node in properties {
            if nodes[attr_node].kind == ast::Kind::JsxSpreadAttribute {
                continue;
            }
            let attr = nodes[attr_node].as_jsx_attribute();
            let name = attr.name.expect("jsx attribute name");
            let initializer = attr.initializer;
            let text_of_name = nodes[name].text(&nodes).to_string();
            if !seen.contains(&text_of_name) {
                seen.insert(text_of_name);
            } else {
                return self.grammar_error_on_node(
                    name,
                    &diagnostics::JSX_elements_cannot_have_multiple_attributes_with_the_same_name,
                    &[],
                );
            }
            if let Some(initializer) = initializer
                && nodes[initializer].kind == ast::Kind::JsxExpression
                && nodes[initializer].expression().is_none()
            {
                return self.grammar_error_on_node(
                    initializer,
                    &diagnostics::JSX_attributes_must_only_be_assigned_a_non_empty_expression,
                    &[],
                );
            }
        }
        false
    }

    /// `func (c *Checker) checkGrammarJsxName` (grammarchecks.go:1162).
    pub(crate) fn check_grammar_jsx_name(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if ast::is_property_access_expression(&nodes[node])
            && nodes[node]
                .expression()
                .is_some_and(|e| ast::is_jsx_namespaced_name(&nodes[e]))
        {
            let expr = nodes[node].expression().expect("expression");
            return self.grammar_error_on_node(
                expr,
                &diagnostics::JSX_property_access_expressions_cannot_include_JSX_namespace_names,
                &[],
            );
        }

        if ast::is_jsx_namespaced_name(&nodes[node])
            && self.compiler_options.get_jsx_transform_enabled()
            && !tsc_scanner::utilities::is_intrinsic_jsx_name(
                &nodes[nodes[node]
                    .as_jsx_namespaced_name()
                    .namespace
                    .expect("namespace")]
                .text(&nodes),
            )
        {
            return self.grammar_error_on_node(
                node,
                &diagnostics::React_components_cannot_include_JSX_namespace_names,
                &[],
            );
        }

        false
    }

    /// `func (c *Checker) checkGrammarJsxExpression` (grammarchecks.go:1174).
    pub(crate) fn check_grammar_jsx_expression(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if let Some(expression) = nodes[node].as_jsx_expression().expression
            && ast::is_comma_sequence(&nodes[expression], &nodes)
        {
            return self.grammar_error_on_node(
                expression,
                &diagnostics::JSX_expressions_may_not_use_the_comma_operator_Did_you_mean_to_write_an_array,
                &[],
            );
        }

        false
    }

    /// `func (c *Checker) checkGrammarForInOrForOfStatement` (grammarchecks.go:1182).
    pub(crate) fn check_grammar_for_in_or_for_of_statement(
        &mut self,
        for_in_or_of_statement: NodeId,
    ) -> bool {
        let as_node = for_in_or_of_statement;
        if self.check_grammar_statement_in_ambient_context(as_node) {
            return true;
        }

        let nodes = self.program_nodes(as_node);
        let data = nodes[as_node].as_for_in_or_of_statement();
        let (await_modifier, initializer, kind, flags) = (
            data.await_modifier,
            data.initializer,
            nodes[as_node].kind,
            nodes[as_node].flags,
        );
        if kind == ast::Kind::ForOfStatement && await_modifier.is_some() {
            if !flags.intersects(ast::NodeFlags::AWAIT_CONTEXT) {
                let source_file =
                    ast::get_source_file_of_node(Some(as_node), &nodes).expect("source file");
                if ast::is_in_top_level_context(as_node, &nodes) {
                    if !self.has_parse_diagnostics(source_file) {
                        let sf = nodes[source_file].as_source_file();
                        if !ast::is_effective_external_module(sf, &self.compiler_options) {
                            let diagnostic = crate::checker_b::create_diagnostic_for_node(
                                await_modifier,
                                &nodes,
                                &diagnostics::X_for_await_loops_are_only_allowed_at_the_top_level_of_a_file_when_that_file_is_a_module_but_this_file_has_no_imports_or_exports_Consider_adding_an_empty_export_to_make_this_file_a_module,
                                &[],
                            );
                            self.add_diagnostic(&diagnostic);
                        }
                        match self.module_kind {
                            ModuleKind::Node16
                            | ModuleKind::Node18
                            | ModuleKind::Node20
                            | ModuleKind::NodeNext => {
                                let source_file_meta_data = self
                                    .program
                                    .as_ref()
                                    .expect("program")
                                    .get_source_file_meta_data(sf.path_key());
                                if source_file_meta_data.implied_node_format == ModuleKind::CommonJS
                                {
                                    let diagnostic = crate::checker_b::create_diagnostic_for_node(
                                        await_modifier,
                                        &nodes,
                                        &diagnostics::The_current_file_is_a_CommonJS_module_and_cannot_use_await_at_the_top_level,
                                        &[],
                                    );
                                    self.add_diagnostic(&diagnostic);
                                } else if self.language_version >= ScriptTarget::ES2017 {
                                    // ok
                                } else {
                                    let diagnostic = crate::checker_b::create_diagnostic_for_node(
                                        await_modifier,
                                        &nodes,
                                        &diagnostics::Top_level_for_await_loops_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher,
                                        &[],
                                    );
                                    self.add_diagnostic(&diagnostic);
                                }
                            }
                            ModuleKind::ES2022
                            | ModuleKind::ESNext
                            | ModuleKind::Preserve
                            | ModuleKind::System => {
                                if self.language_version < ScriptTarget::ES2017 {
                                    let diagnostic = crate::checker_b::create_diagnostic_for_node(
                                        await_modifier,
                                        &nodes,
                                        &diagnostics::Top_level_for_await_loops_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher,
                                        &[],
                                    );
                                    self.add_diagnostic(&diagnostic);
                                }
                            }
                            _ => {
                                let diagnostic = crate::checker_b::create_diagnostic_for_node(
                                    await_modifier,
                                    &nodes,
                                    &diagnostics::Top_level_for_await_loops_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher,
                                    &[],
                                );
                                self.add_diagnostic(&diagnostic);
                            }
                        }
                    }
                } else {
                    // use of 'for-await-of' in non-async function
                    if !self.has_parse_diagnostics(source_file) {
                        let diagnostic = crate::checker_b::create_diagnostic_for_node(
                            await_modifier,
                            &nodes,
                            &diagnostics::X_for_await_loops_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules,
                            &[],
                        );
                        let containing_func = ast::get_containing_function(as_node, &nodes);
                        if let Some(containing_func) = containing_func
                            && nodes[containing_func].kind != ast::Kind::Constructor
                        {
                            debug_assert!(
                                !ast::get_function_flags(Some(&nodes[containing_func]))
                                    .intersects(ast::FunctionFlags::ASYNC),
                                "Enclosing function should never be an async function."
                            );
                            let related_info = crate::checker_b::create_diagnostic_for_node(
                                Some(containing_func),
                                &nodes,
                                &diagnostics::Did_you_mean_to_mark_this_function_as_async,
                                &[],
                            );
                            ast::diagnostic::lock_diagnostic(&diagnostic)
                                .add_related_info(Some(related_info));
                        }
                        self.add_diagnostic(&diagnostic);
                        return true;
                    }
                }
            }
        }

        if ast::is_for_of_statement(&nodes[as_node])
            && !flags.intersects(ast::NodeFlags::AWAIT_CONTEXT)
            && initializer.is_some_and(|i| ast::is_identifier(&nodes[i]))
            && initializer.is_some_and(|i| nodes[i].text(&nodes) == "async")
        {
            self.grammar_error_on_node(
                initializer.expect("initializer"),
                &diagnostics::The_left_hand_side_of_a_for_of_statement_may_not_be_async,
                &[],
            );
            return false;
        }

        if initializer.is_some_and(|i| nodes[i].kind == ast::Kind::VariableDeclarationList) {
            let variable_list = initializer.expect("initializer");
            if !self.check_grammar_variable_declaration_list(variable_list) {
                let nodes = self.program_nodes(as_node);
                let declarations = nodes[variable_list]
                    .as_variable_declaration_list()
                    .declarations
                    .clone();

                // declarations.length can be zero if there is an error in variable declaration in for-of or for-in
                // See http://www.ecma-international.org/ecma-262/6.0/#sec-for-in-and-for-of-statements for details
                // For example:
                //      var let = 10;
                //      for (let of [1,2,3]) {} // this is invalid ES6 syntax
                //      for (let in [1,2,3]) {} // this is invalid ES6 syntax
                // We will then want to skip on grammar checking on variableList declaration
                let Some(declarations) = declarations else {
                    return false;
                };
                if declarations.nodes().is_empty() {
                    return false;
                }

                if declarations.nodes().len() > 1 {
                    let diagnostic = if nodes[as_node].kind == ast::Kind::ForInStatement {
                        &diagnostics::Only_a_single_variable_declaration_is_allowed_in_a_for_in_statement
                    } else {
                        &diagnostics::Only_a_single_variable_declaration_is_allowed_in_a_for_of_statement
                    };
                    return self.grammar_error_on_first_token(
                        declarations.nodes()[1],
                        diagnostic,
                        &[],
                    );
                }

                let first_variable_declaration = declarations.nodes()[0];
                let first_variable = nodes[first_variable_declaration].as_variable_declaration();
                if first_variable.initializer.is_some() {
                    let diagnostic = if nodes[as_node].kind == ast::Kind::ForInStatement {
                        &diagnostics::The_variable_declaration_of_a_for_in_statement_cannot_have_an_initializer
                    } else {
                        &diagnostics::The_variable_declaration_of_a_for_of_statement_cannot_have_an_initializer
                    };
                    return self.grammar_error_on_node(
                        first_variable.name.expect("name"),
                        diagnostic,
                        &[],
                    );
                }
                if first_variable.type_.is_some() {
                    let diagnostic = if nodes[as_node].kind == ast::Kind::ForInStatement {
                        &diagnostics::The_left_hand_side_of_a_for_in_statement_cannot_use_a_type_annotation
                    } else {
                        &diagnostics::The_left_hand_side_of_a_for_of_statement_cannot_use_a_type_annotation
                    };
                    return self.grammar_error_on_node(first_variable_declaration, diagnostic, &[]);
                }
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarAccessor` (grammarchecks.go:1289).
    pub(crate) fn check_grammar_accessor(&mut self, accessor: NodeId) -> bool {
        let nodes = self.program_nodes(accessor);
        let body = nodes[accessor].body();
        let parent_kind = nodes[accessor].parent.map(|p| nodes[p].kind);
        if !nodes[accessor].flags.intersects(ast::NodeFlags::AMBIENT)
            && parent_kind != Some(ast::Kind::TypeLiteral)
            && parent_kind != Some(ast::Kind::InterfaceDeclaration)
        {
            if body.is_none()
                && !ast::has_syntactic_modifier(&nodes[accessor], ast::ModifierFlags::ABSTRACT)
            {
                return self.grammar_error_at_pos(
                    accessor,
                    nodes[accessor].end() - 1,
                    ";".len() as i32,
                    &diagnostics::X_0_expected,
                    &["{".to_string()],
                );
            }
        }
        if body.is_some() {
            if ast::has_syntactic_modifier(&nodes[accessor], ast::ModifierFlags::ABSTRACT) {
                return self.grammar_error_on_node(
                    accessor,
                    &diagnostics::An_abstract_accessor_cannot_have_an_implementation,
                    &[],
                );
            }
            if parent_kind == Some(ast::Kind::TypeLiteral)
                || parent_kind == Some(ast::Kind::InterfaceDeclaration)
            {
                return self.grammar_error_on_node(
                    body.expect("body"),
                    &diagnostics::An_implementation_cannot_be_declared_in_ambient_contexts,
                    &[],
                );
            }
        }

        let func_data = nodes[accessor].function_like_data();
        let type_parameters = func_data.and_then(|d| d.type_parameters.clone());

        if type_parameters.is_some() {
            let name = nodes[accessor].name().expect("name");
            return self.grammar_error_on_node(
                name,
                &diagnostics::An_accessor_cannot_have_type_parameters,
                &[],
            );
        }
        if !self.does_accessor_have_correct_parameter_count(accessor) {
            let nodes = self.program_nodes(accessor);
            let name = nodes[accessor].name().expect("name");
            let message = if nodes[accessor].kind == ast::Kind::GetAccessor {
                &diagnostics::A_get_accessor_cannot_have_parameters
            } else {
                &diagnostics::A_set_accessor_must_have_exactly_one_parameter
            };
            return self.grammar_error_on_node(name, message, &[]);
        }
        let nodes = self.program_nodes(accessor);
        if nodes[accessor].kind == ast::Kind::SetAccessor {
            if nodes[accessor]
                .function_like_data()
                .is_some_and(|d| d.type_.is_some())
            {
                let name = nodes[accessor].name().expect("name");
                return self.grammar_error_on_node(
                    name,
                    &diagnostics::A_set_accessor_cannot_have_a_return_type_annotation,
                    &[],
                );
            }

            // `GetSetAccessorValueParameter` (utilities.go:1914) — inlined:
            // `parameters.len() > 0`, `this` param skipped when two params.
            let parameters: Vec<NodeId> = nodes[accessor]
                .parameters()
                .map(|p| p.to_vec())
                .unwrap_or_default();
            let has_this =
                parameters.len() == 2 && ast::is_this_parameter(&nodes[parameters[0]], &nodes);
            let parameter_node = if !parameters.is_empty() {
                Some(parameters[if has_this { 1 } else { 0 }])
            } else {
                None
            };
            if parameter_node.is_none() {
                panic!("Return value does not match parameter count assertion.");
            }
            let parameter_node = parameter_node.unwrap();
            let parameter = nodes[parameter_node].as_parameter_declaration();
            if let Some(token) = parameter.dot_dot_dot_token {
                return self.grammar_error_on_node(
                    token,
                    &diagnostics::A_set_accessor_cannot_have_rest_parameter,
                    &[],
                );
            }
            if let Some(token) = parameter.question_token {
                return self.grammar_error_on_node(
                    token,
                    &diagnostics::A_set_accessor_cannot_have_an_optional_parameter,
                    &[],
                );
            }
            if parameter.initializer.is_some() {
                let name = nodes[accessor].name().expect("name");
                return self.grammar_error_on_node(
                    name,
                    &diagnostics::A_set_accessor_parameter_cannot_have_an_initializer,
                    &[],
                );
            }
        }

        false
    }

    /// `func (c *Checker) doesAccessorHaveCorrectParameterCount` (grammarchecks.go:1345).
    ///
    /// Does the accessor have the right number of parameters?
    ///
    ///	A `get` accessor has no parameters or a single `this` parameter.
    ///	A `set` accessor has one parameter or a `this` parameter and one more parameter.
    pub(crate) fn does_accessor_have_correct_parameter_count(&mut self, accessor: NodeId) -> bool {
        // `getAccessorThisParameter` returns `nil` if the accessor's arity is incorrect,
        // even if there is a `this` parameter declared.
        let nodes = self.program_nodes(accessor);
        let param_count = nodes[accessor].parameters().map(|p| p.len()).unwrap_or(0);
        let expected = if nodes[accessor].kind == ast::Kind::GetAccessor {
            0
        } else {
            1
        };
        self.get_accessor_this_parameter(accessor).is_some() || param_count == expected
    }

    /// `func (c *Checker) checkGrammarTypeOperatorNode` (grammarchecks.go:1351).
    pub(crate) fn check_grammar_type_operator_node(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let data = nodes[node].as_type_operator_node();
        if data.operator == ast::Kind::UniqueKeyword {
            let inner_type = data.type_.expect("type");
            if nodes[inner_type].kind != ast::Kind::SymbolKeyword {
                return self.grammar_error_on_node(
                    inner_type,
                    &diagnostics::X_0_expected,
                    &[scanner::token_to_string(ast::Kind::SymbolKeyword).to_string()],
                );
            }
            let parent =
                ast::walk_up_parenthesized_types(nodes[node].parent.expect("parent"), &nodes)
                    .expect("parenthesized parent");
            match nodes[parent].kind {
                ast::Kind::VariableDeclaration => {
                    let decl = nodes[parent].as_variable_declaration();
                    if decl
                        .name
                        .is_some_and(|n| nodes[n].kind != ast::Kind::Identifier)
                        || decl.name.is_none()
                    {
                        return self.grammar_error_on_node(
                            node,
                            &diagnostics::X_unique_symbol_types_may_not_be_used_on_a_variable_declaration_with_a_binding_name,
                            &[],
                        );
                    }
                    // `isVariableDeclarationInVariableStatement` (utilities.go:1014)
                    // — inlined: `IsVariableDeclarationList(parent) &&
                    // IsVariableStatement(parent.Parent)`.
                    let decl_parent = nodes[parent].parent;
                    if !(decl_parent.is_some_and(|p| ast::is_variable_declaration_list(&nodes[p]))
                        && decl_parent
                            .and_then(|p| nodes[p].parent)
                            .is_some_and(|p| ast::is_variable_statement(&nodes[p])))
                    {
                        return self.grammar_error_on_node(
                            node,
                            &diagnostics::X_unique_symbol_types_are_only_allowed_on_variables_in_a_variable_statement,
                            &[],
                        );
                    }
                    if decl_parent
                        .is_some_and(|p| !nodes[p].flags.intersects(ast::NodeFlags::CONST))
                    {
                        let name = nodes[parent].name().expect("name");
                        return self.grammar_error_on_node(
                            name,
                            &diagnostics::A_variable_whose_type_is_a_unique_symbol_type_must_be_const,
                            &[],
                        );
                    }
                }
                ast::Kind::PropertyDeclaration => {
                    if !(ast::is_static(&nodes[parent])
                        && crate::utilities::has_readonly_modifier(&nodes[parent]))
                    {
                        let name = nodes[parent].name().expect("name");
                        return self.grammar_error_on_node(
                            name,
                            &diagnostics::A_property_of_a_class_whose_type_is_a_unique_symbol_type_must_be_both_static_and_readonly,
                            &[],
                        );
                    }
                }
                ast::Kind::PropertySignature => {
                    if !ast::has_syntactic_modifier(&nodes[parent], ast::ModifierFlags::READONLY) {
                        let name = nodes[parent].name().expect("name");
                        return self.grammar_error_on_node(
                            name,
                            &diagnostics::A_property_of_an_interface_or_type_literal_whose_type_is_a_unique_symbol_type_must_be_readonly,
                            &[],
                        );
                    }
                }
                _ => {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::X_unique_symbol_types_are_not_allowed_here,
                        &[],
                    );
                }
            }
        } else if data.operator == ast::Kind::ReadonlyKeyword {
            let inner_type = data.type_.expect("type");
            if nodes[inner_type].kind != ast::Kind::ArrayType
                && nodes[inner_type].kind != ast::Kind::TupleType
            {
                return self.grammar_error_on_first_token(
                    node,
                    &diagnostics::X_readonly_type_modifier_is_only_permitted_on_array_and_tuple_literal_types,
                    &[scanner::token_to_string(ast::Kind::SymbolKeyword).to_string()],
                );
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarForInvalidDynamicName` (grammarchecks.go:1391).
    pub(crate) fn check_grammar_for_invalid_dynamic_name(
        &mut self,
        node: NodeId,
        message: &'static diagnostics::Message,
    ) -> bool {
        if !self.is_non_bindable_dynamic_name(node) {
            return false;
        }
        let nodes = self.program_nodes(node);
        let expression = if ast::is_element_access_expression(&nodes[node]) {
            let arg = nodes[node]
                .as_element_access_expression()
                .argument_expression
                .expect("argumentExpression");
            ast::skip_parentheses(arg, &nodes)
        } else {
            nodes[node].expression().expect("expression")
        };

        if !ast::is_entity_name_expression(&nodes[expression], &nodes) {
            return self.grammar_error_on_node(node, message, &[]);
        }

        false
    }

    /// `func (c *Checker) isNonBindableDynamicName` (grammarchecks.go:1410).
    ///
    /// Indicates whether a declaration name is a dynamic name that cannot be late-bound.
    pub(crate) fn is_non_bindable_dynamic_name(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        ast::is_dynamic_name(node, &nodes) && !self.is_late_bindable_name(node)
    }

    /// `func (c *Checker) checkGrammarMethod` (grammarchecks.go:1414).
    pub(crate) fn check_grammar_method(&mut self, node: NodeId) -> bool {
        if self.check_grammar_function_like_declaration(node) {
            return true;
        }

        let nodes = self.program_nodes(node);
        if nodes[node].kind == ast::Kind::MethodDeclaration {
            let parent_kind = nodes[node].parent.map(|p| nodes[p].kind);
            if parent_kind == Some(ast::Kind::ObjectLiteralExpression) {
                // We only disallow modifier on a method declaration if it is a property of object-literal-expression
                if let Some(modifiers) = nodes[node].modifiers()
                    && !(modifiers.nodes.len() == 1
                        && nodes[modifiers.nodes[0]].kind == ast::Kind::AsyncKeyword)
                {
                    return self.grammar_error_on_first_token(
                        node,
                        &diagnostics::Modifiers_cannot_appear_here,
                        &[],
                    );
                }

                if self.check_grammar_for_invalid_question_mark(
                    nodes[node].postfix_token(),
                    &diagnostics::An_object_member_cannot_be_declared_optional,
                ) {
                    return true;
                }
                if self.check_grammar_for_invalid_exclamation_token(
                    nodes[node].postfix_token(),
                    &diagnostics::A_definite_assignment_assertion_is_not_permitted_in_this_context,
                ) {
                    return true;
                }
                if nodes[node].body().is_none() {
                    return self.grammar_error_at_pos(
                        node,
                        nodes[node].end() - 1,
                        ";".len() as i32,
                        &diagnostics::X_0_expected,
                        &["{".to_string()],
                    );
                }
            }
            if self.check_grammar_for_generator(node) {
                return true;
            }
        }

        let nodes = self.program_nodes(node);
        let parent = nodes[node].parent;
        if parent.is_some_and(|p| ast::is_class_like(Some(p), &nodes)) {
            // Technically, computed properties in ambient contexts is disallowed
            // for property declarations and accessors too, not just methods.
            // However, property declarations disallow computed names in general,
            // and accessors are not allowed in ambient contexts in general,
            // so this error only really matters for methods.
            let name = nodes[node].name().expect("name");
            if nodes[node].flags.intersects(ast::NodeFlags::AMBIENT) {
                return self.check_grammar_for_invalid_dynamic_name(
                    name,
                    &diagnostics::A_computed_property_name_in_an_ambient_context_must_refer_to_an_expression_whose_type_is_a_literal_type_or_a_unique_symbol_type,
                );
            } else if nodes[node].kind == ast::Kind::MethodDeclaration
                && nodes[node].body().is_none()
            {
                return self.check_grammar_for_invalid_dynamic_name(
                    name,
                    &diagnostics::A_computed_property_name_in_a_method_overload_must_refer_to_an_expression_whose_type_is_a_literal_type_or_a_unique_symbol_type,
                );
            }
        } else if parent.is_some_and(|p| nodes[p].kind == ast::Kind::InterfaceDeclaration) {
            let name = nodes[node].name().expect("name");
            return self.check_grammar_for_invalid_dynamic_name(
                name,
                &diagnostics::A_computed_property_name_in_an_interface_must_refer_to_an_expression_whose_type_is_a_literal_type_or_a_unique_symbol_type,
            );
        } else if parent.is_some_and(|p| nodes[p].kind == ast::Kind::TypeLiteral) {
            let name = nodes[node].name().expect("name");
            return self.check_grammar_for_invalid_dynamic_name(
                name,
                &diagnostics::A_computed_property_name_in_a_type_literal_must_refer_to_an_expression_whose_type_is_a_literal_type_or_a_unique_symbol_type,
            );
        }

        false
    }

    /// `func (c *Checker) checkGrammarBreakOrContinueStatement` (grammarchecks.go:1462).
    pub(crate) fn check_grammar_break_or_continue_statement(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let target_label = nodes[node].label();
        let mut current = Some(node);
        while let Some(cur) = current {
            if ast::is_function_like_or_class_static_block_declaration(&nodes[cur], &nodes) {
                return self.grammar_error_on_node(
                    node,
                    &diagnostics::Jump_target_cannot_cross_function_boundary,
                    &[],
                );
            }

            match nodes[cur].kind {
                ast::Kind::LabeledStatement => {
                    if target_label.is_some()
                        && nodes[cur].label().is_some_and(|l| {
                            nodes[l].text(&nodes) == nodes[target_label.unwrap()].text(&nodes)
                        })
                    {
                        // found matching label - verify that label usage is correct
                        // continue can only target labels that are on iteration statements
                        let is_misplaced_continue_label = nodes[node].kind
                            == ast::Kind::ContinueStatement
                            && nodes[cur].statement().is_some_and(|s| {
                                !ast::is_iteration_statement(
                                    &nodes[s], &nodes, true, /*lookInLabeledStatements*/
                                )
                            });

                        if is_misplaced_continue_label {
                            return self.grammar_error_on_node(
                                node,
                                &diagnostics::A_continue_statement_can_only_jump_to_a_label_of_an_enclosing_iteration_statement,
                                &[],
                            );
                        }

                        return false;
                    }
                }
                ast::Kind::SwitchStatement => {
                    if nodes[node].kind == ast::Kind::BreakStatement && target_label.is_none() {
                        // unlabeled break within switch statement - ok
                        return false;
                    }
                }
                _ => {
                    if ast::is_iteration_statement(
                        &nodes[cur],
                        &nodes,
                        false, /*lookInLabeledStatements*/
                    ) && target_label.is_none()
                    {
                        // unlabeled break or continue within iteration statement - ok
                        return false;
                    }
                }
            }

            current = nodes[cur].parent;
        }

        if target_label.is_some() {
            let message = if nodes[node].kind == ast::Kind::BreakStatement {
                &diagnostics::A_break_statement_can_only_jump_to_a_label_of_an_enclosing_statement
            } else {
                &diagnostics::A_continue_statement_can_only_jump_to_a_label_of_an_enclosing_iteration_statement
            };

            self.grammar_error_on_node(node, message, &[])
        } else {
            let message = if nodes[node].kind == ast::Kind::BreakStatement {
                &diagnostics::A_break_statement_can_only_be_used_within_an_enclosing_iteration_or_switch_statement
            } else {
                &diagnostics::A_continue_statement_can_only_be_used_within_an_enclosing_iteration_statement
            };
            self.grammar_error_on_node(node, message, &[])
        }
    }

    /// `func (c *Checker) checkGrammarBindingElement` (grammarchecks.go:1518).
    pub(crate) fn check_grammar_binding_element(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let data = nodes[node].as_binding_element();
        if data.dot_dot_dot_token.is_some() {
            let elements = nodes[node]
                .parent
                .and_then(|p| nodes[p].element_list().cloned());
            if let Some(elements) = &elements
                && Some(node) != elements.nodes().last().copied()
            {
                return self.grammar_error_on_node(
                    node,
                    &diagnostics::A_rest_element_must_be_last_in_a_destructuring_pattern,
                    &[],
                );
            }
            self.check_grammar_for_disallowed_trailing_comma(
                elements.as_ref(),
                &diagnostics::A_rest_parameter_or_binding_pattern_may_not_have_a_trailing_comma,
                &nodes,
            );

            if data.property_name.is_some() {
                let name = data.name.expect("name");
                return self.grammar_error_on_node(
                    name,
                    &diagnostics::A_rest_element_cannot_have_a_property_name,
                    &[],
                );
            }
        }

        if data.dot_dot_dot_token.is_some() && data.initializer.is_some() {
            // Error on equals token which immediately precedes the initializer
            let initializer = data.initializer.expect("initializer");
            return self.grammar_error_at_pos(
                node,
                nodes[initializer].pos() - 1,
                1,
                &diagnostics::A_rest_element_cannot_have_an_initializer,
                &[],
            );
        }

        false
    }

    /// `func (c *Checker) checkGrammarVariableDeclaration` (grammarchecks.go:1539).
    pub(crate) fn check_grammar_variable_declaration(&mut self, node: NodeId) -> bool {
        let node_flags = self.get_combined_node_flags_cached(node);
        let block_scope_kind = node_flags & ast::NodeFlags::BLOCK_SCOPED;
        let nodes = self.program_nodes(node);
        let data = nodes[node].as_variable_declaration();
        let (name, initializer, type_, exclamation_token) = (
            data.name,
            data.initializer,
            data.type_,
            data.exclamation_token,
        );
        if name.is_some_and(|n| ast::is_binding_pattern(&nodes[n])) {
            match block_scope_kind {
                ast::NodeFlags::AWAIT_USING => {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::X_0_declarations_may_not_have_binding_patterns,
                        &["await using".to_string()],
                    );
                }
                ast::NodeFlags::USING => {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::X_0_declarations_may_not_have_binding_patterns,
                        &["using".to_string()],
                    );
                }
                _ => {}
            }
        }

        let grandparent_kind = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .map(|p| nodes[p].kind);
        if grandparent_kind != Some(ast::Kind::ForInStatement)
            && grandparent_kind != Some(ast::Kind::ForOfStatement)
        {
            if node_flags.intersects(ast::NodeFlags::AMBIENT) {
                self.check_ambient_initializer(node);
            } else if initializer.is_none() {
                let parent_is_binding_pattern = nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_binding_pattern(&nodes[p]));
                if name.is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
                    && !parent_is_binding_pattern
                {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::A_destructuring_declaration_must_have_an_initializer,
                        &[],
                    );
                }
                match block_scope_kind {
                    ast::NodeFlags::AWAIT_USING => {
                        return self.grammar_error_on_node(
                            node,
                            &diagnostics::X_0_declarations_must_be_initialized,
                            &["await using".to_string()],
                        );
                    }
                    ast::NodeFlags::USING => {
                        return self.grammar_error_on_node(
                            node,
                            &diagnostics::X_0_declarations_must_be_initialized,
                            &["using".to_string()],
                        );
                    }
                    ast::NodeFlags::CONST => {
                        return self.grammar_error_on_node(
                            node,
                            &diagnostics::X_0_declarations_must_be_initialized,
                            &["const".to_string()],
                        );
                    }
                    _ => {}
                }
            }
        }

        if exclamation_token.is_some()
            && (grandparent_kind != Some(ast::Kind::VariableStatement)
                || type_.is_none()
                || initializer.is_some()
                || node_flags.intersects(ast::NodeFlags::AMBIENT))
        {
            let message = if initializer.is_some() {
                &diagnostics::Declarations_with_initializers_cannot_also_have_definite_assignment_assertions
            } else if type_.is_none() {
                &diagnostics::Declarations_with_definite_assignment_assertions_must_also_have_type_annotations
            } else {
                &diagnostics::A_definite_assignment_assertion_is_not_permitted_in_this_context
            };
            return self.grammar_error_on_node(
                exclamation_token.expect("exclamationToken"),
                message,
                &[],
            );
        }

        let grandparent = nodes[node].parent.and_then(|p| nodes[p].parent);
        if let Some(grandparent) = grandparent {
            let source_file =
                ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
            if self
                .program
                .as_ref()
                .expect("program")
                .get_emit_module_format_of_file(nodes[source_file].as_source_file())
                < ModuleKind::System
                && !nodes[grandparent].flags.intersects(ast::NodeFlags::AMBIENT)
                && ast::has_syntactic_modifier(&nodes[grandparent], ast::ModifierFlags::EXPORT)
            {
                if let Some(name) = name {
                    self.check_grammar_for_es_module_marker_in_binding_name(name);
                }
            }
        }

        // 1. LexicalDeclaration : LetOrConst BindingList ;
        // It is a Syntax Error if the BoundNames of BindingList contains "let".
        // 2. ForDeclaration: ForDeclaration : LetOrConst ForBinding
        // It is a Syntax Error if the BoundNames of ForDeclaration contains "let".

        // It is a SyntaxError if a VariableDeclaration or VariableDeclarationNoIn occurs within strict code
        // and its Identifier is eval or arguments
        block_scope_kind != ast::NodeFlags::NONE
            && name.is_some_and(|n| self.check_grammar_name_in_let_or_const_declarations(n))
    }

    /// `func (c *Checker) checkGrammarForEsModuleMarkerInBindingName` (grammarchecks.go:1596).
    pub(crate) fn check_grammar_for_es_module_marker_in_binding_name(
        &mut self,
        name: NodeId,
    ) -> bool {
        let nodes = self.program_nodes(name);
        if ast::is_identifier(&nodes[name]) {
            if nodes[name].text(&nodes) == "__esModule" {
                return self.grammar_error_on_node_skipped_on_no_emit(
                    name,
                    &diagnostics::Identifier_expected_esModule_is_reserved_as_an_exported_marker_when_transforming_ECMAScript_modules,
                    &[],
                );
            }
        } else {
            let elements: Vec<NodeId> = nodes[name]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default();
            for element in elements {
                if let Some(element_name) = nodes[element].name() {
                    if self.check_grammar_for_es_module_marker_in_binding_name(element_name) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// `func (c *Checker) checkGrammarNameInLetOrConstDeclarations` (grammarchecks.go:1611).
    pub(crate) fn check_grammar_name_in_let_or_const_declarations(&mut self, name: NodeId) -> bool {
        let nodes = self.program_nodes(name);
        if nodes[name].kind == ast::Kind::Identifier {
            if nodes[name].text(&nodes) == "let" {
                return self.grammar_error_on_node(
                    name,
                    &diagnostics::X_let_is_not_allowed_to_be_used_as_a_name_in_let_or_const_declarations,
                    &[],
                );
            }
        } else {
            let elements: Vec<NodeId> = nodes[name]
                .elements()
                .map(|e| e.to_vec())
                .unwrap_or_default();
            for element in elements {
                if let Some(element_name) = nodes[element].as_binding_element().name {
                    self.check_grammar_name_in_let_or_const_declarations(element_name);
                }
            }
        }
        false
    }

    /// `func (c *Checker) checkGrammarVariableDeclarationList` (grammarchecks.go:1628).
    pub(crate) fn check_grammar_variable_declaration_list(
        &mut self,
        declaration_list: NodeId,
    ) -> bool {
        let nodes = self.program_nodes(declaration_list);
        let declarations = nodes[declaration_list]
            .as_variable_declaration_list()
            .declarations
            .clone();
        if self.check_grammar_for_disallowed_trailing_comma(
            declarations.as_ref(),
            &diagnostics::Trailing_comma_not_allowed,
            &nodes,
        ) {
            return true;
        }

        let Some(declarations) = &declarations else {
            return false;
        };
        if declarations.nodes().is_empty() {
            return self.grammar_error_at_pos(
                declaration_list,
                declarations.pos(),
                declarations.end() - declarations.pos(),
                &diagnostics::Variable_declaration_list_cannot_be_empty,
                &[],
            );
        }

        let block_scope_flags = nodes[declaration_list].flags & ast::NodeFlags::BLOCK_SCOPED;
        if block_scope_flags == ast::NodeFlags::USING
            || block_scope_flags == ast::NodeFlags::AWAIT_USING
        {
            let parent = nodes[declaration_list].parent;
            if parent.is_some_and(|p| ast::is_for_in_statement(&nodes[p])) {
                let message = if block_scope_flags == ast::NodeFlags::USING {
                    &diagnostics::The_left_hand_side_of_a_for_in_statement_cannot_be_a_using_declaration
                } else {
                    &diagnostics::The_left_hand_side_of_a_for_in_statement_cannot_be_an_await_using_declaration
                };
                return self.grammar_error_on_node(declaration_list, message, &[]);
            }
            if nodes[declaration_list]
                .flags
                .intersects(ast::NodeFlags::AMBIENT)
            {
                let message = if block_scope_flags == ast::NodeFlags::USING {
                    &diagnostics::X_using_declarations_are_not_allowed_in_ambient_contexts
                } else {
                    &diagnostics::X_await_using_declarations_are_not_allowed_in_ambient_contexts
                };
                return self.grammar_error_on_node(declaration_list, message, &[]);
            }
            let grandparent = parent.and_then(|p| nodes[p].parent);
            if parent.is_some_and(|p| ast::is_variable_statement(&nodes[p]))
                && grandparent.is_some_and(|p| {
                    ast::is_case_clause(&nodes[p]) || ast::is_default_clause(&nodes[p])
                })
            {
                let message = if block_scope_flags == ast::NodeFlags::USING {
                    &diagnostics::X_using_declarations_are_not_allowed_in_case_or_default_clauses_unless_contained_within_a_block
                } else {
                    &diagnostics::X_await_using_declarations_are_not_allowed_in_case_or_default_clauses_unless_contained_within_a_block
                };
                return self.grammar_error_on_node(declaration_list, message, &[]);
            }
        }

        if block_scope_flags == ast::NodeFlags::AWAIT_USING {
            return self.check_grammar_await_or_await_using(declaration_list);
        }

        false
    }

    /// `func (c *Checker) checkGrammarAwaitOrAwaitUsing` (grammarchecks.go:1658).
    pub(crate) fn check_grammar_await_or_await_using(&mut self, node: NodeId) -> bool {
        // Grammar checking
        let mut has_error = false;
        let nodes = self.program_nodes(node);
        let container =
            crate::utilities::get_containing_function_or_class_static_block(node, &nodes);
        if let Some(container) = container
            && ast::is_class_static_block_declaration(&nodes[container])
        {
            // NOTE: We report this regardless as to whether there are parse diagnostics.
            let message = if ast::is_await_expression(&nodes[node]) {
                &diagnostics::X_await_expression_cannot_be_used_inside_a_class_static_block
            } else {
                &diagnostics::X_await_using_statements_cannot_be_used_inside_a_class_static_block
            };
            self.error(Some(node), message, &[]);
            has_error = true;
        } else if !nodes[node].flags.intersects(ast::NodeFlags::AWAIT_CONTEXT) {
            if ast::is_in_top_level_context(node, &nodes) {
                let source_file =
                    ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
                if !self.has_parse_diagnostics(source_file) {
                    let mut span = TextRange::default();
                    let mut span_calculated = false;
                    {
                        let sf = nodes[source_file].as_source_file();
                        if !ast::is_effective_external_module(sf, &self.compiler_options) {
                            span = scanner::get_range_of_token_at_position(
                                sf,
                                nodes[node].pos() as usize,
                            );
                            span_calculated = true;
                            let message = if ast::is_await_expression(&nodes[node]) {
                                &diagnostics::X_await_expressions_are_only_allowed_at_the_top_level_of_a_file_when_that_file_is_a_module_but_this_file_has_no_imports_or_exports_Consider_adding_an_empty_export_to_make_this_file_a_module
                            } else {
                                &diagnostics::X_await_using_statements_are_only_allowed_at_the_top_level_of_a_file_when_that_file_is_a_module_but_this_file_has_no_imports_or_exports_Consider_adding_an_empty_export_to_make_this_file_a_module
                            };
                            let diagnostic = ast::diagnostic::new_diagnostic(
                                Some(ast::diagnostic::DiagnosticFile::from_node(
                                    source_file,
                                    &nodes,
                                )),
                                span,
                                message,
                                &[] as &[String],
                            );
                            self.add_diagnostic(&diagnostic);
                            has_error = true;
                        }
                    }
                    match self.module_kind {
                        ModuleKind::Node16
                        | ModuleKind::Node18
                        | ModuleKind::Node20
                        | ModuleKind::NodeNext => {
                            let path_key = {
                                let sf = nodes[source_file].as_source_file();
                                sf.path_key().clone()
                            };
                            let source_file_meta_data = self
                                .program
                                .as_ref()
                                .expect("program")
                                .get_source_file_meta_data(&path_key);
                            if source_file_meta_data.implied_node_format == ModuleKind::CommonJS {
                                if !span_calculated {
                                    let sf = nodes[source_file].as_source_file();
                                    span = scanner::get_range_of_token_at_position(
                                        sf,
                                        nodes[node].pos() as usize,
                                    );
                                }
                                let diagnostic = ast::diagnostic::new_diagnostic(
                                    Some(ast::diagnostic::DiagnosticFile::from_node(
                                        source_file, &nodes,
                                    )),
                                    span,
                                    &diagnostics::The_current_file_is_a_CommonJS_module_and_cannot_use_await_at_the_top_level,
                                    &[] as &[String],
                                );
                                self.add_diagnostic(&diagnostic);
                                has_error = true;
                            } else if self.language_version >= ScriptTarget::ES2017 {
                                // ok
                            } else {
                                if !span_calculated {
                                    let sf = nodes[source_file].as_source_file();
                                    span = scanner::get_range_of_token_at_position(
                                        sf,
                                        nodes[node].pos() as usize,
                                    );
                                }
                                let message = if ast::is_await_expression(&nodes[node]) {
                                    &diagnostics::Top_level_await_expressions_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher
                                } else {
                                    &diagnostics::Top_level_await_using_statements_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher
                                };
                                let diagnostic = ast::diagnostic::new_diagnostic(
                                    Some(ast::diagnostic::DiagnosticFile::from_node(
                                        source_file,
                                        &nodes,
                                    )),
                                    span,
                                    message,
                                    &[] as &[String],
                                );
                                self.add_diagnostic(&diagnostic);
                                has_error = true;
                            }
                        }
                        ModuleKind::ES2022
                        | ModuleKind::ESNext
                        | ModuleKind::Preserve
                        | ModuleKind::System => {
                            if self.language_version < ScriptTarget::ES2017 {
                                if !span_calculated {
                                    let sf = nodes[source_file].as_source_file();
                                    span = scanner::get_range_of_token_at_position(
                                        sf,
                                        nodes[node].pos() as usize,
                                    );
                                }
                                let message = if ast::is_await_expression(&nodes[node]) {
                                    &diagnostics::Top_level_await_expressions_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher
                                } else {
                                    &diagnostics::Top_level_await_using_statements_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher
                                };
                                let diagnostic = ast::diagnostic::new_diagnostic(
                                    Some(ast::diagnostic::DiagnosticFile::from_node(
                                        source_file,
                                        &nodes,
                                    )),
                                    span,
                                    message,
                                    &[] as &[String],
                                );
                                self.add_diagnostic(&diagnostic);
                                has_error = true;
                            }
                        }
                        _ => {
                            if !span_calculated {
                                let sf = nodes[source_file].as_source_file();
                                span = scanner::get_range_of_token_at_position(
                                    sf,
                                    nodes[node].pos() as usize,
                                );
                            }
                            let message = if ast::is_await_expression(&nodes[node]) {
                                &diagnostics::Top_level_await_expressions_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher
                            } else {
                                &diagnostics::Top_level_await_using_statements_are_only_allowed_when_the_module_option_is_set_to_es2022_esnext_system_node16_node18_node20_nodenext_or_preserve_and_the_target_option_is_set_to_es2017_or_higher
                            };
                            let diagnostic = ast::diagnostic::new_diagnostic(
                                Some(ast::diagnostic::DiagnosticFile::from_node(
                                    source_file,
                                    &nodes,
                                )),
                                span,
                                message,
                                &[] as &[String],
                            );
                            self.add_diagnostic(&diagnostic);
                            has_error = true;
                        }
                    }
                }
            } else {
                // use of 'await' in non-async function
                let source_file =
                    ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
                if !self.has_parse_diagnostics(source_file) {
                    let span = {
                        let sf = nodes[source_file].as_source_file();
                        scanner::get_range_of_token_at_position(sf, nodes[node].pos() as usize)
                    };
                    let message = if ast::is_await_expression(&nodes[node]) {
                        &diagnostics::X_await_expressions_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules
                    } else {
                        &diagnostics::X_await_using_statements_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules
                    };
                    let diagnostic = ast::diagnostic::new_diagnostic(
                        Some(ast::diagnostic::DiagnosticFile::from_node(
                            source_file,
                            &nodes,
                        )),
                        span,
                        message,
                        &[] as &[String],
                    );
                    if let Some(container) = container
                        && nodes[container].kind != ast::Kind::Constructor
                        && !crate::utilities::has_async_modifier(&nodes[container])
                    {
                        let nodes = self.program_nodes(node);
                        let related_info = crate::utilities::new_diagnostic_for_node(
                            Some(container),
                            &nodes,
                            &diagnostics::Did_you_mean_to_mark_this_function_as_async,
                            &[],
                        );
                        ast::diagnostic::lock_diagnostic(&diagnostic)
                            .add_related_info(Some(related_info));
                    }
                    self.add_diagnostic(&diagnostic);
                    has_error = true;
                }
            }
        }

        if ast::is_await_expression(&nodes[node])
            && self.is_in_parameter_initializer_before_containing_function(node)
        {
            // NOTE: We report this regardless as to whether there are parse diagnostics.
            self.error(
                Some(node),
                &diagnostics::X_await_expressions_cannot_be_used_in_a_parameter_initializer,
                &[],
            );
            has_error = true;
        }

        has_error
    }

    /// `func (c *Checker) checkGrammarYieldExpression` (grammarchecks.go:1759).
    pub(crate) fn check_grammar_yield_expression(&mut self, node: NodeId) -> bool {
        let mut has_error = false;
        let nodes = self.program_nodes(node);
        if !nodes[node].flags.intersects(ast::NodeFlags::YIELD_CONTEXT) {
            self.grammar_error_on_first_token(
                node,
                &diagnostics::A_yield_expression_is_only_allowed_in_a_generator_body,
                &[],
            );
            has_error = true;
        }
        if self.is_in_parameter_initializer_before_containing_function(node) {
            self.error(
                Some(node),
                &diagnostics::X_yield_expressions_cannot_be_used_in_a_parameter_initializer,
                &[],
            );
            has_error = true;
        }
        has_error
    }

    /// `func (c *Checker) checkGrammarForDisallowedBlockScopedVariableStatement` (grammarchecks.go:1772).
    pub(crate) fn check_grammar_for_disallowed_block_scoped_variable_statement(
        &mut self,
        node: NodeId,
    ) -> bool {
        let nodes = self.program_nodes(node);
        let parent = nodes[node].parent;
        let declaration_list = nodes[node].as_variable_statement().declaration_list;
        if !self.container_allows_block_scoped_variable(parent) {
            let block_scope_kind = declaration_list
                .map(|d| self.get_combined_node_flags_cached(d))
                .unwrap_or_default()
                & ast::NodeFlags::BLOCK_SCOPED;
            if block_scope_kind != ast::NodeFlags::NONE {
                let keyword = match block_scope_kind {
                    k if k == ast::NodeFlags::LET => "let",
                    k if k == ast::NodeFlags::CONST => "const",
                    k if k == ast::NodeFlags::USING => "using",
                    k if k == ast::NodeFlags::AWAIT_USING => "await using",
                    _ => panic!("Unknown BlockScope flag"),
                };
                self.error(
                    Some(node),
                    &diagnostics::X_0_declarations_can_only_be_declared_inside_a_block,
                    &[keyword.to_string()],
                );
            }
        }

        false
    }

    /// `func (c *Checker) containerAllowsBlockScopedVariable` (grammarchecks.go:1796).
    pub(crate) fn container_allows_block_scoped_variable(
        &mut self,
        parent: Option<NodeId>,
    ) -> bool {
        let Some(parent) = parent else {
            return true;
        };
        let nodes = self.program_nodes(parent);
        match nodes[parent].kind {
            ast::Kind::IfStatement
            | ast::Kind::DoStatement
            | ast::Kind::WhileStatement
            | ast::Kind::WithStatement
            | ast::Kind::ForStatement
            | ast::Kind::ForInStatement
            | ast::Kind::ForOfStatement => false,
            ast::Kind::LabeledStatement => {
                self.container_allows_block_scoped_variable(nodes[parent].parent)
            }
            _ => true,
        }
    }

    /// `func (c *Checker) checkGrammarMetaProperty` (grammarchecks.go:1813).
    pub(crate) fn check_grammar_meta_property(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let data = nodes[node].as_meta_property();
        let node_name = data.name.expect("meta property name");
        let name_text = nodes[node_name].text(&nodes).to_string();

        match data.keyword_token {
            ast::Kind::NewKeyword => {
                if name_text != "target" {
                    return self.grammar_error_on_node(
                        node_name,
                        &diagnostics::X_0_is_not_a_valid_meta_property_for_keyword_1_Did_you_mean_2,
                        &[
                            name_text,
                            scanner::token_to_string(data.keyword_token).to_string(),
                            "target".to_string(),
                        ],
                    );
                }
            }
            ast::Kind::ImportKeyword => {
                if name_text != "meta" {
                    let is_callee = nodes[node].parent.is_some_and(|p| {
                        ast::is_call_expression(&nodes[p]) && nodes[p].expression() == Some(node)
                    });
                    if ast::is_import_phase_meta_property(&nodes[node], &nodes) {
                        if !is_callee {
                            return self.grammar_error_at_pos(
                                node,
                                nodes[node].end(),
                                0,
                                &diagnostics::X_0_expected,
                                &["(".to_string()],
                            );
                        }
                    } else {
                        if is_callee {
                            return self.grammar_error_on_node(
                                node_name,
                                &diagnostics::X_0_is_not_a_valid_meta_property_for_keyword_import_Did_you_mean_meta_defer_or_source,
                                &[name_text],
                            );
                        }
                        return self.grammar_error_on_node(
                            node_name,
                            &diagnostics::X_0_is_not_a_valid_meta_property_for_keyword_1_Did_you_mean_2,
                            &[
                                name_text,
                                scanner::token_to_string(data.keyword_token).to_string(),
                                "meta".to_string(),
                            ],
                        );
                    }
                }
            }
            _ => {}
        }

        false
    }

    /// `func (c *Checker) checkGrammarConstructorTypeParameters` (grammarchecks.go:1841).
    pub(crate) fn check_grammar_constructor_type_parameters(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let range = nodes[node]
            .function_like_data()
            .and_then(|d| d.type_parameters.clone());
        if let Some(range) = range {
            let pos = if range.pos() == range.end() {
                range.pos()
            } else {
                let source_file =
                    ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
                scanner::skip_trivia(&nodes[source_file].as_source_file().text, range.pos())
            };
            return self.grammar_error_at_pos(
                node,
                pos,
                range.end() - pos,
                &diagnostics::Type_parameters_cannot_appear_on_a_constructor_declaration,
                &[],
            );
        }

        false
    }

    /// `func (c *Checker) checkGrammarConstructorTypeAnnotation` (grammarchecks.go:1856).
    pub(crate) fn check_grammar_constructor_type_annotation(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if let Some(t) = nodes[node].function_like_data().and_then(|d| d.type_) {
            return self.grammar_error_on_node(
                t,
                &diagnostics::Type_annotation_cannot_appear_on_a_constructor_declaration,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarProperty` (grammarchecks.go:1864).
    pub(crate) fn check_grammar_property(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let property_name = nodes[node].name().expect("property name");
        if ast::is_computed_property_name(&nodes[property_name])
            && nodes[property_name].expression().is_some_and(|e| {
                ast::is_binary_expression(&nodes[e])
                    && nodes[e].as_binary_expression().operator_token == ast::Kind::InKeyword
            })
        {
            let first_member = nodes[node]
                .parent
                .and_then(|p| nodes[p].members().map(|m| m[0]))
                .expect("mapped type member");
            return self.grammar_error_on_node(
                first_member,
                &diagnostics::A_mapped_type_may_not_declare_properties_or_methods,
                &[],
            );
        }
        let parent = nodes[node].parent;
        if parent.is_some_and(|p| ast::is_class_like(Some(p), &nodes)) {
            if ast::is_string_literal(&nodes[property_name])
                && nodes[property_name].text(&nodes) == "constructor"
            {
                return self.grammar_error_on_node(
                    property_name,
                    &diagnostics::Classes_may_not_have_a_field_named_constructor,
                    &[],
                );
            }
            if self.check_grammar_for_invalid_dynamic_name(
                property_name,
                &diagnostics::A_computed_property_name_in_a_class_property_declaration_must_have_a_simple_literal_type_or_a_unique_symbol_type,
            ) {
                return true;
            }
            if ast::is_auto_accessor_property_declaration(&nodes[node])
                && self.check_grammar_for_invalid_question_mark(
                    nodes[node].postfix_token(),
                    &diagnostics::An_accessor_property_cannot_be_declared_optional,
                )
            {
                return true;
            }
        } else if parent.is_some_and(|p| ast::is_interface_declaration(&nodes[p])) {
            if self.check_grammar_for_invalid_dynamic_name(
                property_name,
                &diagnostics::A_computed_property_name_in_an_interface_must_refer_to_an_expression_whose_type_is_a_literal_type_or_a_unique_symbol_type,
            ) {
                return true;
            }
            if !ast::is_property_signature_declaration(&nodes[node]) {
                // Interfaces cannot contain property declarations
                panic!("Unexpected node kind {:?}", nodes[node].kind);
            }
            if let Some(initializer) = nodes[node].initializer() {
                return self.grammar_error_on_node(
                    initializer,
                    &diagnostics::An_interface_property_cannot_have_an_initializer,
                    &[],
                );
            }
        } else if parent.is_some_and(|p| ast::is_type_literal_node(&nodes[p])) {
            if self.check_grammar_for_invalid_dynamic_name(
                property_name,
                &diagnostics::A_computed_property_name_in_a_type_literal_must_refer_to_an_expression_whose_type_is_a_literal_type_or_a_unique_symbol_type,
            ) {
                return true;
            }
            if !ast::is_property_signature_declaration(&nodes[node]) {
                // Type literals cannot contain property declarations
                panic!("Unexpected node kind {:?}", nodes[node].kind);
            }
            if let Some(initializer) = nodes[node].initializer() {
                return self.grammar_error_on_node(
                    initializer,
                    &diagnostics::A_type_literal_property_cannot_have_an_initializer,
                    &[],
                );
            }
        }

        let nodes = self.program_nodes(node);
        if nodes[node].flags.intersects(ast::NodeFlags::AMBIENT) {
            self.check_ambient_initializer(node);
        }

        let nodes = self.program_nodes(node);
        if ast::is_property_declaration(&nodes[node]) {
            let prop_decl = nodes[node].as_property_declaration();
            let postfix_token = prop_decl.named_member_base.postfix_token;
            if let Some(postfix_token) = postfix_token
                && nodes[postfix_token].kind == ast::Kind::ExclamationToken
            {
                if prop_decl.initializer.is_some() {
                    return self.grammar_error_on_node(
                        postfix_token,
                        &diagnostics::Declarations_with_initializers_cannot_also_have_definite_assignment_assertions,
                        &[],
                    );
                } else if prop_decl.type_.is_none() {
                    return self.grammar_error_on_node(
                        postfix_token,
                        &diagnostics::Declarations_with_definite_assignment_assertions_must_also_have_type_annotations,
                        &[],
                    );
                } else if !nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_class_like(Some(p), &nodes))
                    || nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                    || ast::is_static(&nodes[node])
                    || ast::has_abstract_modifier(&nodes[node])
                {
                    return self.grammar_error_on_node(
                        postfix_token,
                        &diagnostics::A_definite_assignment_assertion_is_not_permitted_in_this_context,
                        &[],
                    );
                }
            }
        }

        false
    }

    /// `func (c *Checker) checkAmbientInitializer` (grammarchecks.go:1925).
    pub(crate) fn check_ambient_initializer(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let (initializer, type_node) = match nodes[node].kind {
            ast::Kind::VariableDeclaration => {
                let var_decl = nodes[node].as_variable_declaration();
                (var_decl.initializer, var_decl.type_)
            }
            ast::Kind::PropertyDeclaration => {
                let prop_decl = nodes[node].as_property_declaration();
                (prop_decl.initializer, prop_decl.type_)
            }
            ast::Kind::PropertySignature => {
                let prop_sig = nodes[node].as_property_signature_declaration();
                (prop_sig.initializer, prop_sig.type_)
            }
            _ => panic!("Unexpected node kind {:?}", nodes[node].kind),
        };

        if let Some(initializer) = initializer {
            let is_invalid_initializer =
                !(is_initializer_string_or_number_literal_expression(initializer, &nodes)
                    || self.is_initializer_simple_literal_enum_reference(initializer)
                    || nodes[initializer].kind == ast::Kind::TrueKeyword
                    || nodes[initializer].kind == ast::Kind::FalseKeyword
                    || is_initializer_big_int_literal_expression(initializer, &nodes));
            let is_const_or_readonly = is_declaration_readonly(node, &nodes)
                || (ast::is_variable_declaration(&nodes[node]) && self.is_var_const_like(node));
            if is_const_or_readonly && type_node.is_none() {
                if is_invalid_initializer {
                    return self.grammar_error_on_node(
                        initializer,
                        &diagnostics::A_const_initializer_in_an_ambient_context_must_be_a_string_or_numeric_literal_or_literal_enum_reference,
                        &[],
                    );
                }
            } else {
                return self.grammar_error_on_node(
                    initializer,
                    &diagnostics::Initializers_are_not_allowed_in_ambient_contexts,
                    &[],
                );
            }
        }

        false
    }

    /// `func (c *Checker) isInitializerSimpleLiteralEnumReference` (grammarchecks.go:1978).
    pub(crate) fn is_initializer_simple_literal_enum_reference(&mut self, expr: NodeId) -> bool {
        let nodes = self.program_nodes(expr);
        if ast::is_property_access_expression(&nodes[expr]) {
            let t = self.check_expression_cached(expr);
            return self
                .types
                .get(t)
                .flags
                .intersects(crate::types::TypeFlags::ENUM_LIKE);
        }

        if ast::is_element_access_expression(&nodes[expr]) {
            let element_access = nodes[expr].as_element_access_expression();
            let argument_expression = element_access
                .argument_expression
                .expect("argumentExpression");
            let expression = element_access.expression.expect("expression");

            if is_initializer_string_or_number_literal_expression(argument_expression, &nodes)
                && ast::is_entity_name_expression(&nodes[expression], &nodes)
            {
                let t = self.check_expression_cached(expr);
                return self
                    .types
                    .get(t)
                    .flags
                    .intersects(crate::types::TypeFlags::ENUM_LIKE);
            }
            return false;
        }

        false
    }

    /// `func (c *Checker) checkGrammarTopLevelElementForRequiredDeclareModifier` (grammarchecks.go:1994).
    pub(crate) fn check_grammar_top_level_element_for_required_declare_modifier(
        &mut self,
        node: NodeId,
    ) -> bool {
        // A declare modifier is required for any top level .d.ts declaration except export=, export default, export as namespace
        // interfaces and imports categories:
        //
        //  DeclarationElement:
        //     ExportAssignment
        //     export_opt   InterfaceDeclaration
        //     export_opt   TypeAliasDeclaration
        //     export_opt   ImportDeclaration
        //     export_opt   ExternalImportDeclaration
        //     export_opt   AmbientDeclaration
        //
        // TODO: The spec needs to be amended to reflect this grammar.
        let nodes = self.program_nodes(node);
        if nodes[node].kind == ast::Kind::InterfaceDeclaration
            || nodes[node].kind == ast::Kind::TypeAliasDeclaration
            || nodes[node].kind == ast::Kind::ImportDeclaration
            || nodes[node].kind == ast::Kind::JSImportDeclaration
            || nodes[node].kind == ast::Kind::ImportEqualsDeclaration
            || nodes[node].kind == ast::Kind::ExportDeclaration
            || nodes[node].kind == ast::Kind::ExportAssignment
            || nodes[node].kind == ast::Kind::NamespaceExportDeclaration
            || ast::has_syntactic_modifier(
                &nodes[node],
                ast::ModifierFlags::AMBIENT
                    | ast::ModifierFlags::EXPORT
                    | ast::ModifierFlags::DEFAULT,
            )
        {
            return false;
        }

        self.grammar_error_on_first_token(
            node,
            &diagnostics::Top_level_declarations_in_d_ts_files_must_start_with_either_a_declare_or_export_modifier,
            &[],
        )
    }

    /// `func (c *Checker) checkGrammarTopLevelElementsForRequiredDeclareModifier` (grammarchecks.go:2014).
    /// `file` is the source file node (`*ast.SourceFile` → `NodeId`).
    pub(crate) fn check_grammar_top_level_elements_for_required_declare_modifier(
        &mut self,
        file: NodeId,
    ) -> bool {
        let nodes = self.program_nodes(file);
        let statements: Vec<NodeId> = nodes[file]
            .statements()
            .map(|s| s.to_vec())
            .unwrap_or_default();
        for decl in statements {
            if ast::is_declaration_node(&nodes[decl])
                || nodes[decl].kind == ast::Kind::VariableStatement
            {
                if self.check_grammar_top_level_element_for_required_declare_modifier(decl) {
                    return true;
                }
            }
        }
        false
    }

    /// `func (c *Checker) checkGrammarSourceFile` (grammarchecks.go:2025).
    /// `node` is the source file node (`*ast.SourceFile` → `NodeId`).
    pub(crate) fn check_grammar_source_file(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
            && self.check_grammar_top_level_elements_for_required_declare_modifier(node)
    }

    /// `func (c *Checker) checkGrammarStatementInAmbientContext` (grammarchecks.go:2029).
    pub(crate) fn check_grammar_statement_in_ambient_context(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if nodes[node].flags.intersects(ast::NodeFlags::AMBIENT) {
            let parent = nodes[node].parent;
            // Find containing block which is either Block, ModuleBlock, SourceFile
            if !self
                .node_links
                .get(node)
                .has_reported_statement_in_ambient_context
                && (ast::is_function_like(parent, &nodes)
                    || parent.is_some_and(|p| ast::is_accessor(&nodes[p])))
            {
                let reported = self.grammar_error_on_first_token(
                    node,
                    &diagnostics::An_implementation_cannot_be_declared_in_ambient_contexts,
                    &[],
                );
                self.node_links
                    .get(node)
                    .has_reported_statement_in_ambient_context = reported;
                return reported;
            }

            // We are either parented by another statement, or some sort of block.
            // If we're in a block, we only want to really report an error once
            // to prevent noisiness.  So use a bit on the block to indicate if
            // this has already been reported, and don't report if it has.
            //
            if parent.is_some_and(|p| {
                matches!(
                    nodes[p].kind,
                    ast::Kind::Block | ast::Kind::ModuleBlock | ast::Kind::SourceFile
                )
            }) {
                let parent = parent.expect("parent");
                // Check if the containing block ever report this error
                if !self
                    .node_links
                    .get(parent)
                    .has_reported_statement_in_ambient_context
                {
                    let reported = self.grammar_error_on_first_token(
                        node,
                        &diagnostics::Statements_are_not_allowed_in_ambient_contexts,
                        &[],
                    );
                    self.node_links
                        .get(parent)
                        .has_reported_statement_in_ambient_context = reported;
                    return reported;
                }
            } else {
                // We must be parented by a statement.  If so, there's no need
                // to report the error as our parent will have already done it.
                // debug.Assert(ast.IsStatement(node.Parent)) // !!! commented out in strada - fails if uncommented
            }
        }
        false
    }

    /// `func (c *Checker) checkGrammarNumericLiteral` (grammarchecks.go:2059).
    pub(crate) fn check_grammar_numeric_literal(&mut self, node: NodeId) {
        let nodes = self.program_nodes(node);
        let node_text = scanner::get_text_of_node(node, &nodes);

        // Realism (size) checking
        // We should test against `getTextOfNode(node)` rather than `node.text`, because `node.text` for large numeric literals can contain "."
        // e.g. `node.text` for numeric literal `1100000000000000000000` is `1.1e21`.
        let is_fractional = node_text.contains('.');
        let is_scientific = nodes[node]
            .literal_like_data()
            .is_some_and(|d| d.token_flags.intersects(ast::TokenFlags::SCIENTIFIC));

        // Scientific notation (e.g. 2e54 and 1e00000000010) can't be converted to bigint
        // Fractional numbers (e.g. 9000000000000000.001) are inherently imprecise anyway
        if is_fractional || is_scientific {
            return;
        }

        // Here `node` is guaranteed to be a numeric literal representing an integer.
        // We need to judge whether the integer `node` represents is <= 2 ** 53 - 1, which can be accomplished by comparing to `value` defined below because:
        // 1) when `node` represents an integer <= 2 ** 53 - 1, `node.text` is its exact string representation and thus `value` precisely represents the integer.
        // 2) otherwise, although `node.text` may be imprecise string representation, its mathematical value and consequently `value` cannot be less than 2 ** 53,
        //    thus the result of the predicate won't be affected.
        let value = tsc_jsnum::from_string(&nodes[node].text(&nodes));
        if value <= tsc_jsnum::MAX_SAFE_INTEGER {
            return;
        }

        let diagnostic = crate::checker_b::create_diagnostic_for_node(
            Some(node),
            &nodes,
            &diagnostics::Numeric_literals_with_absolute_values_equal_to_2_53_or_greater_are_too_large_to_be_represented_accurately_as_integers,
            &[],
        );
        self.add_error_or_suggestion(false, &diagnostic);
    }

    /// `func (c *Checker) checkGrammarBigIntLiteral` (grammarchecks.go:2087).
    pub(crate) fn check_grammar_big_int_literal(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let literal_type = nodes[node]
            .parent
            .is_some_and(|p| ast::is_literal_type_node(&nodes[p]))
            || (nodes[node]
                .parent
                .is_some_and(|p| ast::is_prefix_unary_expression(&nodes[p]))
                && nodes[node]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .is_some_and(|p| ast::is_literal_type_node(&nodes[p])));
        if !literal_type {
            // Don't error on BigInt literals in ambient contexts
            if !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
                && self.language_version < ScriptTarget::ES2020
            {
                if self.grammar_error_on_node(
                    node,
                    &diagnostics::BigInt_literals_are_not_available_when_targeting_lower_than_ES2020,
                    &[],
                ) {
                    return true;
                }
            }
        }
        false
    }

    /// `func (c *Checker) checkGrammarImportClause` (grammarchecks.go:2100).
    pub(crate) fn check_grammar_import_clause(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        let data = nodes[node].as_import_clause();
        match data.phase_modifier {
            ast::Kind::TypeKeyword => {
                if !nodes[node].flags.intersects(ast::NodeFlags::JSDOC)
                    && data.name.is_some()
                    && data.named_bindings.is_some()
                {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::A_type_only_import_can_specify_a_default_import_or_named_bindings_but_not_both,
                        &[],
                    );
                }
                if let Some(named_bindings) = data.named_bindings
                    && nodes[named_bindings].kind == ast::Kind::NamedImports
                {
                    return self.check_grammar_type_only_named_imports_or_exports(named_bindings);
                }
            }
            ast::Kind::DeferKeyword => {
                if data.name.is_some() {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::Default_imports_are_not_allowed_in_a_deferred_import,
                        &[],
                    );
                }
                if data.named_bindings.is_none() {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::A_deferred_import_must_specify_a_namespace_binding,
                        &[],
                    );
                }
                if nodes[data.named_bindings.unwrap()].kind == ast::Kind::NamedImports {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::Named_imports_are_not_allowed_in_a_deferred_import,
                        &[],
                    );
                }
                if self.module_kind.supports_deferred_imports() {
                    return false;
                }
                return self.grammar_error_on_node(
                    node,
                    &diagnostics::Deferred_imports_are_only_supported_when_the_module_flag_is_set_to_esnext_or_preserve,
                    &[],
                );
            }
            ast::Kind::SourceKeyword => {
                if data.named_bindings.is_some() {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::Named_and_namespace_imports_are_not_allowed_in_a_source_phase_import,
                        &[],
                    );
                }
                if data.name.is_none() {
                    return self.grammar_error_on_node(
                        node,
                        &diagnostics::A_source_phase_import_must_specify_a_local_binding,
                        &[],
                    );
                }
                if self.module_kind.supports_source_phase_imports() {
                    let parent = nodes[node].parent.expect("import clause parent");
                    let module_specifier =
                        crate::checker_b::get_module_specifier_from_node(parent, &nodes);
                    if let Some(module_specifier) = module_specifier
                        && self.get_emit_syntax_for_module_specifier_expression(module_specifier)
                            == ModuleKind::CommonJS
                    {
                        return self.grammar_error_on_node(
                            node,
                            &diagnostics::Source_phase_imports_are_not_allowed_on_statements_that_compile_to_CommonJS_require_calls,
                            &[],
                        );
                    }
                    return false;
                }
                return self.grammar_error_on_node(
                    node,
                    &diagnostics::Source_phase_imports_are_only_supported_when_the_module_option_is_set_to_esnext_nodenext_or_preserve,
                    &[],
                );
            }
            _ => {}
        }
        false
    }

    /// `func (c *Checker) checkGrammarImportAttributeValues` (grammarchecks.go:2142).
    pub(crate) fn check_grammar_import_attribute_values(&mut self, node: NodeId) -> bool {
        let mut has_error = false;
        let nodes = self.program_nodes(node);
        let attributes: Vec<NodeId> = nodes[node]
            .as_import_attributes()
            .attributes
            .as_ref()
            .map(|a| a.nodes().to_vec())
            .unwrap_or_default();
        for attribute in attributes {
            let value = nodes[attribute].as_import_attribute().value.expect("value");
            if ast::is_string_literal(&nodes[value]) {
                continue;
            }
            has_error = true;
            self.error(
                Some(value),
                &diagnostics::Import_attribute_values_must_be_string_literal_expressions,
                &[],
            );
        }
        has_error
    }

    /// `func (c *Checker) checkGrammarTypeOnlyNamedImportsOrExports` (grammarchecks.go:2155).
    pub(crate) fn check_grammar_type_only_named_imports_or_exports(
        &mut self,
        named_bindings: NodeId,
    ) -> bool {
        let nodes = self.program_nodes(named_bindings);
        let elements: Vec<NodeId> = nodes[named_bindings]
            .element_list()
            .map(|l| l.nodes().to_vec())
            .unwrap_or_default();
        for specifier in elements {
            let specifier_is_type_only = nodes[specifier].is_type_only();
            let message = if nodes[specifier].kind == ast::Kind::ImportSpecifier {
                &diagnostics::The_type_modifier_cannot_be_used_on_a_named_import_when_import_type_is_used_on_its_import_statement
            } else {
                &diagnostics::The_type_modifier_cannot_be_used_on_a_named_export_when_export_type_is_used_on_its_export_statement
            };

            if specifier_is_type_only {
                return self.grammar_error_on_first_token(specifier, message, &[]);
            }
        }

        false
    }

    /// `func (c *Checker) checkGrammarImportCallExpression` (grammarchecks.go:2176).
    pub(crate) fn check_grammar_import_call_expression(&mut self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        if self.compiler_options.verbatim_module_syntax.is_true()
            && self.module_kind == ModuleKind::CommonJS
        {
            let message = get_verbatim_module_syntax_error_message(node, &nodes);
            return self.grammar_error_on_node(node, message, &[]);
        }

        let import_expr = nodes[node].expression().expect("call expression");
        if ast::is_import_source_meta_property(&nodes[import_expr], &nodes) {
            if self.module_kind.supports_source_phase_imports() {
                // ok — falls through to the call-argument checks below
            } else {
                return self.grammar_error_on_node(
                    node,
                    &diagnostics::Source_phase_imports_are_only_supported_when_the_module_option_is_set_to_esnext_nodenext_or_preserve,
                    &[],
                );
            }
        } else if ast::is_import_defer_meta_property(&nodes[import_expr], &nodes) {
            if !self.module_kind.supports_deferred_imports() {
                return self.grammar_error_on_node(
                    node,
                    &diagnostics::Deferred_imports_are_only_supported_when_the_module_flag_is_set_to_esnext_or_preserve,
                    &[],
                );
            }
        } else if self.module_kind == ModuleKind::ES2015 {
            return self.grammar_error_on_node(
                node,
                &diagnostics::Dynamic_imports_are_only_supported_when_the_module_flag_is_set_to_es2020_es2022_esnext_commonjs_amd_system_umd_node16_node18_node20_or_nodenext,
                &[],
            );
        }

        let node_as_call = nodes[node].as_call_expression();
        let (question_dot_token, type_arguments, arguments) = (
            node_as_call.question_dot_token,
            node_as_call.type_arguments.clone(),
            node_as_call.arguments.clone(),
        );
        if ast::is_source_phase_import_call(&nodes[node], &nodes)
            && let Some(question_dot_token) = question_dot_token
        {
            return self.grammar_error_on_node(
                question_dot_token,
                &diagnostics::Optional_chaining_cannot_be_used_with_import_source,
                &[],
            );
        }
        if type_arguments.is_some() {
            return self.grammar_error_on_node(
                node,
                &diagnostics::This_use_of_import_is_invalid_import_calls_can_be_written_but_they_must_have_parentheses_and_cannot_have_type_arguments,
                &[],
            );
        }

        let Some(node_arguments) = arguments else {
            return self.grammar_error_on_node(
                node,
                &diagnostics::Dynamic_imports_can_only_accept_a_module_specifier_and_an_optional_set_of_attributes_as_arguments,
                &[],
            );
        };
        let argument_nodes = node_arguments.nodes().to_vec();
        if !(ModuleKind::Node16 <= self.module_kind && self.module_kind <= ModuleKind::NodeNext)
            && self.module_kind != ModuleKind::ESNext
            && self.module_kind != ModuleKind::Preserve
        {
            // We are allowed trailing comma after proposal-import-assertions.
            self.check_grammar_for_disallowed_trailing_comma(
                Some(&node_arguments),
                &diagnostics::Trailing_comma_not_allowed,
                &nodes,
            );

            if argument_nodes.len() > 1 {
                let import_attributes_argument = argument_nodes[1];
                return self.grammar_error_on_node(
                    import_attributes_argument,
                    &diagnostics::Dynamic_imports_only_support_a_second_argument_when_the_module_option_is_set_to_esnext_node16_node18_node20_nodenext_or_preserve,
                    &[],
                );
            }
        }

        if argument_nodes.is_empty() || argument_nodes.len() > 2 {
            return self.grammar_error_on_node(
                node,
                &diagnostics::Dynamic_imports_can_only_accept_a_module_specifier_and_an_optional_set_of_attributes_as_arguments,
                &[],
            );
        }

        // see: parseArgumentOrArrayLiteralElement...we use this function which parse arguments of callExpression to parse specifier for dynamic import.
        // parseArgumentOrArrayLiteralElement allows spread element to be in an argument list which is not allowed as specifier in dynamic import.
        let spread_element = argument_nodes
            .iter()
            .copied()
            .find(|&n| ast::is_spread_element(&nodes[n]));
        if let Some(spread_element) = spread_element {
            return self.grammar_error_on_node(
                spread_element,
                &diagnostics::Argument_of_dynamic_import_cannot_be_spread_element,
                &[],
            );
        }
        false
    }

    /// `func (c *Checker) checkGrammarImportAttributesType` (grammarchecks.go:2229).
    pub(crate) fn check_grammar_import_attributes_type(&mut self, attributes: NodeId) -> bool {
        let nodes = self.program_nodes(attributes);
        let members = nodes[attributes].member_list().map(|m| m.nodes().to_vec());
        let Some(members) = members else {
            return false;
        };
        for member in members {
            if nodes[member].kind != ast::Kind::PropertySignature {
                return self.grammar_error_on_node(
                    member,
                    &diagnostics::An_import_attributes_type_may_only_contain_property_signatures,
                    &[],
                );
            }
            let property_signature = nodes[member].as_property_signature_declaration();
            if let Some(modifiers) = nodes[member].modifiers() {
                for &modifier in modifiers.nodes.iter() {
                    if nodes[modifier].kind == ast::Kind::ReadonlyKeyword {
                        return self.grammar_error_on_node(
                            modifier,
                            &diagnostics::An_import_attributes_property_cannot_have_a_readonly_modifier,
                            &[],
                        );
                    }
                }
            }
            if property_signature.type_.is_none() {
                return self.grammar_error_on_node(
                    member,
                    &diagnostics::An_import_attributes_property_must_have_a_type_annotation,
                    &[],
                );
            }
            if nodes[member].question_token(&nodes).is_some() {
                return self.grammar_error_on_node(
                    member,
                    &diagnostics::An_import_attributes_property_cannot_be_optional,
                    &[],
                );
            }
            let name = property_signature.named_member_base.name.expect("name");
            if !(ast::is_string_literal_like(&nodes[name]) || ast::is_identifier(&nodes[name])) {
                return self.grammar_error_on_node(
                    name,
                    &diagnostics::An_import_attributes_property_must_have_a_string_literal_or_identifier_name,
                    &[],
                );
            }
            if nodes[name].text(&nodes) == "resolution-mode" {
                let text = nodes[name].text(&nodes).to_string();
                return self.grammar_error_on_node(
                    name,
                    &diagnostics::X_0_is_not_a_valid_key_for_an_import_attributes_type,
                    &[text],
                );
            }

            let type_node = property_signature.type_.expect("type");
            if !ast::is_literal_type_node(&nodes[type_node])
                || !ast::is_string_literal(
                    &nodes[type_node]
                        .as_literal_type_node()
                        .literal
                        .expect("literal"),
                )
            {
                return self.grammar_error_on_node(
                    type_node,
                    &diagnostics::An_import_attributes_property_must_have_a_string_literal_type_annotation,
                    &[],
                );
            }
        }
        false
    }
}

/// `func getIdentifierFromEntityNameExpression` (grammarchecks.go:56).
#[allow(dead_code)]
pub(crate) fn get_identifier_from_entity_name_expression(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    match nodes[node].kind {
        ast::Kind::Identifier => Some(node),
        ast::Kind::PropertyAccessExpression => nodes[node].name(),
        _ => None,
    }
}

/// `func isInitializerStringOrNumberLiteralExpression` (grammarchecks.go:1960).
fn is_initializer_string_or_number_literal_expression(expr: NodeId, nodes: &[ast::Node]) -> bool {
    ast::is_string_or_numeric_literal_like(&nodes[expr])
        || (nodes[expr].kind == ast::Kind::PrefixUnaryExpression
            && nodes[expr].as_prefix_unary_expression().operator == ast::Kind::MinusToken
            && nodes[expr]
                .as_prefix_unary_expression()
                .operand
                .is_some_and(|o| nodes[o].kind == ast::Kind::NumericLiteral))
}

/// `func isInitializerBigIntLiteralExpression` (grammarchecks.go:1965).
fn is_initializer_big_int_literal_expression(expr: NodeId, nodes: &[ast::Node]) -> bool {
    if nodes[expr].kind == ast::Kind::BigIntLiteral {
        return true;
    }

    if nodes[expr].kind == ast::Kind::PrefixUnaryExpression {
        let unary_expr = nodes[expr].as_prefix_unary_expression();
        return unary_expr.operator == ast::Kind::MinusToken
            && unary_expr
                .operand
                .is_some_and(|o| nodes[o].kind == ast::Kind::BigIntLiteral);
    }

    false
}

/// `func isDeclarationReadonly` (utilities.go:871) — PORT: the committed
/// `crate::utilities::is_declaration_readonly` lands with utilities.go;
/// inlined here so grammarchecks.rs does not depend on that landing order.
/// `GetCombinedModifierFlags(declaration)&ModifierFlagsReadonly != 0 &&
/// !IsParameterPropertyDeclaration(declaration, declaration.Parent)`.
fn is_declaration_readonly(declaration: NodeId, nodes: &[ast::Node]) -> bool {
    ast::get_combined_modifier_flags(declaration, nodes).intersects(ast::ModifierFlags::READONLY)
        && !nodes[declaration]
            .parent
            .is_some_and(|p| ast::is_parameter_property_declaration(&nodes[declaration], &nodes[p]))
}

/// `getVerbatimModuleSyntaxErrorMessage` (checker.go) — PORT: the sibling
/// copy in checker_a.rs is module-private; duplicated here so
/// grammarchecks.rs does not depend on its visibility.
fn get_verbatim_module_syntax_error_message(
    node: NodeId,
    nodes: &[ast::Node],
) -> &'static diagnostics::Message {
    let source_file = ast::get_source_file_of_node(Some(node), nodes).expect("source file");
    let file_name = nodes[source_file].as_source_file().file_name();
    // Check if the file is .cts or .cjs (CommonJS-specific extensions)
    if file_name.extension_is_one_of(&[tsc_tspath::EXTENSION_CTS, tsc_tspath::EXTENSION_CJS]) {
        return &diagnostics::ECMAScript_imports_and_exports_cannot_be_written_in_a_CommonJS_file_under_verbatimModuleSyntax;
    }
    // For .ts, .tsx, .js, etc.
    &diagnostics::ECMAScript_imports_and_exports_cannot_be_written_in_a_CommonJS_file_under_verbatimModuleSyntax_Adjust_the_type_field_in_the_nearest_package_json_to_make_this_file_an_ECMAScript_module_or_adjust_your_verbatimModuleSyntax_module_and_moduleResolution_settings_in_TypeScript
}
