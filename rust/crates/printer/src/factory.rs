// Ported from tsc/internal/printer/factory.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The printer `NodeFactory` wraps `ast::NodeFactory`, adding generated-name
// allocation, emit-context bookkeeping, helper construction, and various
// convenience constructors used by transforms.
//
// PORT: `type NodeFactory struct { ast.NodeFactory; emitContext *EmitContext }`
// cannot be expressed directly — the factory is owned by `EmitContext` while
// its hooks call back into the context. The factory therefore holds the same
// `Shared` tables handle as the `EmitContext` and derefs to the inner
// `ast::NodeFactory` for the generated constructors.

use std::ops::{Deref, DerefMut};
use std::sync::Arc;

use tsc_ast::{self as ast, Kind, ModifierList, Node, NodeId, NodeList};

use crate::emit_context::{
    AutoGenerateId, AutoGenerateInfo, AutoGenerateOptions, Shared, next_auto_generate_id,
};
use crate::emit_flags::{EmitFlags, GeneratedIdentifierFlags};
use crate::emit_helpers;
use crate::emit_helpers::EmitHelper;

/// `type NodeFactory struct`
pub struct NodeFactory {
    pub(crate) inner: ast::NodeFactory<'static>,
    pub(crate) shared: Shared,
}

impl Deref for NodeFactory {
    type Target = ast::NodeFactory<'static>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for NodeFactory {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl NodeFactory {
    /// `NewNodeFactory`
    pub(crate) fn new(inner: ast::NodeFactory<'static>, shared: Shared) -> NodeFactory {
        NodeFactory { inner, shared }
    }

    /// `newGeneratedIdentifier` (as a method; see the free function below for
    /// the implementation shared with the `EmitContext` visitor hooks).
    pub fn new_generated_identifier(
        &mut self,
        nodes: &mut Vec<Node>,
        kind: GeneratedIdentifierFlags,
        text: &str,
        node: Option<NodeId>,
        options: &AutoGenerateOptions,
    ) -> NodeId {
        new_generated_identifier(
            &self.shared,
            &mut self.inner,
            nodes,
            kind,
            text,
            node,
            options,
        )
    }

    /// `NewTempVariable` — allocates a new temp variable name, but does not
    /// record it in the environment. It is recommended to pass this to either
    /// `AddVariableDeclaration` or `AddLexicalDeclaration` to ensure it is
    /// properly tracked, if you are not otherwise handling it yourself.
    pub fn new_temp_variable(&mut self, nodes: &mut Vec<Node>) -> NodeId {
        self.new_temp_variable_ex(nodes, &AutoGenerateOptions::default())
    }

    /// `NewTempVariableEx`
    pub fn new_temp_variable_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        options: &AutoGenerateOptions,
    ) -> NodeId {
        self.new_generated_identifier(nodes, GeneratedIdentifierFlags::AUTO, "", None, options)
    }

    /// `NewLoopVariable` — allocates a new loop variable name.
    pub fn new_loop_variable(&mut self, nodes: &mut Vec<Node>) -> NodeId {
        self.new_loop_variable_ex(nodes, &AutoGenerateOptions::default())
    }

    /// `NewLoopVariableEx`
    pub fn new_loop_variable_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        options: &AutoGenerateOptions,
    ) -> NodeId {
        self.new_generated_identifier(nodes, GeneratedIdentifierFlags::LOOP, "", None, options)
    }

    /// `NewUniqueName` — allocates a new unique name based on the provided
    /// text.
    pub fn new_unique_name(&mut self, nodes: &mut Vec<Node>, text: &str) -> NodeId {
        self.new_unique_name_ex(nodes, text, &AutoGenerateOptions::default())
    }

    /// `NewUniqueNameEx`
    pub fn new_unique_name_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        text: &str,
        options: &AutoGenerateOptions,
    ) -> NodeId {
        self.new_generated_identifier(nodes, GeneratedIdentifierFlags::UNIQUE, text, None, options)
    }

    /// `NewGeneratedNameForNode` — allocates a new unique name based on the
    /// provided node.
    pub fn new_generated_name_for_node(&mut self, nodes: &mut Vec<Node>, node: NodeId) -> NodeId {
        self.new_generated_name_for_node_ex(nodes, node, &AutoGenerateOptions::default())
    }

    /// `NewGeneratedNameForNodeEx`
    pub fn new_generated_name_for_node_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        options: &AutoGenerateOptions,
    ) -> NodeId {
        let mut options = options.clone();
        if !options.prefix.is_empty() || !options.suffix.is_empty() {
            options.flags |= GeneratedIdentifierFlags::OPTIMISTIC;
        }
        self.new_generated_identifier(
            nodes,
            GeneratedIdentifierFlags::NODE,
            "",
            Some(node),
            &options,
        )
    }

    /// `newGeneratedPrivateIdentifier`
    pub fn new_generated_private_identifier(
        &mut self,
        nodes: &mut Vec<Node>,
        kind: GeneratedIdentifierFlags,
        text: &str,
        node: Option<NodeId>,
        options: &AutoGenerateOptions,
    ) -> NodeId {
        new_generated_private_identifier(
            &self.shared,
            &mut self.inner,
            nodes,
            kind,
            text,
            node,
            options,
        )
    }

    /// `NewUniquePrivateName` — allocates a new unique private name based on
    /// the provided text.
    pub fn new_unique_private_name(&mut self, nodes: &mut Vec<Node>, text: &str) -> NodeId {
        self.new_unique_private_name_ex(nodes, text, &AutoGenerateOptions::default())
    }

    /// `NewUniquePrivateNameEx`
    pub fn new_unique_private_name_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        text: &str,
        options: &AutoGenerateOptions,
    ) -> NodeId {
        self.new_generated_private_identifier(
            nodes,
            GeneratedIdentifierFlags::UNIQUE,
            text,
            None,
            options,
        )
    }

    /// `NewGeneratedPrivateNameForNode` — allocates a new unique private name
    /// based on the provided node.
    pub fn new_generated_private_name_for_node(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
    ) -> NodeId {
        self.new_generated_private_name_for_node_ex(nodes, node, &AutoGenerateOptions::default())
    }

    /// `NewGeneratedPrivateNameForNodeEx`
    pub fn new_generated_private_name_for_node_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        options: &AutoGenerateOptions,
    ) -> NodeId {
        let mut options = options.clone();
        if !options.prefix.is_empty() || !options.suffix.is_empty() {
            options.flags |= GeneratedIdentifierFlags::OPTIMISTIC;
        }
        self.new_generated_private_identifier(
            nodes,
            GeneratedIdentifierFlags::NODE,
            "",
            Some(node),
            &options,
        )
    }

    /// `NewStringLiteralFromNode` — allocates a new StringLiteral whose source
    /// text is derived from the provided node. This is often used to create a
    /// string representation of an Identifier or NumericLiteral.
    pub fn new_string_literal_from_node(
        &mut self,
        nodes: &mut Vec<Node>,
        text_source_node: NodeId,
    ) -> NodeId {
        let mut text = String::new();
        match nodes[text_source_node].kind {
            Kind::Identifier
            | Kind::PrivateIdentifier
            | Kind::JsxNamespacedName
            | Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TemplateHead
            | Kind::TemplateMiddle
            | Kind::TemplateTail
            | Kind::RegularExpressionLiteral => {
                text = nodes[text_source_node].text(nodes).into_owned();
            }
            _ => {}
        }
        let node = self
            .inner
            .new_string_literal(nodes, &text, ast::TokenFlags::NONE);
        self.shared
            .borrow_mut()
            .text_source
            .insert(node, text_source_node);
        node
    }

    //
    // Common Tokens
    //

    /// `NewThisExpression`
    pub fn new_this_expression(&mut self, nodes: &mut Vec<Node>) -> NodeId {
        self.inner.new_keyword_expression(nodes, Kind::ThisKeyword)
    }

    /// `NewTrueExpression`
    pub fn new_true_expression(&mut self, nodes: &mut Vec<Node>) -> NodeId {
        self.inner.new_keyword_expression(nodes, Kind::TrueKeyword)
    }

    /// `NewFalseExpression`
    pub fn new_false_expression(&mut self, nodes: &mut Vec<Node>) -> NodeId {
        self.inner.new_keyword_expression(nodes, Kind::FalseKeyword)
    }

    //
    // Common Operators
    //

    /// `NewCommaExpression`
    pub fn new_comma_expression(
        &mut self,
        nodes: &mut Vec<Node>,
        left: NodeId,
        right: NodeId,
    ) -> NodeId {
        self.new_binary_operator_expression(nodes, Kind::CommaToken, left, right)
    }

    /// `NewAssignmentExpression`
    pub fn new_assignment_expression(
        &mut self,
        nodes: &mut Vec<Node>,
        left: NodeId,
        right: NodeId,
    ) -> NodeId {
        self.new_binary_operator_expression(nodes, Kind::EqualsToken, left, right)
    }

    /// `NewLogicalORExpression`
    pub fn new_logical_or_expression(
        &mut self,
        nodes: &mut Vec<Node>,
        left: NodeId,
        right: NodeId,
    ) -> NodeId {
        self.new_binary_operator_expression(nodes, Kind::BarBarToken, left, right)
    }

    /// `NewLogicalANDExpression`
    pub fn new_logical_and_expression(
        &mut self,
        nodes: &mut Vec<Node>,
        left: NodeId,
        right: NodeId,
    ) -> NodeId {
        self.new_binary_operator_expression(nodes, Kind::AmpersandAmpersandToken, left, right)
    }

    /// `NewStrictEqualityExpression`
    pub fn new_strict_equality_expression(
        &mut self,
        nodes: &mut Vec<Node>,
        left: NodeId,
        right: NodeId,
    ) -> NodeId {
        self.new_binary_operator_expression(nodes, Kind::EqualsEqualsEqualsToken, left, right)
    }

    /// `NewStrictInequalityExpression`
    pub fn new_strict_inequality_expression(
        &mut self,
        nodes: &mut Vec<Node>,
        left: NodeId,
        right: NodeId,
    ) -> NodeId {
        self.new_binary_operator_expression(nodes, Kind::ExclamationEqualsEqualsToken, left, right)
    }

    /// Common implementation of the `New<Op>Expression` helpers.
    pub(crate) fn new_binary_operator_expression(
        &mut self,
        nodes: &mut Vec<Node>,
        kind: Kind,
        left: NodeId,
        right: NodeId,
    ) -> NodeId {
        new_binary_operator_expression(&mut self.inner, nodes, kind, left, right)
    }

    //
    // Compound Nodes
    //

    /// `NewVoidZeroExpression`
    pub fn new_void_zero_expression(&mut self, nodes: &mut Vec<Node>) -> NodeId {
        new_void_zero_expression(&mut self.inner, nodes)
    }

    /// `InlineExpressions` — converts a slice of expressions into a single
    /// comma-delimited expression. Returns `None` if `expressions` is empty.
    pub fn inline_expressions(
        &mut self,
        nodes: &mut Vec<Node>,
        expressions: &[NodeId],
    ) -> Option<NodeId> {
        if expressions.is_empty() {
            return None;
        }
        if expressions.len() == 1 {
            return Some(expressions[0]);
        }
        let expressions = flatten_comma_elements(nodes, expressions);
        let mut expression = expressions[0];
        for &next in &expressions[1..] {
            expression = self.new_comma_expression(nodes, expression, next);
        }
        Some(expression)
    }

    //
    // Utilities
    //

    /// `CreateExpressionFromEntityName`
    pub fn create_expression_from_entity_name(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
    ) -> NodeId {
        if ast::is_qualified_name(&nodes[node]) {
            let (left, right) = {
                let d = nodes[node].as_qualified_name();
                (
                    d.left.expect("QualifiedName.left"),
                    d.right.expect("QualifiedName.right"),
                )
            };
            let left = self.create_expression_from_entity_name(nodes, left);
            let right_loc = nodes[right].loc;
            let right = self.inner.clone_node(nodes, right);
            nodes[right].loc = right_loc;
            // TODO(rbuckton): Does this need to be parented?
            // PORT: parents are not tracked in the Rust AST.
            let prop_access = self.inner.new_property_access_expression(
                nodes,
                Some(left),
                None,
                Some(right),
                ast::NodeFlags::NONE,
            );
            nodes[prop_access].loc = nodes[node].loc;
            return prop_access;
        }
        let res = self.inner.clone_node(nodes, node);
        nodes[res].loc = nodes[node].loc;
        res
    }

    /// `RestoreEnclosingLabel`
    pub fn restore_enclosing_label(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        outermost_labeled_statement: NodeId,
    ) -> NodeId {
        let mut inner_label = node;
        let statement = nodes[outermost_labeled_statement]
            .as_labeled_statement()
            .statement;
        if let Some(statement) = statement
            && ast::is_labeled_statement(&nodes[statement])
        {
            inner_label = self.restore_enclosing_label(nodes, node, statement);
        }
        let label = nodes[outermost_labeled_statement]
            .as_labeled_statement()
            .label;
        self.inner
            .update_labeled_statement(nodes, outermost_labeled_statement, label, Some(inner_label))
            .unwrap_or(outermost_labeled_statement)
    }

    /// `CreateForOfBindingStatement` — creates a statement to bind the
    /// iteration value.
    pub fn create_for_of_binding_statement(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        bound_value: NodeId,
    ) -> NodeId {
        if ast::is_variable_declaration_list(&nodes[node]) {
            let first_declaration = nodes[node]
                .as_variable_declaration_list()
                .declarations
                .as_ref()
                .unwrap()
                .nodes[0];
            let first_name = nodes[first_declaration].name();
            let updated_declaration = self
                .inner
                .update_variable_declaration(
                    nodes,
                    first_declaration,
                    first_name,
                    None, /*exclamationToken*/
                    None, /*type*/
                    Some(bound_value),
                )
                .unwrap_or(first_declaration);
            let flags = nodes[node].flags;
            let declaration_list = self
                .inner
                .update_variable_declaration_list(
                    nodes,
                    node,
                    Some(self.inner.new_node_list([updated_declaration])),
                    flags,
                )
                .unwrap_or(node);
            let statement = self
                .inner
                .new_variable_statement(nodes, None, Some(declaration_list));
            nodes[statement].loc = nodes[node].loc;
            return statement;
        }
        let updated_expression = self.new_assignment_expression(nodes, node, bound_value);
        nodes[updated_expression].loc = nodes[node].loc;
        let statement = self
            .inner
            .new_expression_statement(nodes, Some(updated_expression));
        nodes[statement].loc = nodes[node].loc;
        statement
    }

    /// `NewTypeCheck`
    pub fn new_type_check(&mut self, nodes: &mut Vec<Node>, value: NodeId, tag: &str) -> NodeId {
        new_type_check(&mut self.inner, nodes, value, tag)
    }

    /// `NewMethodCall`
    pub fn new_method_call(
        &mut self,
        nodes: &mut Vec<Node>,
        object: NodeId,
        method_name: NodeId,
        arguments_list: Vec<NodeId>,
    ) -> NodeId {
        // Preserve the optionality of `object`.
        if ast::is_call_expression(&nodes[object])
            && nodes[object].flags.0 & ast::NodeFlags::OPTIONAL_CHAIN.0 != 0
        {
            let expr = self.inner.new_property_access_expression(
                nodes,
                Some(object),
                None,
                Some(method_name),
                ast::NodeFlags::NONE,
            );
            return self.inner.new_call_expression(
                nodes,
                Some(expr),
                None,
                None,
                Some(self.inner.new_node_list(arguments_list)),
                ast::NodeFlags::OPTIONAL_CHAIN,
            );
        }
        let expr = self.inner.new_property_access_expression(
            nodes,
            Some(object),
            None,
            Some(method_name),
            ast::NodeFlags::NONE,
        );
        self.inner.new_call_expression(
            nodes,
            Some(expr),
            None,
            None,
            Some(self.inner.new_node_list(arguments_list)),
            ast::NodeFlags::NONE,
        )
    }

    /// `NewGlobalMethodCall`
    pub fn new_global_method_call(
        &mut self,
        nodes: &mut Vec<Node>,
        global_object_name: &str,
        method_name: &str,
        arguments_list: Vec<NodeId>,
    ) -> NodeId {
        let object = self.inner.new_identifier(nodes, global_object_name);
        let method = self.inner.new_identifier(nodes, method_name);
        self.new_method_call(nodes, object, method, arguments_list)
    }

    /// `NewFunctionCallCall`
    pub fn new_function_call_call(
        &mut self,
        nodes: &mut Vec<Node>,
        target: NodeId,
        this_arg: Option<NodeId>,
        arguments_list: Vec<NodeId>,
    ) -> NodeId {
        let Some(this_arg) = this_arg else {
            panic!("Attempted to construct function call call without this argument expression")
        };
        let mut args = vec![this_arg];
        args.extend(arguments_list);
        let method = self.inner.new_identifier(nodes, "call");
        self.new_method_call(nodes, target, method, args)
    }

    /// `NewArraySliceCall`
    pub fn new_array_slice_call(
        &mut self,
        nodes: &mut Vec<Node>,
        array: NodeId,
        start: i32,
    ) -> NodeId {
        let mut args = Vec::new();
        if start != 0 {
            args.push(self.inner.new_numeric_literal(
                nodes,
                &start.to_string(),
                ast::TokenFlags::NONE,
            ));
        }
        let method = self.inner.new_identifier(nodes, "slice");
        self.new_method_call(nodes, array, method, args)
    }

    /// `(f *NodeFactory) isIgnorableParen` — determines whether a node is a
    /// parenthesized expression that can be ignored when recreating outer
    /// expressions.
    ///
    /// A parenthesized expression can be ignored when all of the following are true:
    ///
    /// - Its `pos` and `end` are not -1
    /// - It does not have a custom source map range
    /// - It does not have a custom comment range
    /// - It does not have synthetic leading or trailing comments
    ///
    /// If an outermost parenthesized expression is ignored, but the containing expression requires a parentheses around
    /// the expression to maintain precedence, a new parenthesized expression should be created automatically when
    /// the containing expression is created/updated.
    pub(crate) fn is_ignorable_paren(&self, nodes: &[Node], node: NodeId) -> bool {
        if !ast::is_parenthesized_expression(&nodes[node])
            || !ast::node_is_synthesized(&nodes[node])
        {
            return false;
        }
        let mut shared = self.shared.borrow_mut();
        let source_map_range = match shared.emit_nodes.try_get(&node) {
            Some(e) if e.flags & crate::emit_context::HAS_SOURCE_MAP_RANGE != 0 => {
                e.source_map_range
            }
            _ => nodes[node].loc,
        };
        let comment_range = match shared.emit_nodes.try_get(&node) {
            Some(e) if e.flags & crate::emit_context::HAS_COMMENT_RANGE != 0 => e.comment_range,
            _ => nodes[node].loc,
        };
        ast::range_is_synthesized(source_map_range) && ast::range_is_synthesized(comment_range)
        // && len(emitContext.SyntheticLeadingComments(node)) == 0
        // && len(emitContext.SyntheticTrailingComments(node)) == 0
    }

    /// `updateOuterExpression`
    pub(crate) fn update_outer_expression(
        &mut self,
        nodes: &mut Vec<Node>,
        outer_expression: NodeId,
        expression: NodeId,
    ) -> NodeId {
        match nodes[outer_expression].kind {
            Kind::ParenthesizedExpression => self
                .inner
                .update_parenthesized_expression(nodes, outer_expression, Some(expression))
                .unwrap_or(outer_expression),
            Kind::TypeAssertionExpression => {
                let ty = nodes[outer_expression].type_();
                self.inner
                    .update_type_assertion(nodes, outer_expression, ty, Some(expression))
                    .unwrap_or(outer_expression)
            }
            Kind::AsExpression => {
                let ty = nodes[outer_expression].type_();
                self.inner
                    .update_as_expression(nodes, outer_expression, Some(expression), ty)
                    .unwrap_or(outer_expression)
            }
            Kind::SatisfiesExpression => {
                let ty = nodes[outer_expression].type_();
                self.inner
                    .update_satisfies_expression(nodes, outer_expression, Some(expression), ty)
                    .unwrap_or(outer_expression)
            }
            Kind::NonNullExpression => {
                let flags = nodes[outer_expression].flags;
                self.inner
                    .update_non_null_expression(nodes, outer_expression, Some(expression), flags)
                    .unwrap_or(outer_expression)
            }
            Kind::ExpressionWithTypeArguments => {
                let type_arguments = nodes[outer_expression].type_argument_list().cloned();
                self.inner
                    .update_expression_with_type_arguments(
                        nodes,
                        outer_expression,
                        Some(expression),
                        type_arguments,
                    )
                    .unwrap_or(outer_expression)
            }
            Kind::PartiallyEmittedExpression => self
                .inner
                .update_partially_emitted_expression(nodes, outer_expression, Some(expression))
                .unwrap_or(outer_expression),
            kind => panic!("Unexpected outer expression kind: {:?}", kind),
        }
    }

    /// `RestoreOuterExpressions`
    pub fn restore_outer_expressions(
        &mut self,
        nodes: &mut Vec<Node>,
        outer_expression: Option<NodeId>,
        inner_expression: NodeId,
        kinds: ast::OuterExpressionKinds,
    ) -> NodeId {
        if let Some(outer_expression) = outer_expression
            && ast::is_outer_expression(&nodes[outer_expression], kinds, nodes)
            && !self.is_ignorable_paren(nodes, outer_expression)
        {
            let inner = self.restore_outer_expressions(
                nodes,
                nodes[outer_expression].expression(),
                inner_expression,
                ast::outer_expression_kinds::ALL,
            );
            return self.update_outer_expression(nodes, outer_expression, inner);
        }
        inner_expression
    }

    /// `EnsureUseStrict` — ensures `"use strict"` is the first statement of a
    /// slice of statements.
    pub fn ensure_use_strict(
        &mut self,
        nodes: &mut Vec<Node>,
        statements: &[NodeId],
    ) -> Vec<NodeId> {
        for &statement in statements {
            if ast::is_prologue_directive(&nodes[statement], nodes)
                && &*nodes[statement]
                    .expression()
                    .map(|e| nodes[e].text(nodes))
                    .unwrap_or_default()
                    == "use strict"
            {
                return statements.to_vec();
            } else {
                break;
            }
        }
        let use_strict_literal =
            self.inner
                .new_string_literal(nodes, "use strict", ast::TokenFlags::NONE);
        let use_strict_prologue = self
            .inner
            .new_expression_statement(nodes, Some(use_strict_literal));
        let mut result = vec![use_strict_prologue];
        result.extend_from_slice(statements);
        result
    }

    /// `SplitStandardPrologue` — splits a slice of statements into two parts:
    /// standard prologue statements and the rest of the statements.
    pub fn split_standard_prologue<'a>(
        &self,
        nodes: &[Node],
        source: &'a [NodeId],
    ) -> (&'a [NodeId], &'a [NodeId]) {
        for (i, &statement) in source.iter().enumerate() {
            if !ast::is_prologue_directive(&nodes[statement], nodes) {
                return (&source[..i], &source[i..]);
            }
        }
        (source, &[])
    }

    /// `SplitCustomPrologue` — splits a slice of statements into two parts:
    /// custom prologue statements (e.g., with `EFCustomPrologue` set) and the
    /// rest of the statements.
    pub fn split_custom_prologue<'a>(
        &self,
        nodes: &[Node],
        source: &'a [NodeId],
    ) -> (&'a [NodeId], &'a [NodeId]) {
        for (i, &statement) in source.iter().enumerate() {
            if ast::is_prologue_directive(&nodes[statement], nodes)
                || crate::emit_context::emit_flags(&self.shared, statement).0
                    & EmitFlags::CUSTOM_PROLOGUE.0
                    == 0
            {
                return (&source[..i], &source[i..]);
            }
        }
        (&[], source)
    }

    //
    // Declaration Names
    //

    /// `(f *NodeFactory) getName`
    pub(crate) fn get_name(
        &mut self,
        nodes: &mut Vec<Node>,
        node: Option<NodeId>,
        mut emit_flags: EmitFlags,
        opts: AssignedNameOptions,
    ) -> NodeId {
        let node_name = node.and_then(|node| {
            if opts.ignore_assigned_name {
                ast::get_non_assigned_name_of_declaration(node, nodes)
            } else {
                ast::get_name_of_declaration(Some(node), nodes)
            }
        });

        if let Some(node_name) = node_name {
            let name = self.inner.clone_node(nodes, node_name);
            if !opts.allow_comments {
                emit_flags |= EmitFlags::NO_COMMENTS;
            }
            if !opts.allow_source_maps {
                emit_flags |= EmitFlags::NO_SOURCE_MAP;
            }
            crate::emit_context::set_emit_flags_add(&self.shared, name, emit_flags);
            return name;
        }

        match node {
            Some(node) => self.new_generated_name_for_node(nodes, node),
            // PORT: Go would panic on `nil` here only via
            // `NewGeneratedNameForNode(nil)`; `get_name` is only called with a
            // declaration, but keep the `None` arm safe.
            None => self.new_temp_variable(nodes),
        }
    }

    /// `GetLocalName` — gets the local name of a declaration. This is
    /// primarily used for declarations that can be referred to by name in the
    /// declaration's immediate scope (classes, enums, namespaces). A local
    /// name will *never* be prefixed with a module or namespace export
    /// modifier like "exports." when emitted as an expression.
    pub fn get_local_name(&mut self, nodes: &mut Vec<Node>, node: Option<NodeId>) -> NodeId {
        self.get_local_name_ex(nodes, node, &AssignedNameOptions::default())
    }

    /// `GetLocalNameEx`
    pub fn get_local_name_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        node: Option<NodeId>,
        opts: &AssignedNameOptions,
    ) -> NodeId {
        self.get_name(nodes, node, EmitFlags::LOCAL_NAME, *opts)
    }

    /// `GetExportName` — gets the export name of a declaration. This is
    /// primarily used for declarations that can be referred to by name in the
    /// declaration's immediate scope (classes, enums, namespaces). An export
    /// name will *always* be prefixed with an module or namespace export
    /// modifier like `"exports."` when emitted as an expression if the name
    /// points to an exported symbol.
    pub fn get_export_name(&mut self, nodes: &mut Vec<Node>, node: Option<NodeId>) -> NodeId {
        self.get_export_name_ex(nodes, node, &AssignedNameOptions::default())
    }

    /// `GetExportNameEx`
    pub fn get_export_name_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        node: Option<NodeId>,
        opts: &AssignedNameOptions,
    ) -> NodeId {
        self.get_name(nodes, node, EmitFlags::EXPORT_NAME, *opts)
    }

    /// `GetDeclarationName` — gets the name of a declaration to use during
    /// emit.
    pub fn get_declaration_name(&mut self, nodes: &mut Vec<Node>, node: Option<NodeId>) -> NodeId {
        self.get_declaration_name_ex(nodes, node, &NameOptions::default())
    }

    /// `GetDeclarationNameEx`
    pub fn get_declaration_name_ex(
        &mut self,
        nodes: &mut Vec<Node>,
        node: Option<NodeId>,
        opts: &NameOptions,
    ) -> NodeId {
        self.get_name(
            nodes,
            node,
            EmitFlags::NONE,
            AssignedNameOptions {
                allow_comments: opts.allow_comments,
                allow_source_maps: opts.allow_source_maps,
                ..Default::default()
            },
        )
    }

    /// `GetNamespaceMemberName`
    pub fn get_namespace_member_name(
        &mut self,
        nodes: &mut Vec<Node>,
        ns: NodeId,
        mut name: NodeId,
        opts: &NameOptions,
    ) -> NodeId {
        if !self.shared.borrow().auto_generate.contains_key(&name) {
            name = self.inner.clone_node(nodes, name);
        }
        let qualified_name = self.inner.new_property_access_expression(
            nodes,
            Some(ns),
            None, /*questionDotToken*/
            Some(name),
            ast::NodeFlags::NONE,
        );
        // AssignCommentAndSourceMapRanges(qualified_name, name)
        {
            let mut shared = self.shared.borrow_mut();
            let comment_range = match shared.emit_nodes.try_get(&name) {
                Some(e) if e.flags & crate::emit_context::HAS_COMMENT_RANGE != 0 => e.comment_range,
                _ => nodes[name].loc,
            };
            let source_map_range = match shared.emit_nodes.try_get(&name) {
                Some(e) if e.flags & crate::emit_context::HAS_SOURCE_MAP_RANGE != 0 => {
                    e.source_map_range
                }
                _ => nodes[name].loc,
            };
            let emit_node = shared.emit_nodes.get(qualified_name);
            emit_node.comment_range = comment_range;
            emit_node.source_map_range = source_map_range;
            emit_node.flags |=
                crate::emit_context::HAS_COMMENT_RANGE | crate::emit_context::HAS_SOURCE_MAP_RANGE;
        }
        let mut flags = EmitFlags::NONE;
        if !opts.allow_comments {
            flags |= EmitFlags::NO_COMMENTS;
        }
        if !opts.allow_source_maps {
            flags |= EmitFlags::NO_SOURCE_MAP;
        }
        crate::emit_context::set_emit_flags_add(&self.shared, qualified_name, flags);
        qualified_name
    }

    /// `GetExternalModuleOrNamespaceExportName` — gets the export name of a
    /// declaration for use in expressions.
    ///
    /// An export name will *always* be prefixed with a module or namespace
    /// export modifier like `"exports."` when emitted as an expression if the
    /// name points to an exported symbol.
    pub fn get_external_module_or_namespace_export_name(
        &mut self,
        nodes: &mut Vec<Node>,
        ns: Option<NodeId>,
        node: NodeId,
        allow_comments: bool,
        allow_source_maps: bool,
    ) -> NodeId {
        if ns.is_some() && ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::EXPORT) {
            let name_opts = NameOptions {
                allow_comments,
                allow_source_maps,
            };
            let decl_name = self.get_declaration_name_ex(nodes, Some(node), &name_opts);
            return self.get_namespace_member_name(nodes, ns.unwrap(), decl_name, &name_opts);
        }
        self.get_export_name_ex(
            nodes,
            Some(node),
            &AssignedNameOptions {
                allow_comments,
                allow_source_maps,
                ..Default::default()
            },
        )
    }

    //
    // Emit Helpers
    //

    /// `NewUnscopedHelperName` — allocates a new Identifier representing a
    /// reference to a helper function.
    pub fn new_unscoped_helper_name(&mut self, nodes: &mut Vec<Node>, name: &str) -> NodeId {
        let node = self.inner.new_identifier(nodes, name);
        crate::emit_context::set_emit_flags(&self.shared, node, EmitFlags::HELPER_NAME);
        node
    }

    /// `NewCallToHelper`-style shared tail: `helper_name(<args>)`.
    pub(crate) fn new_helper_call(
        &mut self,
        nodes: &mut Vec<Node>,
        helper_name: &str,
        arguments_list: Vec<NodeId>,
    ) -> NodeId {
        let helper = self.new_unscoped_helper_name(nodes, helper_name);
        self.inner.new_call_expression(
            nodes,
            Some(helper),
            None, /*questionDotToken*/
            None, /*typeArguments*/
            Some(self.inner.new_node_list(arguments_list)),
            ast::NodeFlags::NONE,
        )
    }

    // TypeScript Helpers

    /// `NewDecorateHelper`
    pub fn new_decorate_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        decorator_expressions: Vec<NodeId>,
        target: NodeId,
        member_name: Option<NodeId>,
        descriptor: Option<NodeId>,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::decorate_helper());

        let mut arguments_array = Vec::new();
        arguments_array.push(self.inner.new_array_literal_expression(
            nodes,
            Some(self.inner.new_node_list(decorator_expressions)),
            true,
        ));
        arguments_array.push(target);
        if let Some(member_name) = member_name {
            arguments_array.push(member_name);
            if let Some(descriptor) = descriptor {
                arguments_array.push(descriptor);
            }
        }

        self.new_helper_call(nodes, "__decorate", arguments_array)
    }

    /// `NewMetadataHelper`
    pub fn new_metadata_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        metadata_key: &str,
        metadata_value: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::metadata_helper());
        let key = self
            .inner
            .new_string_literal(nodes, metadata_key, ast::TokenFlags::NONE);
        self.new_helper_call(nodes, "__metadata", vec![key, metadata_value])
    }

    /// `NewParamHelper`
    pub fn new_param_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        expression: NodeId,
        parameter_offset: i32,
        location: tsc_core::text::TextRange,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::param_helper());
        let offset = self.inner.new_numeric_literal(
            nodes,
            &parameter_offset.to_string(),
            ast::TokenFlags::NONE,
        );
        let helper = self.new_helper_call(nodes, "__param", vec![offset, expression]);
        nodes[helper].loc = location;
        helper
    }

    // ESNext Helpers

    /// `NewAddDisposableResourceHelper`
    pub fn new_add_disposable_resource_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        env_binding: NodeId,
        value: NodeId,
        is_async: bool,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::add_disposable_resource_helper());
        let flag = self.inner.new_keyword_expression(
            nodes,
            if is_async {
                Kind::TrueKeyword
            } else {
                Kind::FalseKeyword
            },
        );
        self.new_helper_call(
            nodes,
            "__addDisposableResource",
            vec![env_binding, value, flag],
        )
    }

    /// `NewDisposeResourcesHelper`
    pub fn new_dispose_resources_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        env_binding: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::dispose_resources_helper());
        self.new_helper_call(nodes, "__disposeResources", vec![env_binding])
    }

    // Class Fields Helpers

    /// `NewClassPrivateFieldGetHelper`
    pub fn new_class_private_field_get_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        receiver: NodeId,
        state: NodeId,
        kind: PrivateIdentifierKind,
        func: Option<NodeId>,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::class_private_field_get_helper());
        let kind_lit = self
            .inner
            .new_string_literal(nodes, kind.as_str(), ast::TokenFlags::NONE);
        let mut args = vec![receiver, state, kind_lit];
        if let Some(func) = func {
            args.push(func);
        }
        self.new_helper_call(nodes, "__classPrivateFieldGet", args)
    }

    /// `NewClassPrivateFieldSetHelper`
    pub fn new_class_private_field_set_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        receiver: NodeId,
        state: NodeId,
        value: NodeId,
        kind: PrivateIdentifierKind,
        func: Option<NodeId>,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::class_private_field_set_helper());
        let kind_lit = self
            .inner
            .new_string_literal(nodes, kind.as_str(), ast::TokenFlags::NONE);
        let mut args = vec![receiver, state, value, kind_lit];
        if let Some(func) = func {
            args.push(func);
        }
        self.new_helper_call(nodes, "__classPrivateFieldSet", args)
    }

    /// `NewClassPrivateFieldInHelper`
    pub fn new_class_private_field_in_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        state: NodeId,
        receiver: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::class_private_field_in_helper());
        self.new_helper_call(nodes, "__classPrivateFieldIn", vec![state, receiver])
    }

    /// `NewObjectDefinePropertyCall` — creates
    /// `Object.defineProperty(target, name, descriptor)`.
    pub fn new_object_define_property_call(
        &mut self,
        nodes: &mut Vec<Node>,
        target: NodeId,
        name: NodeId,
        descriptor: NodeId,
    ) -> NodeId {
        let object = self.inner.new_identifier(nodes, "Object");
        let method = self.inner.new_identifier(nodes, "defineProperty");
        let callee = self.inner.new_property_access_expression(
            nodes,
            Some(object),
            None,
            Some(method),
            ast::NodeFlags::NONE,
        );
        self.inner.new_call_expression(
            nodes,
            Some(callee),
            None, /*questionDotToken*/
            None, /*typeArguments*/
            Some(self.inner.new_node_list([target, name, descriptor])),
            ast::NodeFlags::NONE,
        )
    }

    /// `NewReflectGetCall` — creates `Reflect.get(target, propertyKey,
    /// receiver)`.
    pub fn new_reflect_get_call(
        &mut self,
        nodes: &mut Vec<Node>,
        target: NodeId,
        property_key: NodeId,
        receiver: NodeId,
    ) -> NodeId {
        let object = self.inner.new_identifier(nodes, "Reflect");
        let method = self.inner.new_identifier(nodes, "get");
        let callee = self.inner.new_property_access_expression(
            nodes,
            Some(object),
            None,
            Some(method),
            ast::NodeFlags::NONE,
        );
        self.inner.new_call_expression(
            nodes,
            Some(callee),
            None, /*questionDotToken*/
            None, /*typeArguments*/
            Some(self.inner.new_node_list([target, property_key, receiver])),
            ast::NodeFlags::NONE,
        )
    }

    /// `NewReflectSetCall` — creates `Reflect.set(target, propertyKey, value,
    /// receiver)`.
    pub fn new_reflect_set_call(
        &mut self,
        nodes: &mut Vec<Node>,
        target: NodeId,
        property_key: NodeId,
        value: NodeId,
        receiver: NodeId,
    ) -> NodeId {
        let object = self.inner.new_identifier(nodes, "Reflect");
        let method = self.inner.new_identifier(nodes, "set");
        let callee = self.inner.new_property_access_expression(
            nodes,
            Some(object),
            None,
            Some(method),
            ast::NodeFlags::NONE,
        );
        self.inner.new_call_expression(
            nodes,
            Some(callee),
            None, /*questionDotToken*/
            None, /*typeArguments*/
            Some(
                self.inner
                    .new_node_list([target, property_key, value, receiver]),
            ),
            ast::NodeFlags::NONE,
        )
    }

    /// `NewFunctionBindCall` — creates `target.bind(thisArg, ...args)`.
    pub fn new_function_bind_call(
        &mut self,
        nodes: &mut Vec<Node>,
        target: NodeId,
        this_arg: NodeId,
        arguments_list: Vec<NodeId>,
    ) -> NodeId {
        let mut args = Vec::with_capacity(1 + arguments_list.len());
        args.push(this_arg);
        args.extend(arguments_list);
        let method = self.inner.new_identifier(nodes, "bind");
        self.new_method_call(nodes, target, method, args)
    }

    /// `NewImmediatelyInvokedArrowFunction` — creates
    /// `(() => { ...statements })()` — an immediately invoked arrow function.
    pub fn new_immediately_invoked_arrow_function(
        &mut self,
        nodes: &mut Vec<Node>,
        statements: Vec<NodeId>,
    ) -> NodeId {
        let parameters = self.inner.new_node_list(Vec::<NodeId>::new());
        let eq_gt = self.inner.new_token(nodes, Kind::EqualsGreaterThanToken);
        let body_stmts = self.inner.new_node_list(statements);
        let block = self.inner.new_block(nodes, Some(body_stmts), true);
        let arrow = self.inner.new_arrow_function(
            nodes,
            None, /*modifiers*/
            None, /*typeParameters*/
            Some(parameters),
            None, /*returnType*/
            None, /*fullSignature*/
            Some(eq_gt),
            Some(block),
        );
        let parens = self.inner.new_parenthesized_expression(nodes, Some(arrow));
        self.inner.new_call_expression(
            nodes,
            Some(parens),
            None, /*questionDotToken*/
            None, /*typeArguments*/
            Some(self.inner.new_node_list(Vec::<NodeId>::new())),
            ast::NodeFlags::NONE,
        )
    }

    /// `NewExportDefault` — creates `export default <expression>;`.
    pub fn new_export_default(&mut self, nodes: &mut Vec<Node>, expression: NodeId) -> NodeId {
        self.inner
            .new_export_assignment(nodes, None, false, None, Some(expression))
    }

    /// `NewExternalModuleExport` — creates `export { <name> };`.
    pub fn new_external_module_export(&mut self, nodes: &mut Vec<Node>, name: NodeId) -> NodeId {
        let specifier = self
            .inner
            .new_export_specifier(nodes, false, None, Some(name));
        let named_exports = self
            .inner
            .new_named_exports(nodes, Some(self.inner.new_node_list([specifier])));
        self.inner
            .new_export_declaration(nodes, None, false, Some(named_exports), None, None)
    }

    // ES2018 Helpers

    /// `NewAssignHelper` — chains a sequence of expressions using the
    /// `__assign` helper or `Object.assign` if available in the target.
    pub fn new_assign_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        attributes_segments: Vec<NodeId>,
        _script_target: tsc_core::options_generated::ScriptTarget,
    ) -> NodeId {
        let object = self.inner.new_identifier(nodes, "Object");
        let method = self.inner.new_identifier(nodes, "assign");
        let callee = self.inner.new_property_access_expression(
            nodes,
            Some(object),
            None,
            Some(method),
            ast::NodeFlags::NONE,
        );
        self.inner.new_call_expression(
            nodes,
            Some(callee),
            None,
            None,
            Some(self.inner.new_node_list(attributes_segments)),
            ast::NodeFlags::NONE,
        )
    }

    // ES2018 Destructuring Helpers

    /// `NewRestHelper`
    pub fn new_rest_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        value: NodeId,
        elements: &[NodeId],
        computed_temp_variables: Option<&[NodeId]>,
        location: tsc_core::text::TextRange,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::rest_helper());
        let mut property_names = Vec::new();
        let mut computed_temp_variable_offset = 0usize;
        for (i, &element) in elements.iter().enumerate() {
            if i == elements.len() - 1 {
                break;
            }
            let property_name =
                ast::try_get_property_name_of_binding_or_assignment_element(element, nodes);
            if let Some(property_name) = property_name {
                if ast::is_computed_property_name(&nodes[property_name]) {
                    let computed_temp_variables = computed_temp_variables.expect(
                        "Encountered computed property name but 'computedTempVariables' argument was not provided.",
                    );
                    let temp = computed_temp_variables[computed_temp_variable_offset];
                    computed_temp_variable_offset += 1;
                    // typeof _tmp === "symbol" ? _tmp : _tmp + ""
                    let type_check = self.new_type_check(nodes, temp, "symbol");
                    let plus = self.inner.new_token(nodes, Kind::PlusToken);
                    let empty_string =
                        self.inner
                            .new_string_literal(nodes, "", ast::TokenFlags::NONE);
                    let concat = self.inner.new_binary_expression(
                        nodes,
                        None,
                        Some(temp),
                        None,
                        Some(plus),
                        Some(empty_string),
                    );
                    let question_token = self.inner.new_token(nodes, Kind::QuestionToken);
                    let colon_token = self.inner.new_token(nodes, Kind::ColonToken);
                    property_names.push(self.inner.new_conditional_expression(
                        nodes,
                        Some(type_check),
                        Some(question_token),
                        Some(temp),
                        Some(colon_token),
                        Some(concat),
                    ));
                } else {
                    property_names.push(self.new_string_literal_from_node(nodes, property_name));
                }
            }
        }
        let prop_names = self.inner.new_array_literal_expression(
            nodes,
            Some(self.inner.new_node_list(property_names)),
            false,
        );
        nodes[prop_names].loc = location;
        self.new_helper_call(nodes, "__rest", vec![value, prop_names])
    }

    // ES2018 Helpers

    /// `NewAwaitHelper` — allocates a new Call expression to the `__await`
    /// helper.
    pub fn new_await_helper(&mut self, nodes: &mut Vec<Node>, expression: NodeId) -> NodeId {
        self.request_emit_helper(&emit_helpers::await_helper());
        self.new_helper_call(nodes, "__await", vec![expression])
    }

    /// `NewAsyncGeneratorHelper` — allocates a new Call expression to the
    /// `__asyncGenerator` helper.
    pub fn new_async_generator_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        generator_func: NodeId,
        has_lexical_this: bool,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::await_helper());
        self.request_emit_helper(&emit_helpers::async_generator_helper());

        // Mark this node as originally an async function body
        crate::emit_context::set_emit_flags_add(
            &self.shared,
            generator_func,
            EmitFlags::ASYNC_FUNCTION_BODY | EmitFlags::REUSE_TEMP_VARIABLE_SCOPE,
        );

        let this_arg = if has_lexical_this {
            self.inner.new_keyword_expression(nodes, Kind::ThisKeyword)
        } else {
            self.new_void_zero_expression(nodes)
        };

        let arguments_id = self.inner.new_identifier(nodes, "arguments");
        self.new_helper_call(
            nodes,
            "__asyncGenerator",
            vec![this_arg, arguments_id, generator_func],
        )
    }

    /// `NewAsyncDelegatorHelper` — allocates a new Call expression to the
    /// `__asyncDelegator` helper.
    pub fn new_async_delegator_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        expression: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::await_helper());
        self.request_emit_helper(&emit_helpers::async_delegator_helper());
        self.new_helper_call(nodes, "__asyncDelegator", vec![expression])
    }

    /// `NewAsyncValuesHelper` — allocates a new Call expression to the
    /// `__asyncValues` helper.
    pub fn new_async_values_helper(&mut self, nodes: &mut Vec<Node>, expression: NodeId) -> NodeId {
        self.request_emit_helper(&emit_helpers::async_values_helper());
        self.new_helper_call(nodes, "__asyncValues", vec![expression])
    }

    // !!! ES2017 Helpers

    /// `NewAwaiterHelper` — allocates a new Call expression to the `__awaiter`
    /// helper.
    pub fn new_awaiter_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        has_lexical_this: bool,
        arguments_expression: Option<NodeId>,
        parameters: Option<NodeList>,
        body: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::awaiter_helper());

        let params = match parameters {
            Some(params) => params,
            None => self.inner.new_node_list(Vec::<NodeId>::new()),
        };

        let asterisk = self.inner.new_token(nodes, Kind::AsteriskToken);
        let generator_func = self.inner.new_function_expression(
            nodes,
            None, /*modifiers*/
            Some(asterisk),
            None, /*name*/
            None, /*typeParameters*/
            Some(params),
            None, /*returnType*/
            None, /*fullSignature*/
            Some(body),
        );

        // Mark this node as originally an async function body
        crate::emit_context::set_emit_flags_add(
            &self.shared,
            generator_func,
            EmitFlags::ASYNC_FUNCTION_BODY | EmitFlags::REUSE_TEMP_VARIABLE_SCOPE,
        );

        let this_arg = if has_lexical_this {
            self.inner.new_keyword_expression(nodes, Kind::ThisKeyword)
        } else {
            self.new_void_zero_expression(nodes)
        };

        let args_arg = match arguments_expression {
            Some(args) => args,
            None => self.new_void_zero_expression(nodes),
        };

        let void_zero = self.new_void_zero_expression(nodes);
        self.new_helper_call(
            nodes,
            "__awaiter",
            vec![this_arg, args_arg, void_zero, generator_func],
        )
    }

    // ES Decorator Helpers

    /// `NewESDecorateClassContextObject`
    pub fn new_es_decorate_class_context_object(
        &mut self,
        nodes: &mut Vec<Node>,
        name_expr: NodeId,
        metadata: NodeId,
    ) -> NodeId {
        let kind_id = self.inner.new_identifier(nodes, "kind");
        let kind_lit = self
            .inner
            .new_string_literal(nodes, "class", ast::TokenFlags::NONE);
        let name_id = self.inner.new_identifier(nodes, "name");
        let metadata_id = self.inner.new_identifier(nodes, "metadata");
        let props = vec![
            self.inner.new_property_assignment(
                nodes,
                None,
                Some(kind_id),
                None,
                None,
                Some(kind_lit),
            ),
            self.inner.new_property_assignment(
                nodes,
                None,
                Some(name_id),
                None,
                None,
                Some(name_expr),
            ),
            self.inner.new_property_assignment(
                nodes,
                None,
                Some(metadata_id),
                None,
                None,
                Some(metadata),
            ),
        ];
        self.inner.new_object_literal_expression(
            nodes,
            Some(self.inner.new_node_list(props)),
            false,
        )
    }

    /// `NewESDecorateClassElementAccessGetMethod`
    pub fn new_es_decorate_class_element_access_get_method(
        &mut self,
        nodes: &mut Vec<Node>,
        name_computed: bool,
        name_expr: NodeId,
    ) -> NodeId {
        let obj = self.inner.new_identifier(nodes, "obj");
        let accessor = if name_computed {
            self.inner.new_element_access_expression(
                nodes,
                Some(obj),
                None,
                Some(name_expr),
                ast::NodeFlags::NONE,
            )
        } else {
            self.inner.new_property_access_expression(
                nodes,
                Some(obj),
                None,
                Some(name_expr),
                ast::NodeFlags::NONE,
            )
        };

        let obj_name = self.inner.new_identifier(nodes, "obj");
        let obj_param = self.inner.new_parameter_declaration(
            nodes,
            None,
            None,
            Some(obj_name),
            None,
            None,
            None,
        );

        let params = self.inner.new_node_list([obj_param]);
        let eq_gt = self.inner.new_token(nodes, Kind::EqualsGreaterThanToken);
        let arrow = self.inner.new_arrow_function(
            nodes,
            None,
            None,
            Some(params),
            None,
            None,
            Some(eq_gt),
            Some(accessor),
        );

        let get_id = self.inner.new_identifier(nodes, "get");
        self.inner
            .new_property_assignment(nodes, None, Some(get_id), None, None, Some(arrow))
    }

    /// `NewESDecorateClassElementAccessSetMethod`
    pub fn new_es_decorate_class_element_access_set_method(
        &mut self,
        nodes: &mut Vec<Node>,
        name_computed: bool,
        name_expr: NodeId,
    ) -> NodeId {
        let obj = self.inner.new_identifier(nodes, "obj");
        let accessor = if name_computed {
            self.inner.new_element_access_expression(
                nodes,
                Some(obj),
                None,
                Some(name_expr),
                ast::NodeFlags::NONE,
            )
        } else {
            self.inner.new_property_access_expression(
                nodes,
                Some(obj),
                None,
                Some(name_expr),
                ast::NodeFlags::NONE,
            )
        };

        let value_id = self.inner.new_identifier(nodes, "value");
        let assignment = self.new_assignment_expression(nodes, accessor, value_id);
        let stmt = self.inner.new_expression_statement(nodes, Some(assignment));
        let body = self
            .inner
            .new_block(nodes, Some(self.inner.new_node_list([stmt])), false);

        let obj_name = self.inner.new_identifier(nodes, "obj");
        let obj_param = self.inner.new_parameter_declaration(
            nodes,
            None,
            None,
            Some(obj_name),
            None,
            None,
            None,
        );
        let value_name = self.inner.new_identifier(nodes, "value");
        let value_param = self.inner.new_parameter_declaration(
            nodes,
            None,
            None,
            Some(value_name),
            None,
            None,
            None,
        );

        let params = self.inner.new_node_list([obj_param, value_param]);
        let eq_gt = self.inner.new_token(nodes, Kind::EqualsGreaterThanToken);
        let arrow = self.inner.new_arrow_function(
            nodes,
            None,
            None,
            Some(params),
            None,
            None,
            Some(eq_gt),
            Some(body),
        );

        let set_id = self.inner.new_identifier(nodes, "set");
        self.inner
            .new_property_assignment(nodes, None, Some(set_id), None, None, Some(arrow))
    }

    /// `NewESDecorateClassElementAccessHasMethod`
    pub fn new_es_decorate_class_element_access_has_method(
        &mut self,
        nodes: &mut Vec<Node>,
        name_computed: bool,
        name_expr: Option<NodeId>,
    ) -> NodeId {
        // The property name for the "in" expression
        let property_name = if !name_computed
            && let Some(name_expr) = name_expr
            && ast::is_identifier(&nodes[name_expr])
        {
            Some(self.new_string_literal_from_node(nodes, name_expr))
        } else {
            name_expr
        };

        let obj_name = self.inner.new_identifier(nodes, "obj");
        let obj_param = self.inner.new_parameter_declaration(
            nodes,
            None,
            None,
            Some(obj_name),
            None,
            None,
            None,
        );
        let in_token = self.inner.new_token(nodes, Kind::InKeyword);
        let obj_id = self.inner.new_identifier(nodes, "obj");
        let in_expr = self.inner.new_binary_expression(
            nodes,
            None,
            property_name,
            None,
            Some(in_token),
            Some(obj_id),
        );

        let params = self.inner.new_node_list([obj_param]);
        let eq_gt = self.inner.new_token(nodes, Kind::EqualsGreaterThanToken);
        let arrow = self.inner.new_arrow_function(
            nodes,
            None,
            None,
            Some(params),
            None,
            None,
            Some(eq_gt),
            Some(in_expr),
        );

        let has_id = self.inner.new_identifier(nodes, "has");
        self.inner
            .new_property_assignment(nodes, None, Some(has_id), None, None, Some(arrow))
    }

    /// `NewESDecorateClassElementAccessObject` — creates the "access" object
    /// for a class element decorator context.
    ///
    /// 15.7.3 CreateDecoratorAccessObject (kind, name)
    ///
    ///  2. If _kind_ is ~field~, ~method~, ~accessor~, or ~getter~, then
    ///     a. Let _getAccess_ be a new Abstract Closure with parameters (_object_) that captures _kind_ and _name_ ...
    ///     b. Perform ! CreateDataPropertyOrThrow(_access_, "get", _getAccess_).
    ///  3. If _kind_ is ~field~, ~accessor_, or ~setter~, then
    ///     a. Let _setAccess_ be a new Abstract Closure with parameters (_object_, _value_) that captures _kind_ and _name_ ...
    ///     b. Perform ! CreateDataPropertyOrThrow(_access_, "set", _setAccess_).
    pub fn new_es_decorate_class_element_access_object(
        &mut self,
        nodes: &mut Vec<Node>,
        name_computed: bool,
        name_expr: Option<NodeId>,
        has_get: bool,
        has_set: bool,
    ) -> NodeId {
        let mut access_props = Vec::new();

        // "has" method: obj => name in obj
        access_props.push(self.new_es_decorate_class_element_access_has_method(
            nodes,
            name_computed,
            name_expr,
        ));

        // "get" method: obj => obj.name or obj => obj[name]
        if has_get {
            access_props.push(self.new_es_decorate_class_element_access_get_method(
                nodes,
                name_computed,
                name_expr.unwrap(),
            ));
        }

        // "set" method: (obj, value) => { obj.name = value; } or (obj, value) => { obj[name] = value; }
        if has_set {
            access_props.push(self.new_es_decorate_class_element_access_set_method(
                nodes,
                name_computed,
                name_expr.unwrap(),
            ));
        }

        self.inner.new_object_literal_expression(
            nodes,
            Some(self.inner.new_node_list(access_props)),
            false,
        )
    }

    /// `NewESDecorateClassElementContextObject`
    #[allow(clippy::too_many_arguments)]
    pub fn new_es_decorate_class_element_context_object(
        &mut self,
        nodes: &mut Vec<Node>,
        kind: &str,
        name_computed: bool,
        name_expr: Option<NodeId>,
        is_static: bool,
        is_private: bool,
        has_get: bool,
        has_set: bool,
        metadata: NodeId,
    ) -> NodeId {
        // Build the name value for the context's "name" property
        let name_value = if !name_computed
            && let Some(name_expr) = name_expr
            && (ast::is_private_identifier(&nodes[name_expr])
                || ast::is_identifier(&nodes[name_expr]))
        {
            Some(self.new_string_literal_from_node(nodes, name_expr))
        } else {
            name_expr
        };

        // Build the access object with has/get/set arrow functions
        let access_obj = self.new_es_decorate_class_element_access_object(
            nodes,
            name_computed,
            name_expr,
            has_get,
            has_set,
        );

        let static_expr = if is_static {
            self.new_true_expression(nodes)
        } else {
            self.new_false_expression(nodes)
        };

        let private_expr = if is_private {
            self.new_true_expression(nodes)
        } else {
            self.new_false_expression(nodes)
        };

        let kind_id = self.inner.new_identifier(nodes, "kind");
        let kind_lit = self
            .inner
            .new_string_literal(nodes, kind, ast::TokenFlags::NONE);
        let name_id = self.inner.new_identifier(nodes, "name");
        let static_id = self.inner.new_identifier(nodes, "static");
        let private_id = self.inner.new_identifier(nodes, "private");
        let access_id = self.inner.new_identifier(nodes, "access");
        let metadata_id = self.inner.new_identifier(nodes, "metadata");
        let props = vec![
            self.inner.new_property_assignment(
                nodes,
                None,
                Some(kind_id),
                None,
                None,
                Some(kind_lit),
            ),
            self.inner
                .new_property_assignment(nodes, None, Some(name_id), None, None, name_value),
            self.inner.new_property_assignment(
                nodes,
                None,
                Some(static_id),
                None,
                None,
                Some(static_expr),
            ),
            self.inner.new_property_assignment(
                nodes,
                None,
                Some(private_id),
                None,
                None,
                Some(private_expr),
            ),
            self.inner.new_property_assignment(
                nodes,
                None,
                Some(access_id),
                None,
                None,
                Some(access_obj),
            ),
            self.inner.new_property_assignment(
                nodes,
                None,
                Some(metadata_id),
                None,
                None,
                Some(metadata),
            ),
        ];
        self.inner.new_object_literal_expression(
            nodes,
            Some(self.inner.new_node_list(props)),
            false,
        )
    }

    /// `NewESDecorateHelper`
    #[allow(clippy::too_many_arguments)]
    pub fn new_es_decorate_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        ctor: NodeId,
        descriptor_in: NodeId,
        decorators: NodeId,
        context_in: NodeId,
        initializers: NodeId,
        extra_initializers: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::es_decorate_helper());
        self.new_helper_call(
            nodes,
            "__esDecorate",
            vec![
                ctor,
                descriptor_in,
                decorators,
                context_in,
                initializers,
                extra_initializers,
            ],
        )
    }

    /// `NewRunInitializersHelper`
    pub fn new_run_initializers_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        this_arg: NodeId,
        initializers: NodeId,
        value: Option<NodeId>,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::run_initializers_helper());
        let arguments = match value {
            Some(value) => vec![this_arg, initializers, value],
            None => vec![this_arg, initializers],
        };
        self.new_helper_call(nodes, "__runInitializers", arguments)
    }

    // ES2015 Helpers

    /// `NewTemplateObjectHelper`
    pub fn new_template_object_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        cooked_array: NodeId,
        raw_array: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::make_template_object_helper());
        self.new_helper_call(nodes, "__makeTemplateObject", vec![cooked_array, raw_array])
    }

    /// `NewPropKeyHelper`
    pub fn new_prop_key_helper(&mut self, nodes: &mut Vec<Node>, expr: NodeId) -> NodeId {
        self.request_emit_helper(&emit_helpers::prop_key_helper());
        self.new_helper_call(nodes, "__propKey", vec![expr])
    }

    /// `NewSetFunctionNameHelper`
    pub fn new_set_function_name_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        func: NodeId,
        name: NodeId,
        prefix: &str,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::set_function_name_helper());
        let arguments = if !prefix.is_empty() {
            let prefix_lit = self
                .inner
                .new_string_literal(nodes, prefix, ast::TokenFlags::NONE);
            vec![func, name, prefix_lit]
        } else {
            vec![func, name]
        };
        self.new_helper_call(nodes, "__setFunctionName", arguments)
    }

    // ES Module Helpers

    /// `NewImportDefaultHelper` — allocates a new Call expression to the
    /// `__importDefault` helper.
    pub fn new_import_default_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        expression: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::import_default_helper());
        self.new_helper_call(nodes, "__importDefault", vec![expression])
    }

    /// `NewImportStarHelper` — allocates a new Call expression to the
    /// `__importStar` helper.
    pub fn new_import_star_helper(&mut self, nodes: &mut Vec<Node>, expression: NodeId) -> NodeId {
        self.request_emit_helper(&emit_helpers::import_star_helper());
        self.new_helper_call(nodes, "__importStar", vec![expression])
    }

    /// `NewExportStarHelper` — allocates a new Call expression to the
    /// `__exportStar` helper.
    pub fn new_export_star_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        module_expression: NodeId,
        exports_expression: NodeId,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::export_star_helper());
        self.new_helper_call(
            nodes,
            "__exportStar",
            vec![module_expression, exports_expression],
        )
    }

    /// `NewAssignmentTargetWrapper`
    pub fn new_assignment_target_wrapper(
        &mut self,
        nodes: &mut Vec<Node>,
        param_name: NodeId,
        expression: NodeId,
    ) -> NodeId {
        let value_id = self.inner.new_identifier(nodes, "value");
        let param = self.inner.new_parameter_declaration(
            nodes,
            None,
            None,
            Some(param_name),
            None,
            None,
            None,
        );
        let params = self.inner.new_node_list([param]);
        let stmt = self.inner.new_expression_statement(nodes, Some(expression));
        let body = self
            .inner
            .new_block(nodes, Some(self.inner.new_node_list([stmt])), false);
        let set_accessor = self.inner.new_set_accessor_declaration(
            nodes,
            None, /*modifiers*/
            Some(value_id),
            None, /*typeParameters*/
            Some(params),
            None, /*returnType*/
            None, /*fullSignature*/
            Some(body),
        );
        let obj_literal = self.inner.new_object_literal_expression(
            nodes,
            Some(self.inner.new_node_list([set_accessor])),
            false,
        );
        let parens = self
            .inner
            .new_parenthesized_expression(nodes, Some(obj_literal));
        let value_id2 = self.inner.new_identifier(nodes, "value");
        // Explicit parens required because of v8 regression (https://bugs.chromium.org/p/v8/issues/detail?id=9560)
        self.inner.new_property_access_expression(
            nodes,
            Some(parens),
            None, /*questionDotToken*/
            Some(value_id2),
            ast::NodeFlags::NONE,
        )
    }

    /// `NewRewriteRelativeImportExtensionsHelper` — allocates a new Call
    /// expression to the `__rewriteRelativeImportExtension` helper.
    pub fn new_rewrite_relative_import_extensions_helper(
        &mut self,
        nodes: &mut Vec<Node>,
        first_argument: NodeId,
        preserve_jsx: bool,
    ) -> NodeId {
        self.request_emit_helper(&emit_helpers::rewrite_relative_import_extensions_helper());
        let mut arguments = vec![first_argument];
        if preserve_jsx {
            arguments.push(self.inner.new_token(nodes, Kind::TrueKeyword));
        }
        self.new_helper_call(nodes, "__rewriteRelativeImportExtension", arguments)
    }

    /// `f.emitContext.RequestEmitHelper(helper)` via the shared tables.
    pub(crate) fn request_emit_helper(&mut self, helper: &Arc<EmitHelper>) {
        if helper.scoped {
            panic!("Cannot request a scoped emit helper");
        }
        for h in &helper.dependencies {
            self.request_emit_helper(h);
        }
        self.shared
            .borrow_mut()
            .emit_helpers
            .add(emit_helpers::EmitHelperRef(helper.clone()));
    }
}

/// `type PrivateIdentifierKind string`
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PrivateIdentifierKind {
    /// `PrivateIdentifierKindField` — `"f"`
    Field,
    /// `PrivateIdentifierKindMethod` — `"m"`
    Method,
    /// `PrivateIdentifierKindAccessor` — `"a"`
    Accessor,
    /// `PrivateIdentifierKindUntransformed` — `"untransformed"`
    Untransformed,
}

impl PrivateIdentifierKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            PrivateIdentifierKind::Field => "f",
            PrivateIdentifierKind::Method => "m",
            PrivateIdentifierKind::Accessor => "a",
            PrivateIdentifierKind::Untransformed => "untransformed",
        }
    }
}

/// `type NameOptions struct`
#[derive(Clone, Copy, Default)]
pub struct NameOptions {
    /// indicates whether comments may be emitted for the name.
    pub allow_comments: bool,
    /// indicates whether source maps may be emitted for the name.
    pub allow_source_maps: bool,
}

/// `type AssignedNameOptions struct`
#[derive(Clone, Copy, Default)]
pub struct AssignedNameOptions {
    /// indicates whether comments may be emitted for the name.
    pub allow_comments: bool,
    /// indicates whether source maps may be emitted for the name.
    pub allow_source_maps: bool,
    /// indicates whether the assigned name of a declaration shouldn't be considered.
    pub ignore_assigned_name: bool,
}

/// `FormatGeneratedName`
pub fn format_generated_name(private_name: bool, prefix: &str, name: &str, suffix: &str) -> String {
    let mut formatted = String::with_capacity(prefix.len() + name.len() + suffix.len() + 2);
    if private_name {
        formatted.push('#');
    }
    formatted.push_str(prefix);
    formatted.push_str(name);
    formatted.push_str(suffix);
    formatted
}

/// `(f *NodeFactory) newGeneratedIdentifier` — implemented as a free function
/// so `EmitContext`'s visitor hooks (which drive `cx.factory` directly) can
/// share it.
pub(crate) fn new_generated_identifier(
    shared: &Shared,
    factory: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<Node>,
    kind: GeneratedIdentifierFlags,
    text: &str,
    node: Option<NodeId>,
    options: &AutoGenerateOptions,
) -> NodeId {
    let id: AutoGenerateId = next_auto_generate_id();

    let text = if text.is_empty() {
        let text = match node {
            None => format!("(auto@{})", id),
            Some(node) if ast::is_member_name(&nodes[node]) => nodes[node].text(nodes).into_owned(),
            Some(node) => {
                let worker_node = crate::emit_context::get_node_for_generated_name_worker(
                    shared, nodes, node, id,
                );
                format!("(generated@{:?})", ast::get_node_id(&nodes[worker_node]))
            }
        };
        format_generated_name(
            false, /*privateName*/
            &options.prefix,
            &text,
            &options.suffix,
        )
    } else {
        text.to_string()
    };

    let name = factory.new_identifier(nodes, &text);
    let auto_generate = AutoGenerateInfo {
        id,
        flags: kind | (options.flags & !GeneratedIdentifierFlags::KIND_MASK),
        prefix: options.prefix.clone(),
        suffix: options.suffix.clone(),
        node,
    };
    shared
        .borrow_mut()
        .auto_generate
        .insert(name, auto_generate);
    name
}

/// `(f *NodeFactory) newGeneratedPrivateIdentifier`
pub(crate) fn new_generated_private_identifier(
    shared: &Shared,
    factory: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<Node>,
    kind: GeneratedIdentifierFlags,
    text: &str,
    node: Option<NodeId>,
    options: &AutoGenerateOptions,
) -> NodeId {
    let id: AutoGenerateId = next_auto_generate_id();

    let text = if text.is_empty() {
        let text = match node {
            None => format!("(auto@{})", id),
            Some(node) if ast::is_member_name(&nodes[node]) => nodes[node].text(nodes).into_owned(),
            Some(node) => {
                let worker_node = crate::emit_context::get_node_for_generated_name_worker(
                    shared, nodes, node, id,
                );
                format!("(generated@{:?})", ast::get_node_id(&nodes[worker_node]))
            }
        };
        format_generated_name(
            true, /*privateName*/
            &options.prefix,
            &text,
            &options.suffix,
        )
    } else if !text.starts_with('#') {
        panic!("First character of private identifier must be #: {}", text)
    } else {
        text.to_string()
    };

    let name = factory.new_private_identifier(nodes, &text);
    let auto_generate = AutoGenerateInfo {
        id,
        flags: kind | (options.flags & !GeneratedIdentifierFlags::KIND_MASK),
        prefix: options.prefix.clone(),
        suffix: options.suffix.clone(),
        node,
    };
    shared
        .borrow_mut()
        .auto_generate
        .insert(name, auto_generate);
    name
}

/// `flattenCommaElement`
fn flatten_comma_element(nodes: &[Node], node: NodeId, expressions: &mut Vec<NodeId>) {
    if ast::is_binary_expression(&nodes[node])
        && ast::node_is_synthesized(&nodes[node])
        && nodes[node]
            .as_binary_expression()
            .operator_token
            .is_some_and(|t| nodes[t].kind == Kind::CommaToken)
    {
        let d = nodes[node].as_binary_expression();
        let (left, right) = (d.left, d.right);
        flatten_comma_element(nodes, left.unwrap(), expressions);
        flatten_comma_element(nodes, right.unwrap(), expressions);
    } else {
        expressions.push(node);
    }
}

/// `flattenCommaElements`
fn flatten_comma_elements(nodes: &[Node], expressions: &[NodeId]) -> Vec<NodeId> {
    let mut result = Vec::new();
    for &expression in expressions {
        flatten_comma_element(nodes, expression, &mut result);
    }
    result
}

/// `(f *NodeFactory) NewBinaryExpression(nil, left, nil, f.NewToken(kind), right)`
/// — free function shared with `EmitContext` hooks.
pub(crate) fn new_binary_operator_expression(
    factory: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<Node>,
    kind: Kind,
    left: NodeId,
    right: NodeId,
) -> NodeId {
    let op = factory.new_token(nodes, kind);
    factory.new_binary_expression(
        nodes,
        None, /*modifiers*/
        Some(left),
        None, /*typeNode*/
        Some(op),
        Some(right),
    )
}

/// `NewVoidZeroExpression`
pub(crate) fn new_void_zero_expression(
    factory: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<Node>,
) -> NodeId {
    let zero = factory.new_numeric_literal(nodes, "0", ast::TokenFlags::NONE);
    factory.new_void_expression(nodes, Some(zero))
}

/// `NewTypeCheck`
pub(crate) fn new_type_check(
    factory: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<Node>,
    value: NodeId,
    tag: &str,
) -> NodeId {
    if tag == "null" {
        let null = factory.new_keyword_expression(nodes, Kind::NullKeyword);
        new_binary_operator_expression(factory, nodes, Kind::EqualsEqualsEqualsToken, value, null)
    } else if tag == "undefined" {
        let void_zero = new_void_zero_expression(factory, nodes);
        new_binary_operator_expression(
            factory,
            nodes,
            Kind::EqualsEqualsEqualsToken,
            value,
            void_zero,
        )
    } else {
        let type_of = factory.new_type_of_expression(nodes, Some(value));
        let tag_lit = factory.new_string_literal(nodes, tag, ast::TokenFlags::NONE);
        new_binary_operator_expression(
            factory,
            nodes,
            Kind::EqualsEqualsEqualsToken,
            type_of,
            tag_lit,
        )
    }
}
