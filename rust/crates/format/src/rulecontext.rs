// Ported from tsc/internal/format/rulecontext.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_astnav::tokens::find_next_token;
use tsc_core::tristate::Tristate;
use tsc_lsutil::{
    FormatCodeSettings, SemicolonPreference, get_first_token, position_is_asi_candidate,
};
use tsc_scanner::scanner::get_token_pos_of_node;

use crate::api::FormatRequestKind;
use crate::context::FormattingContext;
use crate::rule::ContextPredicate;
use crate::scanner::TextRangeWithKind;
use crate::util::line_of_position;

///
/// Contexts
///

/// Lifts a bare predicate fn into a `ContextPredicate` — Go stores plain
/// funcs and closures uniformly in `[]contextPredicate`.
pub(crate) fn pred(f: fn(&mut FormattingContext, &mut Vec<Node>) -> bool) -> ContextPredicate {
    Box::new(f)
}

/// `type optionSelector = func(options lsutil.FormatCodeSettings) core.Tristate`
pub(crate) type OptionSelector = fn(&FormatCodeSettings) -> Tristate;

/// `semicolonOption`
pub(crate) fn semicolon_option(options: &FormatCodeSettings) -> SemicolonPreference {
    options.semicolons.clone()
}

/// `insertSpaceAfterCommaDelimiterOption`
pub(crate) fn insert_space_after_comma_delimiter_option(options: &FormatCodeSettings) -> Tristate {
    options.insert_space_after_comma_delimiter
}

/// `insertSpaceAfterSemicolonInForStatementsOption`
pub(crate) fn insert_space_after_semicolon_in_for_statements_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_semicolon_in_for_statements
}

/// `insertSpaceBeforeAndAfterBinaryOperatorsOption`
pub(crate) fn insert_space_before_and_after_binary_operators_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_before_and_after_binary_operators
}

/// `insertSpaceAfterConstructorOption`
pub(crate) fn insert_space_after_constructor_option(options: &FormatCodeSettings) -> Tristate {
    options.insert_space_after_constructor
}

/// `insertSpaceAfterKeywordsInControlFlowStatementsOption`
pub(crate) fn insert_space_after_keywords_in_control_flow_statements_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_keywords_in_control_flow_statements
}

/// `insertSpaceAfterFunctionKeywordForAnonymousFunctionsOption`
pub(crate) fn insert_space_after_function_keyword_for_anonymous_functions_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_function_keyword_for_anonymous_functions
}

/// `insertSpaceAfterOpeningAndBeforeClosingNonemptyParenthesisOption`
pub(crate) fn insert_space_after_opening_and_before_closing_nonempty_parenthesis_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_opening_and_before_closing_nonempty_parenthesis
}

/// `insertSpaceAfterOpeningAndBeforeClosingNonemptyBracketsOption`
pub(crate) fn insert_space_after_opening_and_before_closing_nonempty_brackets_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_opening_and_before_closing_nonempty_brackets
}

/// `insertSpaceAfterOpeningAndBeforeClosingNonemptyBracesOption`
pub(crate) fn insert_space_after_opening_and_before_closing_nonempty_braces_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_opening_and_before_closing_nonempty_braces
}

/// `insertSpaceAfterOpeningAndBeforeClosingEmptyBracesOption`
pub(crate) fn insert_space_after_opening_and_before_closing_empty_braces_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_opening_and_before_closing_empty_braces
}

/// `insertSpaceAfterOpeningAndBeforeClosingTemplateStringBracesOption`
pub(crate) fn insert_space_after_opening_and_before_closing_template_string_braces_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_opening_and_before_closing_template_string_braces
}

/// `insertSpaceAfterOpeningAndBeforeClosingJsxExpressionBracesOption`
pub(crate) fn insert_space_after_opening_and_before_closing_jsx_expression_braces_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_after_opening_and_before_closing_jsx_expression_braces
}

/// `insertSpaceAfterTypeAssertionOption`
pub(crate) fn insert_space_after_type_assertion_option(options: &FormatCodeSettings) -> Tristate {
    options.insert_space_after_type_assertion
}

/// `insertSpaceBeforeFunctionParenthesisOption`
pub(crate) fn insert_space_before_function_parenthesis_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.insert_space_before_function_parenthesis
}

/// `placeOpenBraceOnNewLineForFunctionsOption`
pub(crate) fn place_open_brace_on_new_line_for_functions_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.place_open_brace_on_new_line_for_functions
}

/// `placeOpenBraceOnNewLineForControlBlocksOption`
pub(crate) fn place_open_brace_on_new_line_for_control_blocks_option(
    options: &FormatCodeSettings,
) -> Tristate {
    options.place_open_brace_on_new_line_for_control_blocks
}

/// `insertSpaceBeforeTypeAnnotationOption`
pub(crate) fn insert_space_before_type_annotation_option(options: &FormatCodeSettings) -> Tristate {
    options.insert_space_before_type_annotation
}

/// `optionEquals`
pub(crate) fn option_equals(
    option_name: fn(&FormatCodeSettings) -> SemicolonPreference,
    option_value: SemicolonPreference,
) -> ContextPredicate {
    Box::new(
        move |context: &mut FormattingContext, _nodes: &mut Vec<Node>| {
            option_name(&context.options) == option_value
        },
    )
}

/// `isOptionEnabled`
pub(crate) fn is_option_enabled(option_name: OptionSelector) -> ContextPredicate {
    Box::new(
        move |context: &mut FormattingContext, _nodes: &mut Vec<Node>| {
            option_name(&context.options).is_true()
        },
    )
}

/// `isOptionDisabled`
pub(crate) fn is_option_disabled(option_name: OptionSelector) -> ContextPredicate {
    Box::new(
        move |context: &mut FormattingContext, _nodes: &mut Vec<Node>| {
            option_name(&context.options).is_false()
        },
    )
}

/// `isOptionDisabledOrUndefined`
pub(crate) fn is_option_disabled_or_undefined(option_name: OptionSelector) -> ContextPredicate {
    Box::new(
        move |context: &mut FormattingContext, _nodes: &mut Vec<Node>| {
            option_name(&context.options).is_false_or_unknown()
        },
    )
}

/// `isOptionDisabledOrUndefinedOrTokensOnSameLine`
pub(crate) fn is_option_disabled_or_undefined_or_tokens_on_same_line(
    option_name: OptionSelector,
) -> ContextPredicate {
    Box::new(
        move |context: &mut FormattingContext, nodes: &mut Vec<Node>| {
            option_name(&context.options).is_false_or_unknown()
                || context.tokens_are_on_same_line(nodes)
        },
    )
}

/// `isOptionEnabledOrUndefined`
pub(crate) fn is_option_enabled_or_undefined(option_name: OptionSelector) -> ContextPredicate {
    Box::new(
        move |context: &mut FormattingContext, _nodes: &mut Vec<Node>| {
            option_name(&context.options).is_true_or_unknown()
        },
    )
}

/// `isForContext`
pub(crate) fn is_for_context(context: &mut FormattingContext, nodes: &mut Vec<Node>) -> bool {
    nodes[context.context_node].kind == Kind::ForStatement
}

/// `isNotForContext`
pub(crate) fn is_not_for_context(context: &mut FormattingContext, nodes: &mut Vec<Node>) -> bool {
    !is_for_context(context, nodes)
}

/// `isBinaryOpContext`
pub(crate) fn is_binary_op_context(context: &mut FormattingContext, nodes: &mut Vec<Node>) -> bool {
    match nodes[context.context_node].kind {
        Kind::BinaryExpression => {
            nodes[context.context_node]
                .as_binary_expression()
                .operator_token
                .is_some_and(|t| nodes[t].kind != Kind::CommaToken)
        }
        Kind::ConditionalExpression
        | Kind::ConditionalType
        | Kind::AsExpression
        | Kind::ExportSpecifier
        | Kind::ImportSpecifier
        | Kind::TypePredicate
        | Kind::UnionType
        | Kind::IntersectionType
        | Kind::SatisfiesExpression => true,

        // equals in binding elements func foo([[x, y] = [1, 2]])
        Kind::BindingElement
        // equal in type X = ...
        | Kind::TypeAliasDeclaration
        // equal in import a = module('a');
        | Kind::ImportEqualsDeclaration
        // equal in export = 1
        | Kind::ExportAssignment
        // equal in let a = 0
        | Kind::VariableDeclaration
        // equal in p = 0
        | Kind::Parameter
        | Kind::EnumMember
        | Kind::PropertyDeclaration
        | Kind::PropertySignature => {
            context.current_token_span.kind == Kind::EqualsToken
                || context.next_token_span.kind == Kind::EqualsToken
        }
        // "in" keyword in for (let x in []) { }
        Kind::ForInStatement
        // "in" keyword in [P in keyof T] T[P]
        | Kind::TypeParameter => {
            context.current_token_span.kind == Kind::InKeyword
                || context.next_token_span.kind == Kind::InKeyword
                || context.current_token_span.kind == Kind::EqualsToken
                || context.next_token_span.kind == Kind::EqualsToken
        }
        // Technically, "of" is not a binary operator, but format it the same way as "in"
        Kind::ForOfStatement => {
            context.current_token_span.kind == Kind::OfKeyword
                || context.next_token_span.kind == Kind::OfKeyword
        }
        _ => false,
    }
}

/// `isNotBinaryOpContext`
pub(crate) fn is_not_binary_op_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    !is_binary_op_context(context, nodes)
}

/// `isNotTypeAnnotationContext`
pub(crate) fn is_not_type_annotation_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    !is_type_annotation_context(context, nodes)
}

/// `isTypeAnnotationContext`
pub(crate) fn is_type_annotation_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    let context_kind = nodes[context.context_node].kind;
    context_kind == Kind::PropertyDeclaration
        || context_kind == Kind::PropertySignature
        || context_kind == Kind::Parameter
        || context_kind == Kind::VariableDeclaration
        || tsc_ast::is_function_like_kind(context_kind)
}

/// `isOptionalPropertyContext`
pub(crate) fn is_optional_property_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    tsc_ast::is_property_declaration(&nodes[context.context_node])
        && tsc_ast::has_question_token(&nodes[context.context_node], nodes)
}

/// `isNonOptionalPropertyContext`
pub(crate) fn is_non_optional_property_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    !is_optional_property_context(context, nodes)
}

/// `isConditionalOperatorContext`
pub(crate) fn is_conditional_operator_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    let kind = nodes[context.context_node].kind;
    kind == Kind::ConditionalExpression || kind == Kind::ConditionalType
}

/// `isSameLineTokenOrBeforeBlockContext`
pub(crate) fn is_same_line_token_or_before_block_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    context.tokens_are_on_same_line(nodes) || is_before_block_context(context, nodes)
}

/// `isBraceWrappedContext`
pub(crate) fn is_brace_wrapped_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    let kind = nodes[context.context_node].kind;
    kind == Kind::ObjectBindingPattern
        || kind == Kind::MappedType
        || is_single_line_block_context(context, nodes)
}

/// `isBeforeMultilineBlockContext` — this check is done before an open brace
/// in a control construct, a function, or a typescript block declaration
pub(crate) fn is_before_multiline_block_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    is_before_block_context(context, nodes)
        && !(context.next_node_all_on_same_line(nodes)
            || context.next_node_block_is_on_one_line(nodes))
}

/// `isMultilineBlockContext`
pub(crate) fn is_multiline_block_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    is_block_context(context, nodes)
        && !(context.context_node_all_on_same_line(nodes)
            || context.context_node_block_is_on_one_line(nodes))
}

/// `isSingleLineBlockContext`
pub(crate) fn is_single_line_block_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    is_block_context(context, nodes)
        && (context.context_node_all_on_same_line(nodes)
            || context.context_node_block_is_on_one_line(nodes))
}

/// `isBlockContext`
pub(crate) fn is_block_context(context: &mut FormattingContext, nodes: &mut Vec<Node>) -> bool {
    node_is_block_context(context.context_node, nodes)
}

/// `isBeforeBlockContext`
pub(crate) fn is_before_block_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    node_is_block_context(context.next_token_parent, nodes)
}

/// `nodeIsBlockContext` — IMPORTANT!!! This method must return true ONLY for
/// nodes with open and close braces as immediate children
pub(crate) fn node_is_block_context(node: NodeId, nodes: &mut Vec<Node>) -> bool {
    if node_is_type_script_decl_with_block_context(node, nodes) {
        // This means we are in a context that looks like a block to the user, but in the grammar is actually not a node (it's a class, module, enum, object type literal, etc).
        return true;
    }

    matches!(
        nodes[node].kind,
        Kind::Block | Kind::CaseBlock | Kind::ObjectLiteralExpression | Kind::ModuleBlock
    )
}

/// `isFunctionDeclContext`
pub(crate) fn is_function_decl_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    matches!(
        nodes[context.context_node].kind,
        Kind::FunctionDeclaration
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            // case ast.KindMemberFunctionDeclaration:
            | Kind::GetAccessor
            | Kind::SetAccessor
            // case ast.KindMethodSignature:
            | Kind::CallSignature
            | Kind::FunctionExpression
            | Kind::Constructor
            | Kind::ArrowFunction
            // case ast.KindConstructorDeclaration:
            // case ast.KindSimpleArrowFunctionExpression:
            // case ast.KindParenthesizedArrowFunctionExpression:
            | Kind::InterfaceDeclaration // This one is not truly a function, but for formatting purposes, it acts just like one
    )
}

/// `isNotFunctionDeclContext`
pub(crate) fn is_not_function_decl_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    !is_function_decl_context(context, nodes)
}

/// `isFunctionDeclarationOrFunctionExpressionContext`
pub(crate) fn is_function_declaration_or_function_expression_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    let kind = nodes[context.context_node].kind;
    kind == Kind::FunctionDeclaration || kind == Kind::FunctionExpression
}

/// `isTypeScriptDeclWithBlockContext`
pub(crate) fn is_type_script_decl_with_block_context_ctx(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    node_is_type_script_decl_with_block_context(context.context_node, nodes)
}

/// `nodeIsTypeScriptDeclWithBlockContext`
pub(crate) fn node_is_type_script_decl_with_block_context(
    node: NodeId,
    nodes: &mut Vec<Node>,
) -> bool {
    matches!(
        nodes[node].kind,
        Kind::ClassDeclaration
            | Kind::ClassExpression
            | Kind::InterfaceDeclaration
            | Kind::EnumDeclaration
            | Kind::TypeLiteral
            | Kind::ModuleDeclaration
            | Kind::ExportDeclaration
            | Kind::NamedExports
            | Kind::ImportDeclaration
            | Kind::NamedImports
    )
}

/// `isAfterCodeBlockContext`
pub(crate) fn is_after_code_block_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    match nodes[context.current_token_parent].kind {
        Kind::ClassDeclaration
        | Kind::ModuleDeclaration
        | Kind::EnumDeclaration
        | Kind::CatchClause
        | Kind::ModuleBlock
        | Kind::SwitchStatement => true,
        Kind::Block => {
            let block_parent = nodes[context.current_token_parent].parent;
            // In a codefix scenario, we can't rely on parents being set. So just always return true.
            block_parent.is_none_or(|bp| {
                nodes[bp].kind != Kind::ArrowFunction && nodes[bp].kind != Kind::FunctionExpression
            })
        }
        _ => false,
    }
}

/// `isControlDeclContext`
pub(crate) fn is_control_decl_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    matches!(
        nodes[context.context_node].kind,
        Kind::IfStatement
            | Kind::SwitchStatement
            | Kind::ForStatement
            | Kind::ForInStatement
            | Kind::ForOfStatement
            | Kind::WhileStatement
            | Kind::TryStatement
            | Kind::DoStatement
            | Kind::WithStatement
            // TODO
            // case ast.KindElseClause:
            | Kind::CatchClause
    )
}

/// `isObjectContext`
pub(crate) fn is_object_context(context: &mut FormattingContext, nodes: &mut Vec<Node>) -> bool {
    nodes[context.context_node].kind == Kind::ObjectLiteralExpression
}

/// `isFunctionCallContext`
pub(crate) fn is_function_call_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::CallExpression
}

/// `isNewContext`
pub(crate) fn is_new_context(context: &mut FormattingContext, nodes: &mut Vec<Node>) -> bool {
    nodes[context.context_node].kind == Kind::NewExpression
}

/// `isFunctionCallOrNewContext`
pub(crate) fn is_function_call_or_new_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    is_function_call_context(context, nodes) || is_new_context(context, nodes)
}

/// `isPreviousTokenNotComma`
pub(crate) fn is_previous_token_not_comma(
    context: &mut FormattingContext,
    _nodes: &mut Vec<Node>,
) -> bool {
    context.current_token_span.kind != Kind::CommaToken
}

/// `isNextTokenNotCloseBracket`
pub(crate) fn is_next_token_not_close_bracket(
    context: &mut FormattingContext,
    _nodes: &mut Vec<Node>,
) -> bool {
    context.next_token_span.kind != Kind::CloseBracketToken
}

/// `isNextTokenNotCloseParen`
pub(crate) fn is_next_token_not_close_paren(
    context: &mut FormattingContext,
    _nodes: &mut Vec<Node>,
) -> bool {
    context.next_token_span.kind != Kind::CloseParenToken
}

/// `isArrowFunctionContext`
pub(crate) fn is_arrow_function_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::ArrowFunction
}

/// `isImportTypeContext`
pub(crate) fn is_import_type_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::ImportType
}

/// `isNonJsxSameLineTokenContext`
pub(crate) fn is_non_jsx_same_line_token_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    context.tokens_are_on_same_line(nodes) && nodes[context.context_node].kind != Kind::JsxText
}

/// `isNonJsxTextContext`
pub(crate) fn is_non_jsx_text_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind != Kind::JsxText
}

/// `isNonJsxElementOrFragmentContext`
pub(crate) fn is_non_jsx_element_or_fragment_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    let kind = nodes[context.context_node].kind;
    kind != Kind::JsxElement && kind != Kind::JsxFragment
}

/// `isJsxExpressionContext`
pub(crate) fn is_jsx_expression_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    let kind = nodes[context.context_node].kind;
    kind == Kind::JsxExpression || kind == Kind::JsxSpreadAttribute
}

/// `isNextTokenParentJsxAttribute`
pub(crate) fn is_next_token_parent_jsx_attribute(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    let kind = nodes[context.next_token_parent].kind;
    kind == Kind::JsxAttribute
        || (kind == Kind::JsxNamespacedName
            && nodes[context.next_token_parent]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::JsxAttribute))
}

/// `isJsxAttributeContext`
pub(crate) fn is_jsx_attribute_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::JsxAttribute
}

/// `isNextTokenParentNotJsxNamespacedName`
pub(crate) fn is_next_token_parent_not_jsx_namespaced_name(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.next_token_parent].kind != Kind::JsxNamespacedName
}

/// `isNextTokenParentJsxNamespacedName`
pub(crate) fn is_next_token_parent_jsx_namespaced_name(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.next_token_parent].kind == Kind::JsxNamespacedName
}

/// `isJsxSelfClosingElementContext`
pub(crate) fn is_jsx_self_closing_element_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::JsxSelfClosingElement
}

/// `isNotBeforeBlockInFunctionDeclarationContext`
pub(crate) fn is_not_before_block_in_function_declaration_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    !is_function_decl_context(context, nodes) && !is_before_block_context(context, nodes)
}

/// `isEndOfDecoratorContextOnSameLine`
pub(crate) fn is_end_of_decorator_context_on_same_line(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    context.tokens_are_on_same_line(nodes)
        && tsc_ast::has_decorators(&nodes[context.context_node])
        && node_is_in_decorator_context(Some(context.current_token_parent), nodes)
        && !node_is_in_decorator_context(Some(context.next_token_parent), nodes)
}

/// `nodeIsInDecoratorContext`
pub(crate) fn node_is_in_decorator_context(
    mut node: Option<NodeId>,
    nodes: &mut Vec<Node>,
) -> bool {
    while let Some(n) = node {
        if !tsc_ast::is_expression(&nodes[n], nodes) {
            break;
        }
        node = nodes[n].parent;
    }
    node.is_some_and(|n| nodes[n].kind == Kind::Decorator)
}

/// `isStartOfVariableDeclarationList`
pub(crate) fn is_start_of_variable_declaration_list(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.current_token_parent].kind == Kind::VariableDeclarationList
        && get_token_pos_of_node(
            context.current_token_parent,
            nodes[context.source_file].as_source_file(),
            false,
            nodes,
        ) == context.current_token_span.loc.pos()
}

/// `isNotFormatOnEnter`
pub(crate) fn is_not_format_on_enter(
    context: &mut FormattingContext,
    _nodes: &mut Vec<Node>,
) -> bool {
    context.formatting_request_kind != FormatRequestKind::FormatOnEnter
}

/// `isModuleDeclContext`
pub(crate) fn is_module_decl_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::ModuleDeclaration
}

/// `isObjectTypeContext`
pub(crate) fn is_object_type_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::TypeLiteral // && context.contextNode.parent.Kind != ast.KindInterfaceDeclaration;
}

/// `isConstructorSignatureContext`
pub(crate) fn is_constructor_signature_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::ConstructSignature
}

/// `isTypeArgumentOrParameterOrAssertion`
pub(crate) fn is_type_argument_or_parameter_or_assertion(
    token: TextRangeWithKind,
    parent: NodeId,
    nodes: &mut Vec<Node>,
) -> bool {
    if token.kind != Kind::LessThanToken && token.kind != Kind::GreaterThanToken {
        return false;
    }
    matches!(
        nodes[parent].kind,
        Kind::TypeReference
            | Kind::TypeAssertionExpression
            | Kind::TypeAliasDeclaration
            | Kind::ClassDeclaration
            | Kind::ClassExpression
            | Kind::InterfaceDeclaration
            | Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::ArrowFunction
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::CallSignature
            | Kind::ConstructSignature
            | Kind::CallExpression
            | Kind::NewExpression
            | Kind::ExpressionWithTypeArguments
    )
}

/// `isTypeArgumentOrParameterOrAssertionContext`
pub(crate) fn is_type_argument_or_parameter_or_assertion_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    is_type_argument_or_parameter_or_assertion(
        context.current_token_span,
        context.current_token_parent,
        nodes,
    ) || is_type_argument_or_parameter_or_assertion(
        context.next_token_span,
        context.next_token_parent,
        nodes,
    )
}

/// `isTypeAssertionContext`
pub(crate) fn is_type_assertion_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::TypeAssertionExpression
}

/// `isNonTypeAssertionContext`
pub(crate) fn is_non_type_assertion_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    !is_type_assertion_context(context, nodes)
}

/// `isVoidOpContext`
pub(crate) fn is_void_op_context(context: &mut FormattingContext, nodes: &mut Vec<Node>) -> bool {
    context.current_token_span.kind == Kind::VoidKeyword
        && nodes[context.current_token_parent].kind == Kind::VoidExpression
}

/// `isYieldOrYieldStarWithOperand`
pub(crate) fn is_yield_or_yield_star_with_operand(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::YieldExpression
        && nodes[context.context_node].expression().is_some()
}

/// `isNonNullAssertionContext`
pub(crate) fn is_non_null_assertion_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    nodes[context.context_node].kind == Kind::NonNullExpression
}

/// `isNotStatementConditionContext`
pub(crate) fn is_not_statement_condition_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    !is_statement_condition_context(context, nodes)
}

/// `isStatementConditionContext`
pub(crate) fn is_statement_condition_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    matches!(
        nodes[context.context_node].kind,
        Kind::IfStatement
            | Kind::ForStatement
            | Kind::ForInStatement
            | Kind::ForOfStatement
            | Kind::DoStatement
            | Kind::WhileStatement
    )
}

/// `isSemicolonDeletionContext`
pub(crate) fn is_semicolon_deletion_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    let mut next_token_kind = context.next_token_span.kind;
    let mut next_token_start = context.next_token_span.loc.pos();
    if tsc_ast::is_trivia(next_token_kind) {
        let next_real_token = if context.next_token_parent == context.current_token_parent {
            // !!! TODO: very different from strada, but strada's logic here is wonky - find the first ancestor without a parent? that's just the source file.
            find_next_token(
                nodes,
                context.source_file,
                context.next_token_parent,
                context.source_file,
            )
        } else {
            get_first_token(nodes, context.next_token_parent, context.source_file)
        };

        let Some(next_real_token) = next_real_token else {
            return true;
        };
        next_token_kind = nodes[next_real_token].kind;
        next_token_start = get_token_pos_of_node(
            next_real_token,
            nodes[context.source_file].as_source_file(),
            false,
            nodes,
        );
    }

    let start_line = line_of_position(
        nodes,
        context.source_file,
        context.current_token_span.loc.pos(),
    );
    let end_line = line_of_position(nodes, context.source_file, next_token_start);
    if start_line == end_line {
        return next_token_kind == Kind::CloseBraceToken || next_token_kind == Kind::EndOfFile;
    }

    if next_token_kind == Kind::SemicolonToken
        && context.current_token_span.kind == Kind::SemicolonToken
    {
        return true;
    }

    if next_token_kind == Kind::SemicolonClassElement || next_token_kind == Kind::SemicolonToken {
        return false;
    }

    let context_kind = nodes[context.context_node].kind;
    if context_kind == Kind::InterfaceDeclaration || context_kind == Kind::TypeAliasDeclaration {
        // Can't remove semicolon after `foo`; it would parse as a method declaration:
        //
        // interface I {
        //   foo;
        //   () void
        // }
        return nodes[context.current_token_parent].kind != Kind::PropertySignature
            || nodes[context.current_token_parent].type_().is_some()
            || next_token_kind != Kind::OpenParenToken;
    }

    if tsc_ast::is_property_declaration(&nodes[context.current_token_parent]) {
        return nodes[context.current_token_parent].initializer().is_none();
    }

    nodes[context.current_token_parent].kind != Kind::ForStatement
        && nodes[context.current_token_parent].kind != Kind::EmptyStatement
        && nodes[context.current_token_parent].kind != Kind::SemicolonClassElement
        && next_token_kind != Kind::OpenBracketToken
        && next_token_kind != Kind::OpenParenToken
        && next_token_kind != Kind::PlusToken
        && next_token_kind != Kind::MinusToken
        && next_token_kind != Kind::SlashToken
        && next_token_kind != Kind::RegularExpressionLiteral
        && next_token_kind != Kind::CommaToken
        && next_token_kind != Kind::TemplateExpression
        && next_token_kind != Kind::TemplateHead
        && next_token_kind != Kind::NoSubstitutionTemplateLiteral
        && next_token_kind != Kind::DotToken
}

/// `isSemicolonInsertionContext`
pub(crate) fn is_semicolon_insertion_context(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    position_is_asi_candidate(
        nodes,
        context.current_token_span.loc.end(),
        context.current_token_parent,
        context.source_file,
    )
}

/// `isNotPropertyAccessOnIntegerLiteral`
pub(crate) fn is_not_property_access_on_integer_literal(
    context: &mut FormattingContext,
    nodes: &mut Vec<Node>,
) -> bool {
    !tsc_ast::is_property_access_expression(&nodes[context.context_node])
        || !nodes[context.context_node]
            .expression()
            .is_some_and(|e| tsc_ast::is_numeric_literal(&nodes[e]))
        || nodes[context.context_node]
            .expression()
            .is_some_and(|e| nodes[e].text(nodes).contains('.'))
}
