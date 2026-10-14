// Ported from tsc/internal/transformers/estransforms/taggedtemplate.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `newTaggedTemplateLiftRestrictionTransformer` — lowers tagged templates
// that contain invalid escape sequences into calls through
// `__makeTemplateObject` (which produces a cooked `undefined` for the invalid
// portions).

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, Node, NodeId, SubtreeFacts, TokenFlags};
use tsc_core::text::TextRange;

use super::{Ec, make_transformer, visit_each_child, visit_node};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;

/// `newlineNormalizer` — <CR><LF> and <CR> LineTerminatorSequences are
/// normalized to <LF> for both TV and TRV (ES6 Spec 11.8.6.1).
fn normalize_newlines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

/// `type taggedTemplateTransformer struct` — `currentSourceFile` and
/// `taggedTemplateStringDeclarations`, held via interior mutability so the
/// `Fn` visit closure can mutate them.
#[derive(Default)]
struct TaggedTemplateTransformer {
    current_source_file: Cell<Option<NodeId>>,
    tagged_template_string_declarations: RefCell<Vec<NodeId>>,
}

/// `newTaggedTemplateLiftRestrictionTransformer`.
pub(crate) fn new_tagged_template_lift_restriction_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        let tx = Rc::new(TaggedTemplateTransformer::default());
        Box::new(move |v, cx, node| tx.visit(&ec, v, cx, node))
    })
}

impl TaggedTemplateTransformer {
    /// `(tx *taggedTemplateTransformer) visit`.
    fn visit<'a>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_INVALID_TEMPLATE_ESCAPE
            == SubtreeFacts::NONE
        {
            return Some(node);
        }
        match cx.nodes[node].kind {
            Kind::SourceFile => Some(self.visit_source_file(ec, v, cx, node)),
            Kind::TaggedTemplateExpression => {
                Some(self.visit_tagged_template_expression(ec, v, cx, node))
            }
            _ => Some(visit_each_child(v, cx, node)),
        }
    }

    /// `(tx *taggedTemplateTransformer) visitSourceFile` — `node` must be a
    /// `SourceFile`.
    fn visit_source_file<'a>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.current_source_file.set(Some(node));
        *self.tagged_template_string_declarations.borrow_mut() = Vec::new();
        let mut visited = visit_each_child(v, cx, node);

        if !self.tagged_template_string_declarations.borrow().is_empty() {
            let declarations =
                std::mem::take(&mut *self.tagged_template_string_declarations.borrow_mut());
            // `slices.Clip(visitedSourceFile.Statements.Nodes)` — the slice
            // contents are read here; `Clip` only trims capacity, a no-op for
            // a fresh `Vec`.
            let mut statements: Vec<NodeId> = cx.nodes[visited]
                .statements()
                .map(<[_]>::to_vec)
                .unwrap_or_default();
            let variable_statement = {
                let mut e = ec.borrow_mut();
                let decl_list_nodes = e.factory.new_node_list(declarations);
                let decl_list = e.factory.new_variable_declaration_list(
                    cx.nodes,
                    Some(decl_list_nodes),
                    ast::NodeFlags::NONE,
                );
                e.factory
                    .new_variable_statement(cx.nodes, None, Some(decl_list))
            };
            statements.push(variable_statement);
            let statements_loc = cx.nodes[node]
                .as_source_file()
                .statements
                .as_ref()
                .map(|l| l.loc)
                .unwrap_or_else(TextRange::default);
            let mut stmt_list = ec.borrow_mut().factory.new_node_list(statements);
            stmt_list.loc = statements_loc;
            let end_of_file_token = cx.nodes[visited].as_source_file().end_of_file_token;
            visited = ec
                .borrow_mut()
                .factory
                .update_source_file(cx.nodes, visited, Some(stmt_list), end_of_file_token)
                .unwrap_or(visited);
        }

        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(visited, &helpers);
        visited
    }

    /// `(tx *taggedTemplateTransformer) visitTaggedTemplateExpression` —
    /// `node` must be a `TaggedTemplateExpression`.
    fn visit_tagged_template_expression<'a>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.process_tagged_template_expression(ec, v, cx, node)
    }

    /// `(tx *taggedTemplateTransformer) processTaggedTemplateExpression` —
    /// `node` must be a `TaggedTemplateExpression`.
    fn process_tagged_template_expression<'a>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let tag_id = cx.nodes[node].as_tagged_template_expression().tag.unwrap();
        let tag = visit_node(v, cx, tag_id).expect("VisitNode returned no node");
        let template = cx.nodes[node]
            .as_tagged_template_expression()
            .template
            .unwrap();

        if !has_invalid_escape(cx.nodes, template) {
            return visit_each_child(v, cx, node);
        }

        // Build up the template arguments and the raw and cooked strings for
        // the template.
        // `templateArguments[0]` is a placeholder for the template object.
        let mut template_arguments: Vec<NodeId> = Vec::new();
        let mut cooked_strings: Vec<NodeId> = Vec::new();
        let mut raw_strings: Vec<NodeId> = Vec::new();

        if ast::is_no_substitution_template_literal(&cx.nodes[template]) {
            cooked_strings.push(create_template_cooked(ec, cx, template));
            raw_strings.push(get_raw_literal(ec, cx, template));
        } else {
            let (head, template_spans) = {
                let te = cx.nodes[template].as_template_expression();
                (te.head, te.template_spans.clone())
            };
            cooked_strings.push(create_template_cooked(ec, cx, head.unwrap()));
            raw_strings.push(get_raw_literal(ec, cx, head.unwrap()));
            if let Some(spans) = template_spans {
                for span in spans.nodes.iter() {
                    let (literal, span_expression) = {
                        let ts = cx.nodes[*span].as_template_span();
                        (ts.literal, ts.expression)
                    };
                    cooked_strings.push(create_template_cooked(ec, cx, literal.unwrap()));
                    raw_strings.push(get_raw_literal(ec, cx, literal.unwrap()));
                    let visited_expr = visit_node(
                        v,
                        cx,
                        span_expression.expect("template span has no expression"),
                    )
                    .expect("VisitNode returned no node");
                    template_arguments.push(visited_expr);
                }
            }
        }

        let helper_call = {
            let mut e = ec.borrow_mut();
            let f = &mut e.factory;
            let cooked_list = f.new_node_list(cooked_strings);
            let cooked_array = f.new_array_literal_expression(cx.nodes, Some(cooked_list), false);
            let raw_list = f.new_node_list(raw_strings);
            let raw_array = f.new_array_literal_expression(cx.nodes, Some(raw_list), false);
            f.new_template_object_helper(cx.nodes, cooked_array, raw_array)
        };

        // Create a variable to cache the template object if we're in a
        // module. Do not do this in the global scope, as any variable we
        // currently generate could conflict with variables from outside of
        // the current compilation. In the future, we can revisit this
        // behavior.
        let template_object = if ast::is_external_module(
            cx.nodes[self
                .current_source_file
                .get()
                .expect("no current source file")]
            .as_source_file(),
        ) {
            let temp_var = ec
                .borrow_mut()
                .factory
                .new_unique_name(cx.nodes, "templateObject");
            let decl = ec.borrow_mut().factory.new_variable_declaration(
                cx.nodes,
                Some(temp_var),
                None,
                None,
                None,
            );
            self.tagged_template_string_declarations
                .borrow_mut()
                .push(decl);
            let assignment =
                ec.borrow_mut()
                    .factory
                    .new_assignment_expression(cx.nodes, temp_var, helper_call);
            ec.borrow_mut()
                .factory
                .new_logical_or_expression(cx.nodes, temp_var, assignment)
        } else {
            helper_call
        };
        let mut all_arguments = vec![template_object];
        all_arguments.extend(template_arguments);

        let arg_list = ec.borrow_mut().factory.new_node_list(all_arguments);
        let call = ec.borrow_mut().factory.new_call_expression(
            cx.nodes,
            Some(tag),
            None, // question_dot_token
            None, // type_arguments
            Some(arg_list),
            ast::NodeFlags::NONE,
        );
        cx.nodes[call].loc = cx.nodes[node].loc;
        call
    }
}

/// `createTemplateCooked` — `template` is a node carrying
/// `TemplateLiteralLikeNodeBase` data.
fn create_template_cooked(ec: &Ec, cx: &mut VisitorCx<'_, '_>, template: NodeId) -> NodeId {
    let data = cx.nodes[template]
        .template_literal_like_data()
        .expect("node has no template literal data");
    if data.template_flags & TokenFlags::IS_INVALID != TokenFlags::NONE {
        return ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
    }
    let text = data.literal_like_node_base.text.clone();
    ec.borrow_mut()
        .factory
        .new_string_literal(cx.nodes, &text, TokenFlags::NONE)
}

/// `getRawLiteral`.
fn get_raw_literal(ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
    let mut text = cx.nodes[node]
        .template_literal_like_data()
        .expect("node has no template literal data")
        .raw_text
        .to_string();
    if text.is_empty() {
        let source_file = ast::get_source_file_of_node(Some(node), cx.nodes);
        text = tsc_scanner::utilities::get_source_text_of_node_from_source_file(
            cx.nodes[source_file.expect("node has no source file")].as_source_file(),
            node,
            false, // include_trivia
            cx.nodes,
        )
        .into_owned();
        // text contains the original source, it will also contain quotes
        // ("`"), dollar signs and braces ("${" and "}"), thus we need to
        // remove those characters.
        // First template piece starts with "`", others with "}"
        // Last template piece ends with "`", others with "${"
        let is_last = cx.nodes[node].kind == Kind::NoSubstitutionTemplateLiteral
            || cx.nodes[node].kind == Kind::TemplateTail;
        let end_len = if is_last { 1 } else { 2 };
        text = text[1..text.len() - end_len].to_string();
    }

    // Newline normalization:
    // ES6 Spec 11.8.6.1 - Static Semantics of TV's and TRV's
    // <CR><LF> and <CR> LineTerminatorSequences are normalized to <LF> for
    // both TV and TRV.
    text = normalize_newlines(&text);

    let result = ec
        .borrow_mut()
        .factory
        .new_string_literal(cx.nodes, &text, TokenFlags::NONE);
    cx.nodes[result].loc = cx.nodes[node].loc;
    result
}

/// `hasInvalidEscape` — `template` is a `NoSubstitutionTemplateLiteral` or a
/// `TemplateExpression`.
fn has_invalid_escape(nodes: &[Node], template: NodeId) -> bool {
    if ast::is_no_substitution_template_literal(&nodes[template]) {
        return nodes[template]
            .template_literal_like_data()
            .expect("node has no template literal data")
            .template_flags
            & TokenFlags::CONTAINS_INVALID_ESCAPE
            != TokenFlags::NONE;
    }
    let (head, template_spans) = {
        let te = nodes[template].as_template_expression();
        (te.head, te.template_spans.clone())
    };
    if nodes[head.expect("template expression has no head")]
        .template_literal_like_data()
        .expect("node has no template literal data")
        .template_flags
        & TokenFlags::CONTAINS_INVALID_ESCAPE
        != TokenFlags::NONE
    {
        return true;
    }
    if let Some(spans) = template_spans {
        for span in spans.nodes.iter() {
            let literal = nodes[*span].as_template_span().literal;
            if nodes[literal.expect("template span has no literal")]
                .template_literal_like_data()
                .expect("node has no template literal data")
                .template_flags
                & TokenFlags::CONTAINS_INVALID_ESCAPE
                != TokenFlags::NONE
            {
                return true;
            }
        }
    }
    false
}
