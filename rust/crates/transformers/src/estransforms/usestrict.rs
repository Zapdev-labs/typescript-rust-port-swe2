// Ported from tsc/internal/transformers/estransforms/usestrict.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `NewUseStrictTransformer` — prepends a `"use strict"` prologue to non-JSON
// source files that need one (non-ESM emit, or ESM source compiled to CJS).

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId};
use tsc_core::options_generated::{CompilerOptions, ModuleKind};
use tsc_core::scriptkind::ScriptKind;

use super::{Ec, make_transformer};
use crate::chain::{GetEmitModuleFormatOfFile, TransformOptions};
use crate::transformer::Transformer;

/// `NewUseStrictTransformer`.
pub fn new_use_strict_transformer<'a>(opts: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    let compiler_options = opts.compiler_options;
    let get_emit_module_format_of_file = opts.get_emit_module_format_of_file;
    make_transformer(opts, move |ec| {
        Box::new(move |v, cx, node| {
            use_strict_visit(
                &ec,
                compiler_options,
                get_emit_module_format_of_file,
                v,
                cx,
                node,
            )
        })
    })
}

/// `(tx *useStrictTransformer) visit`.
fn use_strict_visit<'a>(
    ec: &Ec,
    compiler_options: Option<&'a CompilerOptions>,
    get_emit_module_format_of_file: Option<&'a GetEmitModuleFormatOfFile<'a>>,
    _v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    if cx.nodes[node].kind != Kind::SourceFile {
        return Some(node);
    }
    Some(visit_source_file(
        ec,
        compiler_options,
        get_emit_module_format_of_file,
        cx,
        node,
    ))
}

/// `(tx *useStrictTransformer) visitSourceFile` — `node` must be a
/// `SourceFile`.
fn visit_source_file<'a>(
    ec: &Ec,
    compiler_options: Option<&'a CompilerOptions>,
    get_emit_module_format_of_file: Option<&'a GetEmitModuleFormatOfFile<'a>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    if cx.nodes[node].as_source_file().script_kind == ScriptKind::Json {
        return node;
    }

    let is_external_module = ast::is_external_module(cx.nodes[node].as_source_file());
    let module_kind = compiler_options
        .expect("useStrictTransformer requires compiler options")
        .get_emit_module_kind();
    let format = get_emit_module_format_of_file
        .expect("useStrictTransformer requires getEmitModuleFormatOfFile")(
        cx.nodes[node].as_source_file(),
    );

    // ESM is always strict. If the file is ESM, and CJS emit
    // has not been requested, then skip adding "use strict".
    if is_external_module
        && module_kind >= ModuleKind::ES2015
        && (module_kind == ModuleKind::Preserve || format >= ModuleKind::ES2015)
    {
        return node;
    }

    let statements_nodes: Vec<NodeId> = cx.nodes[node]
        .statements()
        .map(<[_]>::to_vec)
        .unwrap_or_default();
    let statements = ec
        .borrow_mut()
        .factory
        .ensure_use_strict(cx.nodes, &statements_nodes);
    let mut statement_list = ec.borrow_mut().factory.new_node_list(statements);
    statement_list.loc = cx.nodes[node]
        .as_source_file()
        .statements
        .as_ref()
        .map(|l| l.loc)
        .unwrap_or_default();
    let end_of_file_token = cx.nodes[node].as_source_file().end_of_file_token;
    ec.borrow_mut()
        .factory
        .update_source_file(cx.nodes, node, Some(statement_list), end_of_file_token)
        .unwrap_or(node)
}
