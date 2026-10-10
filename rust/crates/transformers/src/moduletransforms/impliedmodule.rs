// Ported from tsc/internal/transformers/moduletransforms/impliedmodule.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The implied-module transform: picks the ES or CommonJS module transformer
// per file based on `GetEmitModuleFormatOfFile`, constructing each lazily on
// first use and reusing it across files (as Go reuses `tx.cjsTransformer`/
// `tx.esmTransformer`).

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{Kind, NodeId};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_core::options_generated::ModuleKind;

use super::commonjsmodule::new_common_js_module_transformer;
use super::esmodule::new_es_module_transformer;
use crate::chain::{GetEmitModuleFormatOfFile, TransformOptions};
use crate::estransforms::{Ec, make_transformer};
use crate::transformer::Transformer;

/// `type ImpliedModuleTransformer struct`.
struct ImpliedModuleTransformer<'a> {
    /// PORT: Go stores `opts *TransformOptions`; an owned copy keeps the
    /// lazy component-constructor calls from needing a `&'a` borrow of the
    /// caller's options (which cannot outlive the local binding).
    opts: TransformOptions<'a>,
    /// `resolver` — stored for parity with Go's
    /// `ImpliedModuleTransformer.resolver`; nothing in `impliedmodule.go`
    /// consults it (the component transformers re-read `opts.Resolver`).
    #[allow(dead_code)]
    resolver: Option<Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    get_emit_module_format_of_file: Option<&'a GetEmitModuleFormatOfFile<'a>>,
    /// `cjsTransformer`
    cjs_transformer: RefCell<Option<Transformer<'a>>>,
    /// `esmTransformer`
    esm_transformer: RefCell<Option<Transformer<'a>>>,
}

/// `NewImpliedModuleTransformer`.
///
/// PORT(deferred): Go wires this constructor (and the direct CJS/ES
/// constructors) from the emit pipeline, which is not yet ported — nothing
/// in the Rust workspace calls it yet. It is factory-shaped so it can be
/// inserted into `chain(...)` once the emit driver exists.
pub fn new_implied_module_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    let opts_owned = TransformOptions {
        context: opts.context.clone(),
        compiler_options: opts.compiler_options,
        resolver: opts.resolver.clone(),
        emit_resolver: opts.emit_resolver.clone(),
        get_emit_module_format_of_file: opts.get_emit_module_format_of_file,
        symbols: opts.symbols,
    };
    make_transformer(opts, |ec| {
        let tx = Rc::new(ImpliedModuleTransformer {
            opts: opts_owned,
            resolver: opts.resolver.clone(),
            get_emit_module_format_of_file: opts.get_emit_module_format_of_file,
            cjs_transformer: RefCell::new(None),
            esm_transformer: RefCell::new(None),
        });
        Box::new(move |_v, cx, node| tx.visit(&ec, _v, cx, node))
    })
}

impl<'a> ImpliedModuleTransformer<'a> {
    /// `(tx *ImpliedModuleTransformer) visit`
    fn visit(
        &self,
        _ec: &Ec,
        _v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].kind == Kind::SourceFile {
            return self.visit_source_file(cx, node);
        }
        Some(node)
    }

    /// `(tx *ImpliedModuleTransformer) visitSourceFile` — `node` must be a
    /// `SourceFile`.
    fn visit_source_file(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        if cx.nodes[node].as_source_file().is_declaration_file {
            return Some(node);
        }

        let format = (self
            .get_emit_module_format_of_file
            .expect("opts.GetEmitModuleFormatOfFile is required by the module transforms"))(
            cx.nodes[node].as_source_file(),
        );

        if format >= ModuleKind::ES2015 {
            let mut esm = self.esm_transformer.borrow_mut();
            if esm.is_none() {
                *esm = new_es_module_transformer(&self.opts);
            }
            esm.as_ref()
                .expect("NewESModuleTransformer returned nil")
                .transform_source_file(cx.nodes, node)
        } else {
            let mut cjs = self.cjs_transformer.borrow_mut();
            if cjs.is_none() {
                *cjs = new_common_js_module_transformer(&self.opts);
            }
            cjs.as_ref()
                .expect("NewCommonJSModuleTransformer returned nil")
                .transform_source_file(cx.nodes, node)
        }
    }
}
