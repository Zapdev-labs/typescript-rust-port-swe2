// Ported from tsc/internal/transformers/chain.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `TransformOptions`, `TransformerFactory`, and `Chain` — the plumbing that
// wires a sequence of transforms into a single source-file transform.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{self as ast, HasFileName, NodeId, SymbolArena};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_core::options_generated::{CompilerOptions, ModuleKind};
use tsc_printer::{EmitContext, EmitResolver};

use crate::transformer::Transformer;

/// `type TransformOptions struct`.
#[derive(Default)]
pub struct TransformOptions<'a> {
    /// `Context *printer.EmitContext` — `None` mirrors Go nil. Chained
    /// transforms share the same `Rc` just as Go components share
    /// `opt.Context`.
    pub context: Option<Rc<RefCell<EmitContext>>>,
    /// `CompilerOptions *core.CompilerOptions`
    pub compiler_options: Option<&'a CompilerOptions>,
    /// `Resolver binder.ReferenceResolver` — Go stores the interface value;
    /// `Rc<RefCell>` preserves the shared-and-mutable semantics.
    pub resolver: Option<Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    /// `EmitResolver printer.EmitResolver`
    pub emit_resolver: Option<Rc<RefCell<dyn EmitResolver + 'a>>>,
    /// `GetEmitModuleFormatOfFile func(file ast.HasFileName) core.ModuleKind`
    pub get_emit_module_format_of_file: Option<&'a GetEmitModuleFormatOfFile<'a>>,
    /// The binder-owned symbol arena the `ReferenceResolver` methods index
    /// into — Go resolvers read through `*ast.Symbol` pointers while the
    /// Rust trait surfaces `&SymbolArena` parameters. Carried on the
    /// options struct (rather than inside the resolver) so the transform
    /// can pass it to every resolver call.
    pub symbols: Option<&'a SymbolArena>,
}

/// `GetEmitModuleFormatOfFile` — the module-format callback stored on
/// `TransformOptions` (factored out for `clippy::type_complexity`).
pub type GetEmitModuleFormatOfFile<'a> = dyn Fn(&dyn HasFileName) -> ModuleKind + 'a;

/// `type TransformerFactory = func(opt *TransformOptions) *Transformer` —
/// `None` mirrors Go's nil return (skipped by `Chain`).
pub type TransformerFactory<'a> =
    Box<dyn Fn(&TransformOptions<'a>) -> Option<Transformer<'a>> + 'a>;

/// `Chain(transforms ...TransformerFactory) TransformerFactory`
///
/// Chains transforms in left-to-right order, running them one at a time in
/// order (as opposed to interleaved at each node) — the resulting combined
/// transform only operates on `SourceFile` nodes.
///
/// PORT: Go's `chainedTransformer` embeds `Transformer` and stores the
/// component `[]*Transformer`; here the component transformers are captured
/// by the visit closure through `Rc` (the closure cannot borrow the
/// transformer it is being installed on).
pub fn chain<'a>(transforms: Vec<TransformerFactory<'a>>) -> TransformerFactory<'a> {
    if transforms.len() < 2 {
        if transforms.is_empty() {
            panic!("Expected some number of transforms to chain, but got none");
        }
        return transforms.into_iter().next().unwrap();
    }
    Box::new(move |opt: &TransformOptions<'a>| {
        let mut constructed: Vec<Transformer<'a>> = Vec::with_capacity(transforms.len());
        for t in &transforms {
            // TODO: flatten nested chains?
            if let Some(result) = t(opt) {
                constructed.push(result);
            }
        }
        match constructed.len() {
            0 => return None,
            1 => return constructed.into_iter().next(),
            _ => {}
        }
        let components = Rc::new(constructed);
        let components_visit = components.clone();
        let visit: Box<VisitFn<'a>> = Box::new(
            move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                // `(ch *chainedTransformer) visit`
                if cx.nodes[node].kind != ast::Kind::SourceFile {
                    panic!("Chained transform passed non-sourcefile initial node");
                }
                let mut result = node;
                for t in components_visit.iter() {
                    result = t
                        .transform_source_file(cx.nodes, result)
                        .expect("chained transform returned no SourceFile");
                }
                Some(result)
            },
        );
        Some(Transformer::new(visit, opt.context.clone()))
    })
}
