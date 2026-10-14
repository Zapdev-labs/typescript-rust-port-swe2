//! `transpile.go` — single-file JavaScript and declaration emit.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_compiler::emit_host::{EmitOnly, EmitOptions};
use tsc_compiler::host::new_compiler_host;
use tsc_compiler::program::{ProgramConfig, ProgramFactories, ProgramHosts, new_program};
use tsc_core::context::Context;
use tsc_core::options_generated::{CompilerOptions, JsxEmit};
use tsc_tsoptions::enummaps::get_default_lib_file_name;
use tsc_tsoptions::parsedcommandline::new_parsed_command_line;
use tsc_tspath::{RootedFilePath, rooted_directory_path_from_normalized, to_rooted_file_path};

use crate::fs::TranspileFs;
use crate::options_generated::set_options_for_transpile;

/// `Options` configures single-file transpilation.
#[derive(Default)]
pub struct Options {
    /// `CompilerOptions` — the base compiler options to use for the
    /// transpilation. If `None`, a default set of compiler options is used.
    /// Regardless of what is provided, a number of options are
    /// unconditionally overridden; see [`transpile_module`] and
    /// [`transpile_declaration`].
    pub compiler_options: Option<CompilerOptions>,

    /// `FileName` — the name given to the synthesized input file. It only
    /// needs to be provided if the source text relies on characteristics
    /// implied by the file's extension or path, e.g. its extension controls
    /// whether the file is parsed as a script or module, whether JSX syntax
    /// is allowed, etc. Defaults to "module.ts", or "module.tsx" if
    /// `CompilerOptions.Jsx` is set.
    pub file_name: String,

    /// `ReportDiagnostics` indicates whether syntactic and compiler option
    /// diagnostics should be included in the result. Regardless of this
    /// setting, diagnostics produced while emitting (including declaration
    /// emit errors such as those produced by isolated declarations) are
    /// always included.
    pub report_diagnostics: bool,
}

/// `Output` contains the emitted text and any requested diagnostics.
#[derive(Default)]
pub struct Output {
    pub output_text: String,
    pub diagnostics: Vec<DiagnosticRef>,
    pub source_map_text: String,
    /// Node arena snapshots keyed by `NodeId::file_index`, retained so
    /// consumers can resolve `DiagnosticFile.node` handles (e.g.
    /// `wrap_ast_diagnostic`) after the program is dropped.
    pub nodes: FxHashMap<u32, Rc<tsc_ast::NodeArenaBuf>>,
}

/// `inputDirectory` is the synthetic current directory used to root the
/// single input file created for transpilation.
fn input_directory() -> tsc_tspath::RootedDirectoryPath {
    rooted_directory_path_from_normalized("/")
}

/// `libDirectory` is the synthetic directory that the barebones default
/// library file is placed in for declaration transpilation. See
/// [`BAREBONES_LIB_CONTENT`].
fn lib_directory() -> tsc_tspath::RootedDirectoryPath {
    rooted_directory_path_from_normalized("/lib")
}

/// `barebonesLibContent` — declaration emit works without a `lib`, but some
/// local inferences you'd expect to work won't without at least a minimal
/// `lib` available, since the checker will type inferred declarations as
/// `any` without these defined. Late bound symbol names, in particular, are
/// impossible to define without `Symbol` at least partially defined.
/// TODO: This should *probably* just load the full, real `lib` for the target.
pub const BAREBONES_LIB_CONTENT: &str = r#"interface Boolean {}
interface Function {}
interface CallableFunction {}
interface NewableFunction {}
interface IArguments {}
interface Number {}
interface Object {}
interface RegExp {}
interface String {}
interface Array<T> { length: number; [n: number]: T; }
interface SymbolConstructor {
    (desc?: string | number): symbol;
    for(name: string): symbol;
    readonly toStringTag: symbol;
}
declare var Symbol: SymbolConstructor;
interface Symbol {
    readonly [Symbol.toStringTag]: string;
}"#;

/// `TranspileModule` transpiles a single file of source text to JavaScript
/// using the specified options. If no compiler options are provided, a
/// default set of compiler options is used. It returns `None` if the context
/// is canceled before emission completes.
///
/// Extra compiler options that are unconditionally used by this function are:
///   - IsolatedModules = true (unless VerbatimModuleSyntax is set, which makes
///     this option redundant)
///   - NoCheck = true
///   - NoResolve = true
///   - NoLib = true
///   - Declaration = false
///   - DeclarationMap = false
///   - IsolatedDeclarations = false
pub fn transpile_module(ctx: &Context, input: &str, options: Options) -> Option<Output> {
    transpile_worker(ctx, input, options, false /*declaration*/)
}

/// `TranspileDeclaration` creates a declaration (.d.ts) file from a single
/// file of source text using the specified options. If no compiler options
/// are provided, a default set of compiler options is used.
///
/// Note that, because only the single input file is available, the resulting
/// declaration file may differ from the one a full program type-check and
/// emit would produce.
///
/// Extra compiler options that are unconditionally used by this function are:
///   - IsolatedModules = true (unless VerbatimModuleSyntax is set, which makes
///     this option redundant)
///   - NoCheck = true
///   - NoResolve = true
///   - NoLib = false
///   - Declaration = true
///   - EmitDeclarationOnly = true
///   - IsolatedDeclarations = true
pub fn transpile_declaration(ctx: &Context, input: &str, options: Options) -> Option<Output> {
    transpile_worker(ctx, input, options, true /*declaration*/)
}

fn transpile_worker(
    ctx: &Context,
    input: &str,
    options: Options,
    declaration: bool,
) -> Option<Output> {
    let mut opts = options.compiler_options.unwrap_or_default();
    set_options_for_transpile(&mut opts, declaration);

    // If jsx is specified, then treat the file as .tsx.
    let file_name = if options.file_name.is_empty() {
        if opts.jsx != JsxEmit::None {
            "module.tsx".to_string()
        } else {
            "module.ts".to_string()
        }
    } else {
        options.file_name
    };
    let input_directory = input_directory();
    let input_file_name = to_rooted_file_path(&file_name, &input_directory);

    let mut files: FxHashMap<RootedFilePath, String> = FxHashMap::default();
    files.insert(input_file_name.clone(), input.to_string());

    // Declaration emit needs a default lib to resolve global types (e.g.
    // `Array`, `Symbol`); plain transpilation sets NoLib so none is read.
    // The default lib name depends on the configured target.
    let lib_directory = lib_directory();
    if declaration {
        let lib_file_name = get_default_lib_file_name(&opts);
        files.insert(
            lib_directory.resolve_file(lib_file_name),
            BAREBONES_LIB_CONTENT.to_string(),
        );
    }

    let program_fs = Arc::new(TranspileFs { files });
    let host = new_compiler_host(program_fs.clone(), lib_directory, None, None, None);

    let program = new_program(tsc_compiler::program::ProgramOptions {
        config: Rc::new(ProgramConfig {
            config: Arc::new(new_parsed_command_line(
                opts,
                vec![input_file_name.clone()],
                vec![],
                input_directory,
                tsc_vfs::vfs::Vfs::case_sensitivity(program_fs.as_ref()),
            )),
            skip_module_resolution: true,
            ..Default::default()
        }),
        hosts: ProgramHosts {
            host: Arc::new(host),
            tracing: None,
        },
        factories: ProgramFactories::default(),
    });

    let mut all_diagnostics: Vec<DiagnosticRef> = Vec::new();
    if options.report_diagnostics {
        let source_file = program.get_source_file(&input_file_name);
        all_diagnostics.extend(program.get_syntactic_diagnostics(ctx.clone(), source_file));
        all_diagnostics.extend(program.get_config_file_parsing_diagnostics());
        all_diagnostics.extend(program.get_program_diagnostics());
    }

    let emit_only = if declaration {
        EmitOnly::Dts
    } else {
        EmitOnly::All
    };

    let output_text = RefCell::new(String::new());
    let source_map_text = RefCell::new(String::new());
    let has_output_text = RefCell::new(false);
    let has_source_map_text = RefCell::new(false);

    let result = program.emit(
        ctx.clone(),
        &mut EmitOptions {
            emit_only,
            force_emit: declaration,
            write_file: Some(Box::new(|file_name, text, _data| {
                if file_name.extension_is(".map") {
                    debug_assert!(
                        !*has_source_map_text.borrow(),
                        "Unexpected multiple source map outputs, file: {}",
                        file_name.as_string()
                    );
                    *source_map_text.borrow_mut() = text.to_string();
                    *has_source_map_text.borrow_mut() = true;
                } else {
                    debug_assert!(
                        !*has_output_text.borrow(),
                        "Unexpected multiple outputs, file: {}",
                        file_name.as_string()
                    );
                    *output_text.borrow_mut() = text.to_string();
                    *has_output_text.borrow_mut() = true;
                }
                Ok(())
            })),
            ..Default::default()
        },
    );
    // PORT: Go's `Emit` returns nil when the context is canceled; the Rust
    // port returns a default `EmitResult`, so cancellation is checked here.
    if ctx.is_cancelled() {
        return None;
    }

    // Diagnostics produced during emit (e.g. isolated declaration errors) are
    // always included, regardless of ReportDiagnostics.
    all_diagnostics.extend(result.diagnostics);

    debug_assert!(*has_output_text.borrow(), "Output generation failed");

    let mut nodes: FxHashMap<u32, Rc<tsc_ast::NodeArenaBuf>> = FxHashMap::default();
    for d in &all_diagnostics {
        if let Some(node) = tsc_ast::diagnostic::lock_diagnostic(d)
            .file()
            .and_then(|f| f.node)
        {
            nodes
                .entry(node.file_index())
                .or_insert_with(|| program.nodes(node.file_index()));
        }
    }

    Some(Output {
        output_text: output_text.into_inner(),
        diagnostics: all_diagnostics,
        source_map_text: source_map_text.into_inner(),
        nodes,
    })
}
