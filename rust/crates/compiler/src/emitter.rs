// Ported from tsc/internal/compiler/emitter.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `*ast.SourceFile`/`​*ast.Node` are `NodeId` values resolved through
// the per-file `Rc<ArenaCell>` arenas exposed by `BasicEmitHost`.
// Go's `sync.Pool` of `printer.EmitTextWriter`s becomes a fresh
// `TextWriter` per emitter — the port is single-threaded (PORTING-NOTES).
//
// PORT: `declarationTransformer` is a two-variant enum — the Go interface
// wraps `*DeclarationTransformer` and `*SupplementalReferencesTransformer`.
//
// PORT(deferred): `emitContext.Factory.ReleaseArenas()` has no Rust
// counterpart — the factory keeps its arenas until the emit context drops.
//
// PORT(deferred): the declaration `MapSourcePosition` handler maps
// positions through the source file's `SpanMap` but keeps the virtual
// source in the map — Go substitutes a `declarationMapSource` whose
// `FileName()` is the original (untransformed) name, and the Rust
// `MapSourcePosition` API returns `NodeId` sources only, so the original
// name cannot be swapped in. Positions are still mapped correctly.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::diagnostic::{DiagnosticRef, DiagnosticsCollection, new_compiler_diagnostic};
use tsc_ast::utilities::HasFileName;
use tsc_ast::{ArenaCell, Node, NodeId, is_in_js_file};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::{CompilerOptions, ModuleKind, NewLineKind};
use tsc_core::tristate::TS_TRUE;
use tsc_diagnostics::{self as diagnostics};
use tsc_outputpaths::{ForceEmitPaths, OutputPaths};
use tsc_printer::{
    EmitContext, EmitHost as PrinterEmitHost, EmitResolver, EmitTextWriter, PrintHandlers, Printer,
    PrinterOptions, TextWriter,
};
use tsc_tracing::{PHASE_EMIT, Tracing, push};
use tsc_transformers::declarations::supplementalreferences::SupplementalReferencesTransformer;
use tsc_transformers::declarations::transform::{
    DeclarationTransformer, new_declaration_transformer,
};
use tsc_transformers::{TransformOptions, Transformer};
use tsc_tspath::{self, RootedDirectoryPath, RootedFilePath};

use crate::emit_host::{
    BasicEmitHost, EmitHost as _, EmitOnly, EmitResult, SourceMapEmitResult, WriteFileData,
    WriteFileFn,
};

// ---------------------------------------------------------------------------
// emitter
// ---------------------------------------------------------------------------

/// `type emitter struct`.
pub struct Emitter<'p, 'w> {
    /// `host EmitHost` — installed by `set_host` (Go's `wg.Queue` body).
    host: Option<Rc<BasicEmitHost<'p>>>,
    /// `emitOnly`.
    emit_only: EmitOnly,
    /// `emitterDiagnostics`.
    emitter_diagnostics: DiagnosticsCollection,
    /// `writer` — a fresh `TextWriter` per emit (Go reuses pooled writers).
    writer: RefCell<Option<TextWriter>>,
    /// `paths`.
    paths: Option<OutputPaths>,
    /// `sourceFile`.
    source_file: NodeId,
    /// `emitResult`.
    emit_result: EmitResult,
    /// `forceEmit`.
    force_emit: bool,
    /// `writeFile`.
    write_file: Option<WriteFileFn<'w>>,
    /// `tr`.
    tr: Option<Arc<Tracing>>,
}

impl<'p, 'w> Emitter<'p, 'w> {
    /// The `emitter{...}` literal in `Program.Emit`.
    pub fn new(
        source_file: NodeId,
        emit_only: EmitOnly,
        force_emit: bool,
        write_file: Option<WriteFileFn<'w>>,
        tr: Option<Arc<Tracing>>,
    ) -> Emitter<'p, 'w> {
        Emitter {
            host: None,
            emit_only,
            emitter_diagnostics: DiagnosticsCollection::default(),
            writer: RefCell::new(None),
            paths: None,
            source_file,
            emit_result: EmitResult::default(),
            force_emit,
            write_file,
            tr,
        }
    }

    /// `emitter.host = host` — the emit host the program creates per file.
    pub fn set_host(&mut self, host: Rc<BasicEmitHost<'p>>) {
        self.host = Some(host);
    }

    /// `emitter.paths = outputpaths.GetOutputPathsFor(...)`.
    pub fn compute_paths(&mut self, force_dts_emit: bool, force_js_emit: bool, force_emit: bool) {
        let host = self.host.as_ref().expect("emit host installed");
        let nodes = host.emit_nodes(self.source_file.file_index());
        self.paths = Some(tsc_outputpaths::get_output_paths_for(
            self.source_file,
            host.options(),
            &**host,
            ForceEmitPaths {
                dts: force_dts_emit,
                js: force_js_emit,
                declaration_map: force_emit && self.emit_only == EmitOnly::Dts,
            },
            &nodes,
        ));
    }

    /// The `newLine`-configured pooled writer (`writerPool.Get()`).
    fn take_writer(&self) -> TextWriter {
        let host = self.host.as_ref().expect("emit host installed");
        let new_line = host.options().new_line.get_new_line_character();
        let mut writer = self
            .writer
            .borrow_mut()
            .take()
            .unwrap_or_else(|| TextWriter::new(new_line, 0));
        writer.clear();
        writer
    }

    fn put_writer(&self, writer: TextWriter) {
        *self.writer.borrow_mut() = Some(writer);
    }

    /// `(e *emitter) emit`.
    pub fn emit(&mut self) {
        let host = self.host.clone().expect("emit host installed");
        let path_key = {
            let nodes = host.emit_nodes(self.source_file.file_index());
            nodes[self.source_file]
                .as_source_file()
                .path_key()
                .as_string()
                .to_string()
        };
        let trace_done = push(
            self.tr.as_ref(),
            PHASE_EMIT,
            "emit",
            [("path".to_string(), serde_json::Value::from(path_key))]
                .into_iter()
                .collect(),
            true,
        );
        let emit_context = Rc::new(RefCell::new(EmitContext::new()));
        host.set_emit_context(emit_context.clone());
        self.emit_js_file(&host, emit_context.clone());
        self.emit_declaration_file(&host, emit_context);
        self.emit_result.diagnostics = self.emitter_diagnostics.get_diagnostics();
        trace_done();
    }

    /// `&e.emitResult` — consumed by `CombineEmitResults`.
    pub fn emit_result(&mut self) -> EmitResult {
        std::mem::take(&mut self.emit_result)
    }

    /// `getDeclarationTransformers` — the two-element Go slice becomes a
    /// `[DeclarationTransformer; 2]`.
    fn get_declaration_transformers<'a>(
        &self,
        host: &'a Rc<BasicEmitHost<'p>>,
        emit_resolver: &Rc<RefCell<tsc_checker::emitresolver::EmitResolver>>,
        source_file: NodeId,
        declaration_file_path: &RootedFilePath,
        symbol_arena: &'a Rc<RefCell<Vec<tsc_ast::Symbol>>>,
        nodes: &[Node],
    ) -> [DeclarationTransformerKind<'a>; 2] {
        let force_dts_emit = self.emit_only == EmitOnly::BuilderSignature
            || self.force_emit && self.emit_only == EmitOnly::Dts;
        [
            DeclarationTransformerKind::Declaration(new_declaration_transformer(
                host.clone(),
                emit_resolver.clone(),
                host.options(),
                declaration_file_path.clone(),
                Some(&**symbol_arena),
            )),
            DeclarationTransformerKind::Supplemental(SupplementalReferencesTransformer::new(
                host.clone(),
                source_file,
                declaration_file_path.clone(),
                force_dts_emit,
                nodes,
            )),
        ]
    }

    /// `runScriptTransformers`.
    fn run_script_transformers<'a>(
        &self,
        host: &'a Rc<BasicEmitHost<'p>>,
        emit_context: &Rc<RefCell<EmitContext>>,
        emit_resolver: &Rc<RefCell<tsc_checker::emitresolver::EmitResolver>>,
        source_file: NodeId,
        symbol_arena: &'a Rc<RefCell<Vec<tsc_ast::Symbol>>>,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        let trace_done = push(
            self.tr.as_ref(),
            PHASE_EMIT,
            "transformNodes",
            [(
                "path".to_string(),
                serde_json::Value::from(
                    nodes[source_file]
                        .as_source_file()
                        .path_key()
                        .as_string()
                        .to_string(),
                ),
            )]
            .into_iter()
            .collect(),
            false,
        );
        let mut source_file = Some(source_file);
        let options = host.options();
        // JS files don't use reference calculations as they don't do import elision, no need to calculate it
        let import_elision_enabled =
            options.verbatim_module_syntax != TS_TRUE && !is_in_js_file(source_file, nodes);
        let reference_resolver: Rc<RefCell<dyn ReferenceResolver + '_>>;
        if import_elision_enabled
            || options.get_jsx_transform_enabled()
                && nodes[source_file.expect("source file")]
                    .as_source_file()
                    .language_variant
                    == LanguageVariant::Jsx
            || !options.get_isolated_modules()
            || options.emit_decorator_metadata == TS_TRUE
        {
            reference_resolver =
                Rc::new(RefCell::new(EmitResolverAsReference(emit_resolver.clone())));
        } else {
            reference_resolver = Rc::new(RefCell::new(
                tsc_binder::referenceresolver::new_reference_resolver(options, Default::default()),
            ));
        }
        let get_module_format = |file: &dyn HasFileName| -> ModuleKind {
            host.program().get_emit_module_format_of_file(file)
        };
        // `TransformOptions<'a>` is an ordinary local: the transformer
        // constructors retain only the *fields* they need (`Rc` clones and
        // `&'a` field values), not `&'a TransformOptions<'a>` itself, so
        // `opts` drops with this scope — leaking it here would pin the
        // `emit_resolver`'s `Rc`s (and, transitively, its `NodeBuilder`
        // arenas) for the rest of the process.
        let opts = TransformOptions {
            context: Some(emit_context.clone()),
            compiler_options: Some(options),
            resolver: Some(reference_resolver),
            emit_resolver: Some(emit_resolver.clone()),
            get_emit_module_format_of_file: Some(&get_module_format),
            symbols: Some(&**symbol_arena),
        };
        for transformer in get_script_transformers(&opts, source_file.expect("source file"), nodes)
        {
            if let Some(file) = source_file {
                source_file = transformer.transform_source_file(nodes, file);
            }
        }
        trace_done();
        source_file
    }

    /// `runDeclarationTransformers`.
    fn run_declaration_transformers<'a>(
        &self,
        host: &'a Rc<BasicEmitHost<'p>>,
        emit_resolver: &Rc<RefCell<tsc_checker::emitresolver::EmitResolver>>,
        source_file: NodeId,
        declaration_file_path: &RootedFilePath,
        symbol_arena: &'a Rc<RefCell<Vec<tsc_ast::Symbol>>>,
        nodes: &mut Vec<Node>,
    ) -> (Option<NodeId>, Vec<DiagnosticRef>) {
        let trace_done = push(
            self.tr.as_ref(),
            PHASE_EMIT,
            "transformNodes",
            [(
                "path".to_string(),
                serde_json::Value::from(
                    nodes[source_file]
                        .as_source_file()
                        .path_key()
                        .as_string()
                        .to_string(),
                ),
            )]
            .into_iter()
            .collect(),
            false,
        );
        let mut diags: Vec<DiagnosticRef> = Vec::new();
        let mut source_file = Some(source_file);
        for transformer in self.get_declaration_transformers(
            host,
            emit_resolver,
            source_file.expect("source file"),
            declaration_file_path,
            symbol_arena,
            nodes,
        ) {
            match transformer {
                DeclarationTransformerKind::Declaration(tx) => {
                    if let Some(file) = source_file {
                        source_file = tx.transform_source_file(nodes, file);
                    }
                    diags.extend(tx.get_diagnostics());
                }
                DeclarationTransformerKind::Supplemental(tx) => {
                    if let Some(file) = source_file {
                        source_file = Some(tx.transform_source_file(file, nodes));
                    }
                    diags.extend(tx.get_diagnostics());
                }
            }
        }
        trace_done();
        (source_file, diags)
    }

    /// `emitJSFile`.
    fn emit_js_file<'a>(
        &mut self,
        host: &'a Rc<BasicEmitHost<'p>>,
        emit_context: Rc<RefCell<EmitContext>>,
    ) {
        // Declare before `emit_resolver` so the arena outlives the
        // `&'a` borrows the resolver/transform options capture.
        let symbol_arena = host.checker().borrow().symbol_arena.clone();
        let emit_resolver = host.new_emit_resolver_for_context(emit_context.clone());
        let options = host.options();
        let js_file_path = self
            .paths
            .as_ref()
            .map(|p| p.js_file_path().clone())
            .unwrap_or_default();
        let source_map_file_path = self
            .paths
            .as_ref()
            .map(|p| p.source_map_file_path().clone())
            .unwrap_or_default();

        if self.emit_only != EmitOnly::All && self.emit_only != EmitOnly::Js
            || js_file_path.as_string().is_empty()
        {
            return;
        }

        if !self.force_emit && (options.no_emit == TS_TRUE || host.is_emit_blocked(&js_file_path)) {
            self.emit_result.emit_skipped = true;
            return;
        }

        let trace_done = push(
            self.tr.as_ref(),
            PHASE_EMIT,
            "emitJsFileOrBundle",
            [(
                "jsFilePath".to_string(),
                serde_json::Value::from(js_file_path.as_string().to_string()),
            )]
            .into_iter()
            .collect(),
            true,
        );

        let mut nodes_mut = host.emit_nodes_mut(self.source_file.file_index());
        let source_file = self.run_script_transformers(
            host,
            &emit_context,
            &emit_resolver,
            self.source_file,
            &symbol_arena,
            &mut nodes_mut,
        );

        if let Some(source_file) = source_file {
            let printer_options = PrinterOptions {
                remove_comments: options.remove_comments == TS_TRUE,
                new_line: options.new_line,
                no_emit_helpers: options.no_emit_helpers == TS_TRUE,
                source_map: options.source_map == TS_TRUE,
                inline_source_map: options.inline_source_map == TS_TRUE,
                inline_sources: options.inline_sources == TS_TRUE,
                target: options.target,
                ..Default::default()
            };

            // create a printer to print the nodes
            let mut emit_context_mut = emit_context.borrow_mut();
            let symbols = symbol_arena.borrow();
            let mut writer = self.take_writer();
            // Compute before `Printer` takes the `&mut` arena borrow.
            let should_emit_source_maps = should_emit_source_maps(options, source_file, &nodes_mut);
            let mut printer = Printer::new(
                printer_options,
                PrintHandlers::default(),
                &mut emit_context_mut,
                &mut nodes_mut,
                &symbols,
            );

            self.print_source_file(
                host,
                &js_file_path,
                &source_map_file_path,
                source_file,
                &mut printer,
                options,
                should_emit_source_maps,
                &mut writer,
            );
            drop(printer);
            drop(symbols);
            drop(emit_context_mut);
            self.put_writer(writer);
        }
        drop(nodes_mut);
        trace_done();
    }

    /// `emitDeclarationFile`.
    fn emit_declaration_file<'a>(
        &mut self,
        host: &'a Rc<BasicEmitHost<'p>>,
        emit_context: Rc<RefCell<EmitContext>>,
    ) {
        let symbol_arena = host.checker().borrow().symbol_arena.clone();
        let emit_resolver = host.new_emit_resolver_for_context(emit_context.clone());
        let options = host.options();
        let declaration_file_path = self
            .paths
            .as_ref()
            .map(|p| p.declaration_file_path().clone())
            .unwrap_or_default();
        let declaration_map_path = self
            .paths
            .as_ref()
            .map(|p| p.declaration_map_path().clone())
            .unwrap_or_default();

        if self.emit_only == EmitOnly::Js || declaration_file_path.as_string().is_empty() {
            return;
        }
        let emit_declaration_map =
            self.emit_only != EmitOnly::BuilderSignature && options.declaration_map == TS_TRUE;
        let content_mapped_source = self.source_file;

        let trace_done = push(
            self.tr.as_ref(),
            PHASE_EMIT,
            "emitDeclarationFileOrBundle",
            [(
                "declarationFilePath".to_string(),
                serde_json::Value::from(declaration_file_path.as_string().to_string()),
            )]
            .into_iter()
            .collect(),
            true,
        );

        let mut nodes_mut = host.emit_nodes_mut(self.source_file.file_index());
        let (source_file, diags) = self.run_declaration_transformers(
            host,
            &emit_resolver,
            self.source_file,
            &declaration_file_path,
            &symbol_arena,
            &mut nodes_mut,
        );

        for elem in &diags {
            // Add declaration transform diagnostics to emit diagnostics
            self.emitter_diagnostics.add(elem);
        }

        if !self.force_emit
            && self.emit_only != EmitOnly::BuilderSignature
            && (options.no_emit == TS_TRUE || host.is_emit_blocked(&declaration_file_path))
        {
            self.emit_result.emit_skipped = true;
            drop(nodes_mut);
            trace_done();
            return;
        }

        let decl_blocked =
            !diags.is_empty() && !self.force_emit && self.emit_only != EmitOnly::BuilderSignature;
        if decl_blocked {
            self.emit_result.emit_skipped = true;
            drop(nodes_mut);
            trace_done();
            return;
        }

        if let Some(source_file) = source_file {
            let printer_options = PrinterOptions {
                remove_comments: options.remove_comments == TS_TRUE,
                new_line: options.new_line,
                no_emit_helpers: true,
                // Module: 			   options.Module, // NYI
                // ModuleResolution:   options.ModuleResolution, // NYI
                target: options.get_emit_script_target(),
                source_map: emit_declaration_map,
                inline_source_map: options.inline_source_map == TS_TRUE,
                // InlineSources:       options.InlineSources.IsTrue(), // ignored, per strada
                // ExtendedDiagnostics: options.ExtendedDiagnostics.IsTrue(), // NYI
                only_print_jsdoc_style: true,
                omit_brace_source_map_positions: true,
                ..Default::default()
            };

            // create a printer to print the nodes
            let mut print_handlers = PrintHandlers::default();
            let content_mapped_file_name = nodes_mut[content_mapped_source]
                .as_source_file()
                .file_name()
                .clone();
            let span_map = nodes_mut[content_mapped_source].as_source_file().span_map();
            if emit_declaration_map {
                if let Some(span_map) = span_map {
                    // `originalSource := newDeclarationMapSource(contentMappedSource)` —
                    // a synthetic `sourcemap.Source` keyed on the original file
                    // carrying its pre-mapping text and line map.
                    let (original_file_name, original_text) = {
                        let sf = nodes_mut[content_mapped_source].as_source_file();
                        (
                            sf.original_file_name(&nodes_mut).clone(),
                            sf.original_text().to_string(),
                        )
                    };
                    let original_source = std::rc::Rc::new(tsc_printer::SyntheticSourceFile {
                        line_map: tsc_core::core::compute_ecma_line_starts(&original_text).to_vec(),
                        text: original_text,
                        file_name: original_file_name,
                    });
                    print_handlers.map_source_position = Some(Box::new(
                        move |source_name: &tsc_tspath::RootedFilePath,
                              source: tsc_printer::SourceMapSource,
                              pos: i32|
                              -> (
                            Option<tsc_printer::SourceMapSource>,
                            Option<i32>,
                        ) {
                            // `if source.FileName() != contentMappedSource.FileName()`
                            if *source_name != content_mapped_file_name {
                                return (Some(source), Some(pos));
                            }
                            let mapped = tsc_spanmap::SpanMap::virtual_to_original_position_exact(
                                Some(&span_map),
                                pos,
                            );
                            match mapped {
                                (pos, true) => (
                                    Some(tsc_printer::SourceMapSource::Synthetic(
                                        original_source.clone(),
                                    )),
                                    Some(pos),
                                ),
                                (_, false) => (None, None),
                            }
                        },
                    ));
                }
            }

            let mut emit_context_mut = emit_context.borrow_mut();
            let symbols = symbol_arena.borrow();

            let declaration_map_options = CompilerOptions {
                source_map: if emit_declaration_map {
                    TS_TRUE
                } else {
                    tsc_core::tristate::TS_FALSE
                },
                source_root: options.source_root.clone(),
                map_root: options.map_root.clone(),
                // Explicitly do not pass through either inline option.
                ..Default::default()
            };

            let mut writer = self.take_writer();
            // Compute before `Printer` takes the `&mut` arena borrow.
            let should_emit_maps =
                should_emit_source_maps(&declaration_map_options, source_file, &nodes_mut);
            let mut printer = Printer::new(
                printer_options,
                print_handlers,
                &mut emit_context_mut,
                &mut nodes_mut,
                &symbols,
            );
            self.print_source_file(
                host,
                &declaration_file_path,
                &declaration_map_path,
                source_file,
                &mut printer,
                &declaration_map_options,
                should_emit_maps,
                &mut writer,
            );
            drop(printer);
            drop(symbols);
            drop(emit_context_mut);
            self.put_writer(writer);
        }
        drop(nodes_mut);
        trace_done();
    }

    /// `printSourceFile`.
    ///
    /// PORT: `emitContext` is not a parameter — Go passes it for
    /// `emitContext.Factory.ReleaseArenas()`, which has no Rust counterpart
    /// (see file header), and the `Printer` already holds the `&mut` borrow.
    #[allow(clippy::too_many_arguments)]
    fn print_source_file<'a>(
        &mut self,
        host: &'a BasicEmitHost<'p>,
        js_file_path: &RootedFilePath,
        source_map_file_path: &RootedFilePath,
        source_file: NodeId,
        printer: &mut Printer<'_>,
        map_options: &CompilerOptions,
        should_emit_source_maps: bool,
        writer: &mut TextWriter,
    ) {
        // !!! sourceMapGenerator
        let options = host.options();
        let mut source_map_generator: Option<tsc_sourcemap::Generator> = if should_emit_source_maps
        {
            Some(tsc_sourcemap::Generator::new(
                js_file_path.base_name(),
                &get_source_root(map_options),
                // `self.source_file`, not `source_file`: the transformed
                // root is minted in the checked-out arena and is out of
                // bounds for `emit_nodes` (same issue as below at
                // `get_source_mapping_url`). Only `file_name()` is read,
                // which is identical on the original node.
                self.get_source_map_directory(
                    host,
                    map_options,
                    js_file_path,
                    Some(self.source_file),
                ),
                host.case_sensitivity(),
            ))
        } else {
            None
        };

        printer.write(
            Some(source_file),
            Some(source_file),
            writer,
            source_map_generator.as_mut(),
        );
        // PORT(deferred): `emitContext.Factory.ReleaseArenas()` — no Rust
        // counterpart (see file header).

        let mut source_map_url_pos = -1;
        if let Some(source_map_generator) = source_map_generator.as_mut() {
            if map_options.source_map == TS_TRUE || map_options.inline_source_map == TS_TRUE {
                self.emit_result.source_maps.push(SourceMapEmitResult {
                    input_source_file_names: source_map_generator.sources().to_vec(),
                    source_map: source_map_generator.raw_source_map(),
                    generated_file: js_file_path.as_string().to_string(),
                });
            }

            // `self.source_file`, not `source_file`: the transformed root is
            // minted inside the checked-out arena, so reads via
            // `emit_nodes` (which see the pre-transform clone) would index
            // out of bounds. The source-map path only needs `file_name()`,
            // which is identical on the original node.
            let source_mapping_url = self.get_source_mapping_url(
                host,
                map_options,
                source_map_generator,
                js_file_path,
                source_map_file_path,
                Some(self.source_file),
            );

            if !source_mapping_url.is_empty() {
                if !writer.is_at_start_of_line() {
                    writer.raw_write(if options.new_line == NewLineKind::CRLF {
                        "\r\n"
                    } else {
                        "\n"
                    });
                }
                source_map_url_pos = writer.get_text_pos();
                writer.write_comment("//# sourceMappingURL=");
                writer.write_comment(&source_mapping_url);
            }

            // Write the source map
            if !source_map_file_path.as_string().is_empty() {
                let source_map = source_map_generator.to_json_string();
                let mut data = WriteFileData {
                    source_file: Some(self.source_file),
                    ..Default::default()
                };
                match self.write_text(host, source_map_file_path, &source_map, &mut data) {
                    Err(err) => {
                        self.emitter_diagnostics.add(&new_compiler_diagnostic(
                            &diagnostics::Could_not_write_file_0_Colon_1,
                            &[js_file_path.as_string().to_string(), err],
                        ));
                    }
                    Ok(()) => {
                        self.emit_result
                            .emitted_files
                            .push(source_map_file_path.clone());
                    }
                }
            }
        } else {
            writer.write_line();
        }

        // Write the output file
        let mut text = writer.get_text();
        if options.emit_bom == TS_TRUE {
            text =
                String::from_utf8_lossy(&tsc_stringutil::add_utf8_byte_order_mark(text.as_bytes()))
                    .into_owned();
        }
        let mut data = WriteFileData {
            source_map_url_pos,
            diagnostics: self.emitter_diagnostics.get_diagnostics(),
            source_file: Some(self.source_file),
            ..Default::default()
        };
        let result = self.write_text(host, js_file_path, &text, &mut data);
        let skipped_dts_write = data.skipped_dts_write;
        match result {
            Err(err) => {
                self.emitter_diagnostics.add(&new_compiler_diagnostic(
                    &diagnostics::Could_not_write_file_0_Colon_1,
                    &[js_file_path.as_string().to_string(), err],
                ));
            }
            Ok(()) if !skipped_dts_write => {
                self.emit_result.emitted_files.push(js_file_path.clone());
            }
            _ => {}
        }

        // Reset state
        writer.clear();
    }

    /// `writeText`.
    fn write_text(
        &self,
        host: &BasicEmitHost<'p>,
        file_name: &RootedFilePath,
        text: &str,
        data: &mut WriteFileData,
    ) -> Result<(), String> {
        if let Some(write_file) = &self.write_file {
            return write_file(file_name, text, data);
        }
        host.write_file(file_name, text).map_err(|e| e.to_string())
    }

    /// `getMapRootDirectory`.
    fn get_map_root_directory(
        &self,
        host: &BasicEmitHost<'p>,
        map_root: &tsc_tspath::SourceMapLocation,
        source_file: Option<NodeId>,
    ) -> RootedDirectoryPath {
        let mut source_map_directory =
            map_root.resolve_directory(host.common_source_directory(), host.base_directory());
        if let Some(source_file) = source_file {
            let nodes = host.emit_nodes(source_file.file_index());
            source_map_directory = tsc_outputpaths::get_source_file_name_in_new_dir(
                nodes[source_file].as_source_file().file_name(),
                &source_map_directory,
                host.common_source_directory(),
                host.case_sensitivity(),
            )
            .directory();
        }
        source_map_directory
    }

    /// `getSourceMapDirectory`.
    fn get_source_map_directory(
        &self,
        host: &BasicEmitHost<'p>,
        map_options: &CompilerOptions,
        file_path: &RootedFilePath,
        source_file: Option<NodeId>,
    ) -> RootedDirectoryPath {
        if !map_options.source_root.as_string().is_empty() {
            return host.common_source_directory().clone();
        }
        if !map_options.map_root.as_string().is_empty() {
            return self.get_map_root_directory(host, &map_options.map_root, source_file);
        }
        file_path.directory()
    }

    /// `getSourceMappingURL`.
    fn get_source_mapping_url(
        &self,
        host: &BasicEmitHost<'p>,
        map_options: &CompilerOptions,
        source_map_generator: &mut tsc_sourcemap::Generator,
        file_path: &RootedFilePath,
        source_map_file_path: &RootedFilePath,
        source_file: Option<NodeId>,
    ) -> String {
        if map_options.inline_source_map == TS_TRUE {
            // Encode the sourceMap into the sourceMap url
            return source_map_generator.base64_data_url();
        }

        let source_map_file = source_map_file_path.base_name();
        if !map_options.map_root.as_string().is_empty() {
            let source_map_directory =
                self.get_map_root_directory(host, &map_options.map_root, source_file);
            let source_map_file_path = source_map_directory.resolve_file(source_map_file);
            if map_options.map_root.is_relative() {
                return tsc_stringutil::encode_uri(
                    tsc_tspath::get_relative_path_to_directory_or_url(
                        file_path.directory().as_string(),
                        source_map_file_path.as_string(),
                        true,
                        host.case_sensitivity(),
                    )
                    .as_bytes(),
                );
            }
            return tsc_stringutil::encode_uri(source_map_file_path.as_string().as_bytes());
        }
        tsc_stringutil::encode_uri(source_map_file.as_bytes())
    }
}

/// `type declarationTransformer interface`.
enum DeclarationTransformerKind<'a> {
    Declaration(DeclarationTransformer<'a>),
    Supplemental(SupplementalReferencesTransformer<'a>),
}

/// `getModuleTransformer`.
fn get_module_transformer<'a>(opts: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    match opts
        .compiler_options
        .expect("compiler options")
        .get_emit_module_kind()
    {
        ModuleKind::Preserve => {
            // `ESModuleTransformer` contains logic for preserving CJS input syntax in `--module preserve`
            tsc_transformers::moduletransforms::esmodule::new_es_module_transformer(opts)
        }
        ModuleKind::ESNext
        | ModuleKind::ES2022
        | ModuleKind::ES2020
        | ModuleKind::ES2015
        | ModuleKind::Node20
        | ModuleKind::Node18
        | ModuleKind::Node16
        | ModuleKind::NodeNext
        | ModuleKind::CommonJS => {
            tsc_transformers::moduletransforms::impliedmodule::new_implied_module_transformer(opts)
        }
        _ => tsc_transformers::moduletransforms::commonjsmodule::new_common_js_module_transformer(
            opts,
        ),
    }
}

/// `getScriptTransformers`.
fn get_script_transformers<'a>(
    opts: &TransformOptions<'a>,
    source_file: NodeId,
    nodes: &[Node],
) -> Vec<Transformer<'a>> {
    // `emitResolver == nil || emitResolver.EmitContext() == nil` cannot occur:
    // the emitter mints both before calling.
    let mut tx: Vec<Transformer<'a>> = Vec::new();
    let options = opts.compiler_options.expect("compiler options");

    // JS files don't use reference calculations as they don't do import elision, no need to calculate it
    let import_elision_enabled =
        options.verbatim_module_syntax != TS_TRUE && !is_in_js_file(Some(source_file), nodes);
    let jsx_transform_enabled = options.get_jsx_transform_enabled()
        && nodes[source_file].as_source_file().language_variant == LanguageVariant::Jsx;

    // transform TypeScript syntax
    {
        // use type nodes to add metadata decorators
        if options.emit_decorator_metadata == TS_TRUE {
            if let Some(t) =
                tsc_transformers::tstransforms::metadata::new_metadata_transformer(opts)
            {
                tx.push(t);
            }
        }

        // erase types
        if let Some(t) =
            tsc_transformers::tstransforms::typeeraser::new_type_eraser_transformer(opts)
        {
            tx.push(t);
        }

        // elide imports
        if import_elision_enabled {
            if let Some(t) =
                tsc_transformers::tstransforms::importelision::new_import_elision_transformer(opts)
            {
                tx.push(t);
            }
        }

        // transform `enum`, `namespace`, and parameter properties
        if let Some(t) =
            tsc_transformers::tstransforms::runtimesyntax::new_runtime_syntax_transformer(opts)
        {
            tx.push(t);
        }

        if options.experimental_decorators == TS_TRUE {
            if let Some(t) =
                tsc_transformers::tstransforms::legacydecorators::new_legacy_decorators_transformer(
                    opts,
                )
            {
                tx.push(t);
            }
        }
    }

    if jsx_transform_enabled {
        if let Some(t) = tsc_transformers::jsxtransforms::new_jsx_transformer(opts) {
            tx.push(t);
        }
    }

    if let Some(downleveler) = tsc_transformers::estransforms::definitions::get_es_transformer(opts)
    {
        tx.push(downleveler);
    }

    if let Some(t) = tsc_transformers::estransforms::usestrict::new_use_strict_transformer(opts) {
        tx.push(t);
    }

    // transform module syntax
    if let Some(t) = get_module_transformer(opts) {
        tx.push(t);
    }

    // inlining (formerly done via substitutions)
    if !options.get_isolated_modules() {
        if let Some(t) =
            tsc_transformers::inliners::constenum::new_const_enum_inlining_transformer(opts)
        {
            tx.push(t);
        }
    }
    tx
}

/// `EmitResolverAsReference` — `Rc<RefCell<dyn EmitResolver>>` cannot
/// coerce to `Rc<RefCell<dyn ReferenceResolver>>` (`RefCell` is invariant),
/// so the emit resolver is wrapped and the six `ReferenceResolver` methods
/// forwarded.
struct EmitResolverAsReference<'a>(Rc<RefCell<dyn EmitResolver + 'a>>);

impl<'a> ReferenceResolver for EmitResolverAsReference<'a> {
    fn get_referenced_export_container(
        &mut self,
        node: NodeId,
        prefix_locals: bool,
        nodes: &[Node],
        symbols: &std::cell::RefCell<Vec<tsc_ast::Symbol>>,
    ) -> Option<NodeId> {
        self.0
            .borrow_mut()
            .get_referenced_export_container(node, prefix_locals, nodes, symbols)
    }
    fn get_referenced_import_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &std::cell::RefCell<Vec<tsc_ast::Symbol>>,
    ) -> Option<NodeId> {
        self.0
            .borrow_mut()
            .get_referenced_import_declaration(node, nodes, symbols)
    }
    fn get_referenced_value_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &std::cell::RefCell<Vec<tsc_ast::Symbol>>,
    ) -> Option<NodeId> {
        self.0
            .borrow_mut()
            .get_referenced_value_declaration(node, nodes, symbols)
    }
    fn get_referenced_value_declarations(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &std::cell::RefCell<Vec<tsc_ast::Symbol>>,
    ) -> Vec<NodeId> {
        self.0
            .borrow_mut()
            .get_referenced_value_declarations(node, nodes, symbols)
    }
    fn get_element_access_expression_name(&mut self, expression: Option<NodeId>) -> String {
        self.0
            .borrow_mut()
            .get_element_access_expression_name(expression)
    }
    fn get_referenced_member_value_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &std::cell::RefCell<Vec<tsc_ast::Symbol>>,
    ) -> Option<NodeId> {
        self.0
            .borrow_mut()
            .get_referenced_member_value_declaration(node, nodes, symbols)
    }

    fn resolve_node(&mut self, id: NodeId, nodes: &[Node]) -> Option<Node> {
        self.0.borrow_mut().resolve_node(id, nodes)
    }
}

/// `shouldEmitSourceMaps`.
fn should_emit_source_maps(
    map_options: &CompilerOptions,
    source_file: NodeId,
    nodes: &[Node],
) -> bool {
    (map_options.source_map == TS_TRUE || map_options.inline_source_map == TS_TRUE)
        && !nodes[source_file]
            .as_source_file()
            .file_name()
            .extension_is(tsc_tspath::EXTENSION_JSON)
}

/// `getSourceRoot`.
fn get_source_root(map_options: &CompilerOptions) -> String {
    // Normalize source root and make sure it has trailing "/" so that it can be used to combine paths with the
    // relative paths of the sources list in the sourcemap
    let source_root = map_options.source_root.as_string();
    if !source_root.is_empty() {
        return tsc_tspath::ensure_trailing_directory_separator(source_root).into_owned();
    }
    source_root.to_string()
}
