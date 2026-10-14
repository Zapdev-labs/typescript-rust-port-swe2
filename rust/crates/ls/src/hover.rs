// Ported from tsc/internal/ls/hover.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - `*ast.Symbol`/`*ast.Node`/`*checker.Signature`/`*checker.Type` are
//   `SymbolId`/`NodeId`/`SignatureId`/`TypeId`. Symbol fields are read via
//   `c.symbol_arena.get_ref(id)` (the checker's shared symbol arena); node
//   fields via `program.nodes(id.file_index())` snapshots — a node's owning
//   arena may differ from the hover file's arena, so `arena_of` is used at
//   every dereference.
// - `documentationLocationMapper` is
//   `&dyn Fn(NodeId, TextRange) -> (lsproto::Location, Fidelity)`.
// - Go's closures inside `getQuickInfoAndDeclarationAtLocation`
//   (`writeTypeClassified`, `writeSymbol`, ...) become methods on
//   `QuickInfoState`, which holds the captured state.
// - `getDeclarationsFromLocation`/`getDeclarationsFromObjectLiteralElement`/
//   `getDeclarationNameForKeyword` live in `definition.go` (sibling-owned);
//   local copies are kept here.
// - `sourceFileRangeToLSPLocationForFeature`/`getMappedLocation`/
//   `tryGetSourcePosition`/`getScript` are already ported in
//   `crates/ls/src/source_map.rs`; `documentationLocationMapper` delegates
//   to them.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, ArenaCheckout, Kind, Node, NodeFlags, NodeId, SemanticMeaning, SymbolFlags, SymbolId};
use tsc_ast::checkflags::CheckFlags;
use tsc_checker::checker_core::Checker;
use tsc_checker::nodebuilder::{VerbosityContext, new_node_builder_ex};
use tsc_checker::types::{
    SignatureId, SignatureKind, SymbolFormatFlags, TypeFormatFlags, TypeId,
};
use tsc_collections::Set;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::options_generated::NewLineKind;
use tsc_core::text::TextRange;
use tsc_lsconv::converters::source_file_script;
use tsc_lsproto as lsproto;
use tsc_lsutil::symbol_display::{get_symbol_kind, get_symbol_modifiers, ScriptElementKind, ScriptElementKindModifier};
use tsc_nodebuilder as nodebuilder;
use tsc_printer::{
    EmitContext, EmitFlags, EmitTextWriter, PrintHandlers, Printer, PrinterOptions,
};
use tsc_spanmap::{Feature, Fidelity};

use crate::api::Error;
use crate::displaypartswriter::{DisplayPartsWriter, new_display_parts_writer};
use crate::hovericon::{build_vs_hover_raw_content, get_vs_hover_image_id};
use crate::languageservice::LanguageService;
use crate::utilities::{create_range_from_node, get_container_node, get_containing_object_literal_element, get_meaning_from_location, is_in_comment};

/// `symbolFormatFlags`.
const SYMBOL_FORMAT_FLAGS: SymbolFormatFlags = SymbolFormatFlags(
    SymbolFormatFlags::WRITE_TYPE_PARAMETERS_OR_ARGUMENTS.0
        | SymbolFormatFlags::USE_ONLY_EXTERNAL_ALIASING.0
        | SymbolFormatFlags::ALLOW_ANY_NODE_KIND.0
        | SymbolFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE.0,
);

/// `typeFormatFlags`.
const TYPE_FORMAT_FLAGS: TypeFormatFlags = TypeFormatFlags(
    TypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE.0
        | TypeFormatFlags::USE_INSTANTIATION_EXPRESSIONS.0,
);

/// `documentationLocationMapper` — maps a `SourceFile` (`NodeId`) + range to
/// an LSP location, following declaration source maps.
type DocumentationLocationMapper<'a> =
    dyn Fn(NodeId, TextRange) -> (lsproto::Location, Fidelity) + 'a;

/// `noMappedLocation` (jsdoc.go) — the mapper used when no mapping context
/// is available.
pub(crate) fn no_mapped_location(_file: NodeId, _range: TextRange) -> (lsproto::Location, Fidelity) {
    (lsproto::Location::default(), Fidelity::None)
}

impl<'h> LanguageService<'h> {
    /// `ProvideHover`.
    pub(crate) fn provide_hover(
        &self,
        ctx: &Context,
        params: &lsproto::HoverParams,
    ) -> Result<lsproto::HoverResponse, Error> {
        let caps = lsproto::get_client_capabilities(ctx);
        let content_format =
            lsproto::preferred_markup_kind(&caps.text_document.hover.content_format);

        let verbosity_level = params.verbosity_level.unwrap_or(0);

        let (program, file) = self.get_program_and_file(&params.text_document.uri);
        // PORT: `positions` holds `SourceFileScript`s that borrow the node's
        // arena, so `nodes` must outlive the projection loop.
        let nodes = program.nodes(file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            file,
            &nodes,
            params.position,
            Feature::Hover,
        );
        let mut hovers: Vec<lsproto::Hover> = Vec::new();
        for projection in &positions {
            if !projection.fidelity.is_single_segment() {
                continue;
            }
            let file = projection.script.file;
            let position = projection.position;
            let node = {
                let mut nodes = program.nodes_mut(file.file_index());
                tsc_astnav::tokens::get_touching_property_name(&mut nodes, file, position)
            }
            .expect("GetTouchingPropertyName should return a node");
            let skip = {
                let nodes = program.arena_of(node);
                ast::is_source_file(&nodes[node])
                    || ast::is_property_access_or_qualified_name(&nodes[node]) && {
                        drop(nodes);
                        let mut nodes = program.nodes_mut(file.file_index());
                        is_in_comment(&mut nodes, file, position, Some(node)).is_none()
                    }
            };
            if skip {
                // Avoid giving quickInfo for the sourceFile as a whole or
                // inside the comment of a/**/.b
                continue;
            }
            let (checker, done) = program.get_type_checker_for_file(ctx.clone(), file);
            let range_node = get_node_for_quick_info(&program, node);
            let symbol = get_symbol_at_location_for_quick_info(&program, &checker, range_node);

            // Always create VerbosityContext for hover so that canExpandSymbol can signal
            // canIncreaseVerbosity even at Level 0. The nodebuilder also detects expandable
            // types at Level 0 via shouldExpandType (maxExpansionDepth = 0).
            let mut max_trunc_len = self.user_preferences().maximum_hover_length;
            if max_trunc_len <= 0 {
                max_trunc_len = 500;
            }
            let mut vc = VerbosityContext {
                level: verbosity_level,
                max_truncation_length: max_trunc_len,
                ..Default::default()
            };

            let vs_capability = caps.vs_supports_visual_studio_extensions;
            let (quick_info, documentation, vs_documentation, quick_info_runs) = self
                .get_quick_info_and_documentation_for_symbol(
                    &program,
                    &checker,
                    symbol,
                    range_node,
                    content_format.clone(),
                    &mut vc,
                    vs_capability,
                );
            if quick_info.is_empty() {
                done();
                continue;
            }
            let (range_file, text_range) = {
                let nodes = program.arena_of(range_node);
                let range_file = ast::get_source_file_of_node(Some(range_node), &nodes)
                    .expect("source file of node");
                let text_range = crate::findallreferences::get_range_of_node(
                    range_node,
                    Some(range_file),
                    None,
                    &nodes,
                );
                (range_file, text_range)
            };
            let (hover_range, hover_fidelity) = {
                let nodes = program.nodes(range_file.file_index());
                self.converters.to_lsp_range_for_feature(
                    &source_file_script(range_file, &nodes),
                    text_range,
                    Feature::Hover,
                )
            };

            let content = if content_format == lsproto::MarkupKind::Markdown {
                format_quick_info(&quick_info) + &documentation
            } else {
                quick_info.clone() + &documentation
            };

            let mut hover = lsproto::Hover {
                contents: lsproto::MarkupContentOrStringOrMarkedStringWithLanguageOrMarkedStrings {
                    markup_content: Some(lsproto::MarkupContent {
                        kind: content_format.clone(),
                        value: content,
                    }),
                    ..Default::default()
                },
                ..Default::default()
            };
            if hover_fidelity.is_single_segment() {
                hover.range = Some(hover_range);
            }

            if caps.experimental.hover_verbosity_level {
                hover.can_increase_verbosity = vc.can_increase_verbosity && !vc.truncated;
            }

            // Clients that support Visual Studio extensions (e.g. VS itself, when Corsa/Native TS Preview is
            // enabled) render `_vs_rawContent` in place of `contents`. Without it, VS shows plain markdown
            // with no symbol icon and no syntax coloring, unlike the legacy TSServer-backed hover path.
            if vs_capability && !quick_info_runs.is_empty() {
                let mut kind = ScriptElementKind::Keyword;
                let mut modifiers = ScriptElementKindModifier::NONE;
                if let Some(symbol) = symbol {
                    // Resolve aliases to their target before computing the icon kind, so e.g. `import { x }`
                    // shows the icon for whatever `x` actually is (const, function, ...) rather than a
                    // generic alias icon. GetSymbolModifiers already accounts for the alias target itself.
                    let mut icon_symbol = symbol;
                    if checker.borrow().symbol_arena.get_ref(symbol)
                        .flags
                        .intersects(SymbolFlags::ALIAS)
                    {
                        if let Some(resolved) = checker.borrow_mut().get_aliased_symbol(symbol) {
                            if resolved != symbol {
                                icon_symbol = resolved;
                            }
                        }
                    }
                    let symbols_rc = checker.borrow().symbol_arena.clone();
                    kind = {
                        let nodes = program.arena_of(range_node);
                        get_symbol_kind(
                            Some(&mut checker.borrow_mut()),
                            icon_symbol,
                            range_node,
                            &nodes,
                            &symbols_rc,
                        )
                    };
                    modifiers = {
                        let mut nodes = program.nodes_mut(range_node.file_index());
                        get_symbol_modifiers(
                            Some(&mut checker.borrow_mut()),
                            Some(symbol),
                            &mut nodes,
                            &symbols_rc,
                        )
                    };
                }
                let image_id = get_vs_hover_image_id(kind, modifiers);
                let mut documentation_runs: Vec<lsproto::VSClassifiedTextRun> = Vec::new();
                let doc_text = vs_documentation.trim_start_matches('\n');
                if !doc_text.is_empty() {
                    documentation_runs.push(lsproto::VSClassifiedTextRun {
                        classification_type_name: lsproto::ClassificationTypeName::Text.to_string(),
                        text: doc_text.to_string(),
                        ..Default::default()
                    });
                }
                hover.vs_raw_content = build_vs_hover_raw_content(
                    Some(image_id),
                    &quick_info_runs,
                    &documentation_runs,
                );
            }

            done();
            hovers.push(hover);
        }
        if hovers.is_empty() {
            return Ok(lsproto::HoverOrNull::default());
        }
        if hovers.len() == 1 {
            return Ok(lsproto::HoverOrNull {
                hover: hovers.into_iter().next(),
            });
        }

        let mut combined = hovers[0].clone();
        let mut contents: Vec<String> = Vec::with_capacity(hovers.len());
        let mut seen_contents: Set<String> = Set::new();
        let mut raw_contents: Vec<
            lsproto::VSImageElementOrClassifiedTextElementOrContainerElement,
        > = Vec::new();
        let mut common_range = combined.range;
        for hover in &hovers {
            let content = hover.contents.markup_content.as_ref().map_or("", |m| {
                m.value.trim_end_matches('\n')
            });
            if !seen_contents.has(&content.to_string()) {
                seen_contents.add(content.to_string());
                contents.push(content.to_string());
                if let Some(vs_raw_content) = &hover.vs_raw_content {
                    raw_contents.push(
                        lsproto::VSImageElementOrClassifiedTextElementOrContainerElement {
                            container_element: Some(vs_raw_content.clone()),
                            ..Default::default()
                        },
                    );
                }
            }
            combined.can_increase_verbosity =
                combined.can_increase_verbosity || hover.can_increase_verbosity;
            if common_range.is_none()
                || hover.range.is_none()
                || common_range != hover.range
            {
                common_range = None;
            }
        }
        let separator = if content_format == lsproto::MarkupKind::Markdown {
            "\n\n---\n\n"
        } else {
            "\n\n"
        };
        if let Some(markup) = combined.contents.markup_content.as_mut() {
            markup.value = contents.join(separator);
        }
        combined.range = common_range;
        combined.vs_raw_content = match raw_contents.len() {
            0 => None,
            1 => raw_contents.into_iter().next().and_then(|e| e.container_element),
            _ => Some(lsproto::VSContainerElement {
                style: lsproto::VSContainerElementStyle::Stacked,
                elements: Some(raw_contents),
                ..Default::default()
            }),
        };
        Ok(lsproto::HoverOrNull {
            hover: Some(combined),
        })
    }

    /// `getQuickInfoAndDocumentationForSymbol` — PORT: Go's `node` parameter
    /// is the caller's `rangeNode` (from `getNodeForQuickInfo`).
    fn get_quick_info_and_documentation_for_symbol(
        &self,
        program: &Rc<Program>,
        c: &Rc<RefCell<Checker>>,
        symbol: Option<SymbolId>,
        node: NodeId,
        content_format: lsproto::MarkupKind,
        vc: &mut VerbosityContext,
        vs_capability: bool,
    ) -> (String, String, String, Vec<lsproto::VSClassifiedTextRun>) {
        let meaning = {
            let mut nodes = program.nodes_mut(node.file_index());
            get_meaning_from_location(&mut nodes, node)
        };
        let info =
            get_quick_info_and_declaration_at_location(
                program, c, symbol, node, vc, vs_capability, meaning,
            );
        let quick_info = info.display_parts.string().to_string();
        if quick_info.is_empty() {
            return (String::new(), String::new(), String::new(), Vec::new());
        }
        let quick_info_runs = info.display_parts.get_runs().to_vec();

        let mapper = self.documentation_location_mapper(Feature::Hover);
        let documentation = get_documentation_for_symbol(
            &mapper,
            program,
            c,
            symbol,
            node,
            info.declaration,
            content_format,
            false, /*commentOnly*/
        );

        // VS's rich hover (_vs_rawContent) renders documentation as plain colorized text with no Markdown
        // parser, so it can't use the tag section (@param/@returns/@example/@see, etc.) that
        // getDocumentationFromDeclaration renders with '*@tag*' bolding and ```-fenced @example blocks --
        // those would show up as literal asterisks/backticks. This also matches the legacy TSServer-backed
        // VS hover (TypeScript-VS's HoverService.cs), which only ever surfaced the JSDoc summary
        // (TSServer's quickinfo `documentation`) and never included the tag section at all (TSServer
        // exposes tags via a separate `tags` field that legacy VS hover never read). So request
        // comment-only, plain-text documentation for the VS path instead of reusing `documentation`.
        let mut vs_documentation = String::new();
        if vs_capability {
            vs_documentation = get_documentation_for_symbol(
                &mapper,
                program,
                c,
                symbol,
                node,
                info.declaration,
                lsproto::MarkupKind::PlainText,
                true, /*commentOnly*/
            );
        }

        (quick_info, documentation, vs_documentation, quick_info_runs)
    }

    /// `documentationLocationMapper`.
    fn documentation_location_mapper(
        &self,
        feature: Feature,
    ) -> impl Fn(NodeId, TextRange) -> (lsproto::Location, Fidelity) + '_ {
        move |file: NodeId, file_range: TextRange| {
            self.source_file_range_to_lsp_location_for_feature(file, file_range, feature)
        }
    }
}

/// `getDocumentationForSymbol` tries each documentation source in turn
/// (call-signature documentation, declaration JSDoc, root-symbol JSDoc, alias
/// target JSDoc) and returns the first non-empty result, formatted for
/// `content_format`. `comment_only` restricts the result to the JSDoc summary,
/// excluding the @tag section.
fn get_documentation_for_symbol(
    get_mapped_location: &DocumentationLocationMapper<'_>,
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    symbol: Option<SymbolId>,
    node: NodeId,
    declaration: Option<NodeId>,
    content_format: lsproto::MarkupKind,
    comment_only: bool,
) -> String {
    let call_or_new = get_call_or_new_expression(program, node);
    let documentation = documentation_from_signature(
        get_mapped_location,
        program,
        c,
        symbol,
        call_or_new,
        node,
        content_format.clone(),
        comment_only,
    );
    if !documentation.is_empty() {
        return documentation;
    }

    let documentation = documentation_from_root_symbols(
        get_mapped_location,
        program,
        c,
        symbol,
        node,
        content_format.clone(),
        comment_only,
    );
    if !documentation.is_empty() {
        return documentation;
    }

    let documentation = get_documentation_from_declaration(
        get_mapped_location,
        program,
        c,
        symbol,
        declaration,
        node,
        content_format.clone(),
        comment_only,
    );
    if !documentation.is_empty() {
        return documentation;
    }

    documentation_from_alias(
        get_mapped_location,
        program,
        c,
        symbol,
        node,
        content_format,
        comment_only,
    )
}

/// `documentationFromSignature`.
fn documentation_from_signature(
    get_mapped_location: &DocumentationLocationMapper<'_>,
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    symbol: Option<SymbolId>,
    node: Option<NodeId>,
    location: NodeId,
    content_format: lsproto::MarkupKind,
    comment_only: bool,
) -> String {
    let Some(node) = node else {
        return String::new();
    };
    let Some(signature) = c.borrow_mut().get_resolved_signature_api(node) else {
        return String::new();
    };
    let declaration = c.borrow().signature_arena.get(signature).declaration();
    let Some(declaration) = declaration else {
        return String::new();
    };
    let is_sig_decl = {
        let nodes = program.arena_of(declaration);
        ast::is_call_signature_declaration(&nodes[declaration])
            || ast::is_construct_signature_declaration(&nodes[declaration])
    };
    if is_sig_decl {
        return get_documentation_from_declaration(
            get_mapped_location,
            program,
            c,
            symbol,
            Some(declaration),
            location,
            content_format,
            comment_only,
        );
    }
    String::new()
}

/// `documentationFromAlias`.
fn documentation_from_alias(
    get_mapped_location: &DocumentationLocationMapper<'_>,
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    symbol: Option<SymbolId>,
    node: NodeId,
    content_format: lsproto::MarkupKind,
    comment_only: bool,
) -> String {
    let Some(symbol) = symbol else {
        return String::new();
    };
    if !c.borrow().symbol_arena.get_ref(symbol)
        .flags
        .intersects(SymbolFlags::ALIAS)
    {
        return String::new();
    }

    let aliased_symbol = c.borrow_mut().get_aliased_symbol(symbol);
    let Some(aliased_symbol) = aliased_symbol else {
        return String::new();
    };
    if aliased_symbol == c.borrow().get_unknown_symbol() {
        return String::new();
    }

    let mut candidates = vec![aliased_symbol];
    if let Some(export_symbol) =
        c.borrow().symbol_arena.get_ref(aliased_symbol).export_symbol
    {
        candidates.push(export_symbol);
    }

    for candidate in candidates {
        let (value_declaration, first_declaration) = {
            let arena = c.borrow().symbol_arena.clone();
            let arena = arena.clone();
            let sym = &arena[candidate.index()];
            (sym.value_declaration, sym.declarations.first().copied())
        };
        let Some(aliased_declaration) = value_declaration.or(first_declaration) else {
            continue;
        };
        let documentation = get_documentation_from_declaration(
            get_mapped_location,
            program,
            c,
            Some(candidate),
            Some(aliased_declaration),
            node,
            content_format.clone(),
            comment_only,
        );
        if !documentation.is_empty() {
            return documentation;
        }
    }

    String::new()
}

/// `documentationFromRootSymbols`.
fn documentation_from_root_symbols(
    get_mapped_location: &DocumentationLocationMapper<'_>,
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    symbol: Option<SymbolId>,
    node: NodeId,
    content_format: lsproto::MarkupKind,
    comment_only: bool,
) -> String {
    let Some(symbol) = symbol else {
        return String::new();
    };

    let root_symbols = c.borrow_mut().get_root_symbols(symbol);
    if root_symbols.len() <= 1 {
        return String::new();
    }

    let mut docs: Vec<String> = Vec::new();
    for root_symbol in root_symbols {
        let mut declarations = {
            let arena = c.borrow().symbol_arena.clone();
            let arena = arena.clone();
            arena[root_symbol.index()].declarations.clone()
        };
        if declarations.is_empty() {
            if let Some(value_declaration) = {
                let arena = c.borrow().symbol_arena.clone();
                arena.get_ref(root_symbol).value_declaration
            } {
                declarations = vec![value_declaration];
            }
        }
        for declaration in declarations {
            let documentation = get_documentation_from_declaration(
                get_mapped_location,
                program,
                c,
                Some(root_symbol),
                Some(declaration),
                node,
                content_format.clone(),
                comment_only,
            );
            if !documentation.is_empty() && !docs.contains(&documentation) {
                docs.push(documentation);
            }
        }
    }
    docs.join("\n")
}

/// `getDocumentationFromDeclaration`.
pub(crate) fn get_documentation_from_declaration(
    get_mapped_location: &DocumentationLocationMapper<'_>,
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    _symbol: Option<SymbolId>,
    declaration: Option<NodeId>,
    _location: NodeId,
    content_format: lsproto::MarkupKind,
    comment_only: bool,
) -> String {
    let Some(declaration) = declaration else {
        return String::new();
    };
    let is_markdown = content_format == lsproto::MarkupKind::Markdown;
    let mut b = String::new();
    let mut seen_symbols: Set<SymbolId> = Set::new();
    let jsdoc = crate::jsdoc::get_jsdoc_or_tag(program, c, Some(declaration), &mut seen_symbols);
    let skip = {
        let nodes = program.arena_of(declaration);
        !nodes[declaration].flags.intersects(NodeFlags::REPARSED)
            && jsdoc.is_some_and(|jsdoc| contains_typedef_tag(&program.arena_of(jsdoc), jsdoc))
    };
    if let Some(jsdoc) = jsdoc.filter(|_| !skip) {
        let comments = {
            let nodes = program.arena_of(jsdoc);
            nodes[jsdoc].comments().map(|c| c.to_vec()).unwrap_or_default()
        };
        write_comments(
            get_mapped_location,
            &mut b,
            program,
            c,
            &comments,
            is_markdown,
        );
        let nodes = program.arena_of(jsdoc);
        if nodes[jsdoc].kind == Kind::JSDoc && !comment_only {
            if let Some(tags) = &nodes[jsdoc].as_js_doc().tags {
                let tags = tags.nodes().to_vec();
                drop(nodes);
                for tag in tags {
                    let tnodes = program.arena_of(tag);
                    let tag_kind = tnodes[tag].kind;
                    if tag_kind == Kind::JSDocTypeTag
                        || tag_kind == Kind::JSDocTypedefTag
                        || tag_kind == Kind::JSDocCallbackTag
                    {
                        continue;
                    }
                    b.push_str("\n\n");
                    let tag_name = tnodes[tag]
                        .tag_name()
                        .map(|n| tnodes[n].text(&tnodes).into_owned())
                        .unwrap_or_default();
                    if is_markdown {
                        b.push_str("*@");
                        b.push_str(&tag_name);
                        b.push('*');
                    } else {
                        b.push('@');
                        b.push_str(&tag_name);
                    }
                    match tag_kind {
                        Kind::JSDocParameterTag | Kind::JSDocPropertyTag => {
                            write_optional_entity_name(&mut b, &tnodes, tnodes[tag].name());
                        }
                        Kind::JSDocAugmentsTag => {
                            write_optional_entity_name(&mut b, &tnodes, tnodes[tag].class_name());
                        }
                        Kind::JSDocTemplateTag => {
                            let type_parameters =
                                tnodes[tag].type_parameters().map(|t| t.to_vec()).unwrap_or_default();
                            for (i, tp) in type_parameters.iter().enumerate() {
                                if i != 0 {
                                    b.push(',');
                                }
                                write_optional_entity_name(&mut b, &tnodes, tnodes[*tp].name());
                            }
                        }
                        _ => {}
                    }
                    let comments = tnodes[tag].comments().map(|c| c.to_vec()).unwrap_or_default();
                    if tag_kind == Kind::JSDocUnknownTag && tag_name == "example" {
                        let mut comment_text = tsc_scanner::utilities::get_text_of_jsdoc_comment(
                            tnodes[tag].comment_list(),
                            &tnodes,
                        );
                        if let Some(rest) = comment_text.strip_prefix("<caption>") {
                            if let Some(caption_end) = rest.find("</caption>") {
                                if caption_end > 0 {
                                    b.push_str(" — ");
                                    b.push_str(&rest[..caption_end]);
                                    comment_text = rest[caption_end + "</caption>".len()..]
                                        .trim_start()
                                        .to_string();
                                }
                            }
                        }
                        b.push('\n');
                        if comment_text.len() > 6
                            && comment_text.starts_with("```")
                            && comment_text.ends_with("```")
                            && comment_text.contains('\n')
                        {
                            b.push_str(&comment_text);
                            b.push('\n');
                        } else {
                            write_code(&mut b, "tsx", &comment_text);
                        }
                    } else if tag_kind == Kind::JSDocSeeTag
                        && tnodes[tag].as_js_doc_see_tag().name_expression.is_some()
                    {
                        let name_expression =
                            tnodes[tag].as_js_doc_see_tag().name_expression.expect("name expression");
                        b.push_str(" — ");
                        let name = program.arena_of(name_expression)[name_expression].name();
                        write_name_link(
                            get_mapped_location,
                            &mut b,
                            program,
                            c,
                            name,
                            "",
                            false, /*quote*/
                            is_markdown,
                        );
                        if !comments.is_empty() {
                            b.push(' ');
                            write_comments(
                                get_mapped_location,
                                &mut b,
                                program,
                                c,
                                &comments,
                                is_markdown,
                            );
                        }
                    } else if tag_kind == Kind::JSDocThrowsTag
                        && tnodes[tag].as_js_doc_throws_tag().type_expression.is_some()
                    {
                        let type_expression =
                            tnodes[tag].as_js_doc_throws_tag().type_expression.expect("type expression");
                        b.push_str(" — ");
                        b.push_str(&tsc_scanner::utilities::get_text_of_node(
                            type_expression,
                            &tnodes,
                        ));
                        if !comments.is_empty() {
                            b.push(' ');
                            write_comments(
                                get_mapped_location,
                                &mut b,
                                program,
                                c,
                                &comments,
                                is_markdown,
                            );
                        }
                    } else if !comments.is_empty() {
                        b.push(' ');
                        if nodes_comment_kind(program, comments[0]) != Kind::JSDocText
                            || !nodes_comment_text(program, comments[0]).starts_with('-')
                        {
                            b.push_str("— ");
                        }
                        write_comments(
                            get_mapped_location,
                            &mut b,
                            program,
                            c,
                            &comments,
                            is_markdown,
                        );
                    }
                }
            }
        }
    }
    b
}

fn nodes_comment_kind(program: &Rc<Program>, comment: NodeId) -> Kind {
    program.arena_of(comment)[comment].kind
}

fn nodes_comment_text(program: &Rc<Program>, comment: NodeId) -> String {
    let nodes = program.arena_of(comment);
    nodes[comment].text(&nodes).into_owned()
}

/// `formatQuickInfo`.
fn format_quick_info(quick_info: &str) -> String {
    let mut b = String::with_capacity(32);
    write_code(&mut b, "typescript", quick_info);
    b
}

/// `shouldGetType`.
fn should_get_type(nodes: &[Node], node: NodeId) -> bool {
    match nodes[node].kind {
        Kind::Identifier => {
            // If we're in a JSDoc node with no associated symbol, no binding has taken place for the node and
            // we can't answer questions about types of declaration nodes (such as property declarations).
            !(nodes[node].flags.intersects(NodeFlags::JSDOC)
                && ast::is_declaration_name(node, nodes))
                && !ast::is_label_name(node, nodes)
                && !ast::is_tag_name(node, nodes)
                && nodes[node]
                    .parent
                    .map_or(true, |p| !ast::is_const_type_reference(&nodes[p], nodes))
        }
        Kind::ThisKeyword | Kind::ThisType | Kind::SuperKeyword | Kind::NamedTupleMember => true,
        Kind::MetaProperty => ast::is_import_meta(&nodes[node], nodes),
        _ => false,
    }
}

/// `symbolDisplayInfo` holds the result of
/// `getSymbolDisplayPartsDocumentationAndSymbolKind`.
pub(crate) struct SymbolDisplayInfo {
    /// `displayParts`.
    pub(crate) display_parts: DisplayPartsWriter,
    /// `declaration`.
    pub(crate) declaration: Option<NodeId>,
}

/// The captured closure state of `getQuickInfoAndDeclarationAtLocation` —
/// Go's `writeTypeClassified`/`writeSymbol`/etc. closures become methods here.
struct QuickInfoState<'a> {
    /// `c`.
    c: &'a RefCell<Checker>,
    /// `program`.
    program: &'a Rc<Program>,
    /// `dpw`.
    dpw: DisplayPartsWriter,
    /// `vc` — Go's `*checker.VerbosityContext`; the only caller always
    /// passes non-nil (the Go `vc == nil` defaulting is handled there).
    vc: &'a mut VerbosityContext,
    /// `vsCapability`.
    vs_capability: bool,
    /// `meaning`.
    meaning: SemanticMeaning,
    /// `node`.
    node: NodeId,
    /// `container`.
    container: Option<NodeId>,
    /// `sourceFile` for printer context.
    source_file: Option<NodeId>,
    /// `firstDeclaration`.
    first_declaration: Option<NodeId>,
    /// `visitedAliases`.
    visited_aliases: Set<SymbolId>,
    /// `aliasLevel`.
    alias_level: i32,
    /// `symbolWasExpanded`.
    symbol_was_expanded: bool,
}

/// `nodeBuilderFlags` for classified output (same as
/// `signatureHelpNodeBuilderFlags`).
const CLASSIFIED_NODE_BUILDER_FLAGS: nodebuilder::Flags = nodebuilder::Flags(
    nodebuilder::Flags::IGNORE_ERRORS.0
        | nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE.0
        | nodebuilder::Flags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME.0,
);

fn to_node_builder_flags(flags: TypeFormatFlags) -> nodebuilder::Flags {
    nodebuilder::Flags(flags.0 & TypeFormatFlags::NODE_BUILDER_FLAGS_MASK.0)
}

/// Runs a node-builder→printer pipeline that prints `node` into `dpw`,
/// preserving VS classifications. Local helper for `writeTypeClassified`/
/// `writeSignatureClassified`/`writeModuleImportAttributes`.
fn print_node_classified(
    c: &RefCell<Checker>,
    nodes: &mut Vec<Node>,
    emit_context: &mut EmitContext,
    node: NodeId,
    source_file: Option<NodeId>,
    temp_dpw: &mut DisplayPartsWriter,
    id_to_symbol: Option<&FxHashMap<NodeId, SymbolId>>,
) {
    let symbol_arena = c.borrow().symbol_arena.clone();
    let symbols = symbol_arena.clone();
    let mut p = Printer::new(
        PrinterOptions {
            new_line: NewLineKind::LF,
            ..Default::default()
        },
        PrintHandlers::default(),
        emit_context,
        nodes,
        &symbols,
    );
    p.id_to_symbol = id_to_symbol;
    p.write(Some(node), source_file, temp_dpw, None);
}

impl<'a> QuickInfoState<'a> {
    fn checker(&self) -> std::cell::RefMut<'_, Checker> {
        self.c.borrow_mut()
    }

    fn sym_flags(&self, symbol: SymbolId) -> SymbolFlags {
        self.c.borrow().symbol_arena.get_ref(symbol).flags
    }

    fn sym_check_flags(&self, symbol: SymbolId) -> CheckFlags {
        self.c.borrow().symbol_arena.get_ref(symbol).check_flags
    }

    fn sym_value_declaration(&self, symbol: SymbolId) -> Option<NodeId> {
        self.c.borrow().symbol_arena.get_ref(symbol).value_declaration
    }

    fn sym_declarations(&self, symbol: SymbolId) -> Vec<NodeId> {
        self.c.borrow().symbol_arena.get_ref(symbol)
            .declarations
            .clone()
    }

    /// `setDeclaration`.
    fn set_declaration(&mut self, declaration: Option<NodeId>) {
        if self.first_declaration.is_none() {
            self.first_declaration = declaration;
        }
    }

    /// `writeNewLine`.
    fn write_new_line(&mut self) {
        if !self.dpw.string().is_empty() {
            self.dpw.write("\n");
        }
        if self.alias_level != 0 {
            self.dpw.write_punctuation("(");
            self.dpw.write("alias");
            self.dpw.write_punctuation(") ");
        }
    }

    /// `writeTypeClassified` — writes a type to `dpw` with proper
    /// classification (punctuation, symbols, keywords). Falls back to flat
    /// text when `vs_capability` is false or when `TypeToTypeNode` fails.
    fn write_type_classified(
        &mut self,
        t: TypeId,
        enclosing: Option<NodeId>,
        flags: TypeFormatFlags,
    ) {
        let flags = flags | TypeFormatFlags::MULTILINE_OBJECT_LITERALS;
        if !self.vs_capability {
            // PORT: `self.c.borrow_mut()` (not `self.checker()`) so the
            // borrow is field-scoped and `self.vc` can be reborrowed.
            let text = self.c.borrow_mut().type_to_string_ex(
                t,
                enclosing,
                flags,
                Some(&mut *self.vc),
            );
            self.dpw.write(&text);
            return;
        }
        let combined_flags =
            to_node_builder_flags(flags) | CLASSIFIED_NODE_BUILDER_FLAGS;
        let mut node_builder =
            new_node_builder_ex(&self.c.borrow(), EmitContext::new(), FxHashMap::default());
        let file_index = builder_arena_index(&node_builder, enclosing);
        let (file_index, arena_cell) = self.program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = ArenaCheckout::new(arena_cell);
        let type_node = node_builder.type_to_type_node(
            &mut self.c.borrow_mut(),
            &mut nodes,
            t,
            enclosing,
            combined_flags,
            nodebuilder::InternalFlags::NONE,
            None,
        );
        let Some(type_node) = type_node else {
            let text = self.c.borrow_mut().type_to_string_ex(
                t,
                enclosing,
                flags,
                Some(&mut *self.vc),
            );
            self.dpw.write(&text);
            return;
        };
        let emit_context_cell = node_builder
            .impl_
            .as_ref()
            .expect("NodeBuilder without impl")
            .e
            .clone();
        let mut emit_context = emit_context_cell.borrow_mut();
        let id_to_symbol = std::mem::take(
            &mut node_builder
                .impl_
                .as_mut()
                .expect("NodeBuilder without impl")
                .id_to_symbol,
        );
        let mut temp_dpw =
            new_display_parts_writer(true, &self.c.borrow(), &self.program.clone());
        print_node_classified(
            self.c,
            &mut nodes,
            &mut emit_context,
            type_node,
            self.source_file,
            &mut temp_dpw,
            Some(&id_to_symbol),
        );
        self.dpw.write_from(&temp_dpw);
    }

    /// `writeSignatureClassified` — writes a signature to `dpw` with proper
    /// classification.
    fn write_signature_classified(
        &mut self,
        sig: SignatureId,
        enclosing: Option<NodeId>,
        flags: TypeFormatFlags,
    ) {
        let flags = flags | TypeFormatFlags::MULTILINE_OBJECT_LITERALS;
        if !self.vs_capability {
            let text = self.c.borrow_mut().signature_to_string_ex(
                sig,
                enclosing,
                flags,
                Some(&mut *self.vc),
            );
            self.dpw.write(&text);
            return;
        }
        let is_constructor = self
            .c
            .borrow()
            .signature_arena
            .get(sig)
            .flags()
            .intersects(tsc_checker::types::SignatureFlags::CONSTRUCT)
            && !flags.intersects(TypeFormatFlags::WRITE_CALL_STYLE_SIGNATURE);
        let sig_output = if flags.intersects(TypeFormatFlags::WRITE_ARROW_STYLE_SIGNATURE) {
            if is_constructor {
                Kind::ConstructorType
            } else {
                Kind::FunctionType
            }
        } else if is_constructor {
            Kind::ConstructSignature
        } else {
            Kind::CallSignature
        };
        let combined_flags =
            to_node_builder_flags(flags) | CLASSIFIED_NODE_BUILDER_FLAGS;
        let mut node_builder =
            new_node_builder_ex(&self.c.borrow(), EmitContext::new(), FxHashMap::default());
        let file_index = builder_arena_index(&node_builder, enclosing);
        let (file_index, arena_cell) = self.program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = ArenaCheckout::new(arena_cell);
        let sig_node = node_builder.signature_to_signature_declaration(
            &mut self.c.borrow_mut(),
            &mut nodes,
            sig,
            sig_output,
            enclosing,
            combined_flags,
            nodebuilder::InternalFlags::NONE,
            None,
        );
        let Some(sig_node) = sig_node else {
            let text = self.c.borrow_mut().signature_to_string_ex(
                sig,
                enclosing,
                flags,
                Some(&mut *self.vc),
            );
            self.dpw.write(&text);
            return;
        };
        let emit_context_cell = node_builder
            .impl_
            .as_ref()
            .expect("NodeBuilder without impl")
            .e
            .clone();
        let mut emit_context = emit_context_cell.borrow_mut();
        let id_to_symbol = std::mem::take(
            &mut node_builder
                .impl_
                .as_mut()
                .expect("NodeBuilder without impl")
                .id_to_symbol,
        );
        let mut temp_dpw =
            new_display_parts_writer(true, &self.c.borrow(), &self.program.clone());
        print_node_classified(
            self.c,
            &mut nodes,
            &mut emit_context,
            sig_node,
            self.source_file,
            &mut temp_dpw,
            Some(&id_to_symbol),
        );
        self.dpw.write_from(&temp_dpw);
    }

    /// `writeSymbolClassified` — writes a symbol name to `dpw` with proper
    /// classification based on symbol flags.
    fn write_symbol_classified(
        &mut self,
        symbol: SymbolId,
        enclosing: Option<NodeId>,
        meaning: SymbolFlags,
        flags: SymbolFormatFlags,
    ) {
        let text = self
            .checker()
            .symbol_to_string_ex(symbol, enclosing, meaning, flags, None);
        if !self.vs_capability {
            self.dpw.write(&text);
            return;
        }
        // Use WriteSymbol which calls classificationForSymbol to determine
        // the correct classification.
        self.dpw.write_symbol(&text, symbol);
    }

    /// `writeModuleImportAttributes`.
    fn write_module_import_attributes(&mut self, symbol: SymbolId) {
        let declarations = self.sym_declarations(symbol);
        let declaration = declarations.iter().copied().find(|declaration| {
            let nodes = self.program.arena_of(*declaration);
            ast::is_module_declaration(&nodes[*declaration])
                && nodes[*declaration].as_module_declaration().attributes.is_some()
        });
        let Some(declaration) = declaration else {
            return;
        };
        let attributes = {
            let nodes = self.program.arena_of(declaration);
            nodes[declaration]
                .as_module_declaration()
                .attributes
                .expect("attributes")
        };
        let mut emit_context = EmitContext::new();
        emit_context.set_emit_flags(attributes, EmitFlags::SINGLE_LINE);
        let source_file = {
            let nodes = self.program.arena_of(declaration);
            ast::get_source_file_of_node(Some(declaration), &nodes)
        };
        let mut temp_dpw = new_display_parts_writer(
            self.vs_capability,
            &self.c.borrow(),
            &self.program.clone(),
        );
        let mut nodes = ArenaCheckout::new(
            self.program.nodes_handle_or_fallback(declaration.file_index()).1,
        );
        print_node_classified(
            self.c,
            &mut nodes,
            &mut emit_context,
            attributes,
            source_file,
            &mut temp_dpw,
            None,
        );
        self.dpw.write_keyword(" with ");
        self.dpw.write_from(&temp_dpw);
    }

    /// `writeSignatures`.
    fn write_signatures(
        &mut self,
        signatures: &[SignatureId],
        prefix: &str,
        parenthesized: bool,
        symbol: SymbolId,
    ) {
        for (i, &sig) in signatures.iter().enumerate() {
            self.write_new_line();
            if i == 3 && signatures.len() >= 5 {
                self.dpw
                    .write_comment(&format!("// +{} more overloads", signatures.len() - 3));
                break;
            }
            if parenthesized {
                self.dpw.write_punctuation("(");
                self.dpw.write(prefix);
                self.dpw.write_punctuation(") ");
            } else {
                self.dpw.write_keyword(prefix);
            }
            self.write_symbol_classified(
                symbol,
                self.container,
                SymbolFlags::NONE,
                SYMBOL_FORMAT_FLAGS,
            );
            if self
                .sym_flags(symbol)
                .intersects(SymbolFlags::OPTIONAL)
            {
                self.dpw.write_punctuation("?");
            }
            self.write_signature_classified(
                sig,
                self.container,
                TYPE_FORMAT_FLAGS
                    | TypeFormatFlags::WRITE_CALL_STYLE_SIGNATURE
                    | TypeFormatFlags::WRITE_TYPE_ARGUMENTS_OF_SIGNATURE,
            );
        }
    }

    /// `writeTypeParams`.
    fn write_type_params(&mut self, params: &[TypeId]) {
        if params.is_empty() {
            return;
        }
        self.dpw.write_punctuation("<");
        for (i, &tp) in params.iter().enumerate() {
            if i != 0 {
                self.dpw.write_punctuation(", ");
            }
            let tp_symbol = self.c.borrow().types.get(tp).symbol();
            if let Some(tp_symbol) = tp_symbol {
                self.write_symbol_classified(
                    tp_symbol,
                    None,
                    SymbolFlags::NONE,
                    SYMBOL_FORMAT_FLAGS,
                );
            }
            if let Some(cons) = self.c.borrow_mut().get_constraint_of_type_parameter(tp) {
                self.dpw.write_keyword(" extends ");
                self.write_type_classified(cons, None, TYPE_FORMAT_FLAGS);
            }
            if let Some(def) = self.c.borrow_mut().get_default_from_type_parameter(tp) {
                self.dpw.write_operator(" = ");
                self.write_type_classified(def, None, TYPE_FORMAT_FLAGS);
            }
        }
        self.dpw.write_punctuation(">");
    }

    /// `canExpandSymbol` — only offers symbol-level expansion for types that
    /// `tryExpandSymbol` handles: class, interface, enum, namespace/module.
    /// For functions/variables/properties, the node builder's
    /// `probeTypeExpandability` detects expandable type components.
    fn can_expand_symbol(&mut self, symbol: SymbolId) -> bool {
        let flags = self.sym_flags(symbol);
        if !flags.intersects(
            SymbolFlags::CLASS | SymbolFlags::INTERFACE | SymbolFlags::NAMESPACE,
        ) {
            return false;
        }
        let t = if flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
            self.checker().get_declared_type_of_symbol(symbol)
        } else {
            self.checker().get_type_of_symbol_at_location(symbol, Some(self.node))
        };
        if self.checker().is_lib_type_for_hover_verbosity(t) {
            return false;
        }
        if self.vc.level > 0 {
            return true;
        }
        // At level 0, signal that expansion is possible but don't expand.
        self.vc.can_increase_verbosity = true;
        false
    }

    /// `tryExpandSymbol` — checks if a symbol can be expanded at the current
    /// verbosity level.
    fn try_expand_symbol(&mut self, symbol: SymbolId, meaning: SymbolFlags) -> bool {
        if self.symbol_was_expanded {
            return true;
        }
        if self.can_expand_symbol(symbol) {
            let mut expand_vc = VerbosityContext {
                level: self.vc.level - 1,
                max_truncation_length: self.vc.max_truncation_length,
                ..Default::default()
            };
            let expanded = self.checker().expand_symbol_for_hover(
                symbol,
                meaning,
                Some(&mut expand_vc),
            );
            if !expanded.is_empty() {
                self.vc.can_increase_verbosity =
                    self.vc.can_increase_verbosity || expand_vc.can_increase_verbosity;
                self.vc.truncated = self.vc.truncated || expand_vc.truncated;
                self.dpw.write(&expanded);
                self.symbol_was_expanded = true;
                return true;
            }
        }
        false
    }

    /// `writeSymbol` — recursively writes all meanings of the symbol
    /// (resolving aliases first).
    fn write_symbol(&mut self, symbol: SymbolId) {
        // Recursively write all meanings of alias
        if self.sym_flags(symbol).intersects(SymbolFlags::ALIAS)
            && !self.visited_aliases.has(&symbol)
        {
            self.visited_aliases.add(symbol);
            let aliased_symbol = self.c.borrow_mut().get_aliased_symbol(symbol);
            if let Some(aliased_symbol) = aliased_symbol {
                if aliased_symbol != self.c.borrow().get_unknown_symbol() {
                    self.alias_level += 1;
                    self.write_symbol(aliased_symbol);
                    self.alias_level -= 1;
                }
            }
        }
        let mut flags = match self.meaning {
            SemanticMeaning::VALUE => {
                self.sym_flags(symbol) & (SymbolFlags::VALUE | SymbolFlags::SIGNATURE)
            }
            SemanticMeaning::TYPE => self.sym_flags(symbol) & SymbolFlags::TYPE,
            SemanticMeaning::NAMESPACE => self.sym_flags(symbol) & SymbolFlags::NAMESPACE,
            _ => {
                self.sym_flags(symbol)
                    & (SymbolFlags::VALUE
                        | SymbolFlags::SIGNATURE
                        | SymbolFlags::TYPE
                        | SymbolFlags::NAMESPACE)
            }
        };
        if flags == SymbolFlags::NONE {
            if self.alias_level != 0 || !self.dpw.string().is_empty() {
                return;
            }
            flags = self.sym_flags(symbol)
                & (SymbolFlags::VALUE
                    | SymbolFlags::SIGNATURE
                    | SymbolFlags::TYPE
                    | SymbolFlags::NAMESPACE);
            if flags == SymbolFlags::NONE {
                return;
            }
        }
        if flags.intersects(SymbolFlags::PROPERTY)
            && self
                .sym_value_declaration(symbol)
                .is_some_and(|vd| ast::is_method_declaration(&self.program.arena_of(vd)[vd]))
        {
            flags = SymbolFlags::METHOD;
        }
        if flags.intersects(
            SymbolFlags::VARIABLE | SymbolFlags::PROPERTY | SymbolFlags::ACCESSOR,
        ) {
            self.write_new_line();
            if !self.sym_check_flags(symbol).intersects(CheckFlags::INDEX_SYMBOL) {
                if flags.intersects(SymbolFlags::PROPERTY) {
                    self.dpw.write_punctuation("(");
                    self.dpw.write("property");
                    self.dpw.write_punctuation(") ");
                } else if flags.intersects(SymbolFlags::ACCESSOR) {
                    self.dpw.write_punctuation("(");
                    self.dpw.write("accessor");
                    self.dpw.write_punctuation(") ");
                } else {
                    let decl = self
                        .sym_value_declaration(symbol)
                        .map(|decl| ast::get_root_declaration(decl, &self.program.arena_of(decl)));
                    if let Some(decl) = decl {
                        let nodes = self.program.arena_of(decl);
                        if ast::is_parameter_declaration(&nodes[decl]) {
                            self.dpw.write_punctuation("(");
                            self.dpw.write("parameter");
                            self.dpw.write_punctuation(") ");
                        } else if ast::is_var_let(decl, &nodes) {
                            self.dpw.write_keyword("let ");
                        } else if ast::is_var_const(decl, &nodes) {
                            self.dpw.write_keyword("const ");
                        } else if ast::is_var_using(decl, &nodes) {
                            self.dpw.write_keyword("using ");
                        } else if ast::is_var_await_using(decl, &nodes) {
                            self.dpw.write_keyword("await ");
                            self.dpw.write_keyword("using ");
                        } else {
                            self.dpw.write_keyword("var ");
                        }
                    }
                }
                let (name, parent_flags) = {
                    let arena = self.c.borrow().symbol_arena.clone();
                    let arena = arena.clone();
                    let sym = &arena[symbol.index()];
                    (
                        sym.name.clone(),
                        sym.parent.map(|p| arena[p.index()].flags),
                    )
                };
                if name.as_ref() == ast::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                    && parent_flags.is_some_and(|f| f.intersects(SymbolFlags::MODULE))
                {
                    self.dpw.write("exports");
                } else {
                    self.write_symbol_classified(
                        symbol,
                        self.container,
                        SymbolFlags::NONE,
                        SYMBOL_FORMAT_FLAGS,
                    );
                }
                if self.sym_flags(symbol).intersects(SymbolFlags::OPTIONAL) {
                    self.dpw.write_punctuation("?");
                }
                self.dpw.write_punctuation(": ");
            }
            if let Some(call_node) = get_call_or_new_expression(self.program, self.node) {
                let mut flags = TYPE_FORMAT_FLAGS
                    | TypeFormatFlags::WRITE_TYPE_ARGUMENTS_OF_SIGNATURE
                    | TypeFormatFlags::WRITE_ARROW_STYLE_SIGNATURE;
                if ast::is_call_expression(&self.program.arena_of(call_node)[call_node]) {
                    flags |= TypeFormatFlags::WRITE_CALL_STYLE_SIGNATURE;
                }
                let sig = self
                    .checker()
                    .get_resolved_signature_api(call_node)
                    .expect("GetResolvedSignature");
                self.write_signature_classified(sig, self.container, flags);
            } else {
                let t = self.checker().get_type_of_symbol_at_location(symbol, Some(self.node));
                // If the type is a constrained type parameter, support expansion:
                // Level 0: show just "T", signal canIncreaseVerbosity
                // Level 1+: show "T extends Constraint" with the constraint expanded at level-1
                let t_symbol_is_tp = self
                    .c
                    .borrow()
                    .types
                    .get(t)
                    .symbol()
                    .is_some_and(|s| {
                        self.c.borrow().symbol_arena.get_ref(s)
                            .flags
                            .intersects(SymbolFlags::TYPE_PARAMETER)
                    });
                if t_symbol_is_tp
                    && self.checker().get_constraint_of_type_parameter(t).is_some()
                {
                    if self.vc.level > 0 {
                        let mut expand_vc = VerbosityContext {
                            level: self.vc.level - 1,
                            max_truncation_length: self.vc.max_truncation_length,
                            ..Default::default()
                        };
                        let text = self.checker().type_parameter_to_string_ex(
                            t,
                            self.container,
                            Some(&mut expand_vc),
                        );
                        self.dpw.write(&text);
                        self.vc.can_increase_verbosity = self.vc.can_increase_verbosity
                            || expand_vc.can_increase_verbosity;
                        self.vc.truncated = self.vc.truncated || expand_vc.truncated;
                    } else {
                        self.write_type_classified(t, self.container, TYPE_FORMAT_FLAGS);
                        self.vc.can_increase_verbosity = true;
                    }
                } else {
                    self.write_type_classified(t, self.container, TYPE_FORMAT_FLAGS);
                }
            }
            self.set_declaration(
                self.sym_value_declaration(symbol)
                    .or_else(|| self.sym_declarations(symbol).first().copied()),
            );
        }
        if flags.intersects(SymbolFlags::ENUM_MEMBER) {
            self.write_new_line();
            self.dpw.write_punctuation("(");
            self.dpw.write("enum member");
            self.dpw.write_punctuation(") ");
            let t = self.checker().get_type_of_symbol(symbol);
            self.write_type_classified(t, self.container, TYPE_FORMAT_FLAGS);
            if self.c.borrow().types.get(t).flags().intersects(tsc_checker::types::TypeFlags::LITERAL)
            {
                self.dpw.write_operator(" = ");
                let text = tsc_checker::checker_core::value_to_string(
                    self.c.borrow().types.get(t).as_literal_type().value(),
                );
                self.dpw.write_literal(&text);
            }
            self.set_declaration(self.sym_value_declaration(symbol));
        }
        if flags.intersects(SymbolFlags::FUNCTION | SymbolFlags::METHOD) {
            let is_method = flags.intersects(SymbolFlags::METHOD);
            let prefix = if is_method { "method" } else { "function " };
            let node_is_fn_name = {
                let nodes = self.program.arena_of(self.node);
                ast::is_identifier(&nodes[self.node])
                    && nodes[self.node].parent.is_some_and(|p| {
                        (ast::is_function_like_declaration(Some(p), &nodes)
                            || ast::is_method_signature_declaration(&nodes[p]))
                            && nodes[p].name() == Some(self.node)
                    })
            };
            if node_is_fn_name {
                let parent = self.program.arena_of(self.node)[self.node].parent.expect("parent");
                if self.sym_declarations(symbol).contains(&parent) {
                    self.set_declaration(Some(parent));
                    let sig = self.checker().get_signature_from_declaration(parent);
                    self.write_signatures(&[sig], prefix, is_method, symbol);
                } else {
                    self.write_function_signatures(symbol, prefix, is_method);
                }
            } else {
                self.write_function_signatures(symbol, prefix, is_method);
            }
            self.set_declaration(self.sym_value_declaration(symbol));
        }
        if flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
            self.write_class_or_interface(flags, symbol);
            if flags.intersects(SymbolFlags::CLASS) {
                self.set_declaration(self.sym_value_declaration(symbol));
            } else {
                self.set_declaration(
                    self.sym_declarations(symbol)
                        .iter()
                        .copied()
                        .find(|&d| ast::is_interface_declaration(&self.program.arena_of(d)[d])),
                );
            }
        }
        if flags.intersects(SymbolFlags::ENUM) {
            self.write_new_line();
            if !self.try_expand_symbol(symbol, flags) {
                if self.sym_declarations(symbol).iter().copied().any(|d| {
                    let nodes = self.program.arena_of(d);
                    ast::is_enum_declaration(&nodes[d]) && ast::is_enum_const(d, &nodes)
                }) {
                    self.dpw.write_keyword("const ");
                }
                self.dpw.write_keyword("enum ");
                self.write_symbol_classified(
                    symbol,
                    self.container,
                    SymbolFlags::NONE,
                    SYMBOL_FORMAT_FLAGS,
                );
            }
            self.set_declaration(
                self.sym_declarations(symbol)
                    .iter()
                    .copied()
                    .find(|&d| ast::is_enum_declaration(&self.program.arena_of(d)[d])),
            );
        }
        if flags.intersects(SymbolFlags::MODULE) {
            self.write_new_line();
            if !self.try_expand_symbol(symbol, flags) {
                let is_module = self.sym_value_declaration(symbol).is_some_and(|vd| {
                    let nodes = self.program.arena_of(vd);
                    ast::is_source_file(&nodes[vd]) || ast::is_ambient_module(&nodes[vd], &nodes)
                });
                self.dpw
                    .write_keyword(if is_module { "module " } else { "namespace " });
                self.write_symbol_classified(
                    symbol,
                    self.container,
                    SymbolFlags::NONE,
                    SYMBOL_FORMAT_FLAGS,
                );
                self.write_module_import_attributes(symbol);
            }
            self.set_declaration(
                self.sym_declarations(symbol)
                    .iter()
                    .copied()
                    .find(|&d| ast::is_module_declaration(&self.program.arena_of(d)[d])),
            );
        }
        if flags.intersects(SymbolFlags::TYPE_PARAMETER) {
            self.write_new_line();
            self.dpw.write_punctuation("(");
            self.dpw.write("type parameter");
            self.dpw.write_punctuation(") ");
            {
                let nodes = self.program.arena_of(self.node);
                if ast::is_identifier(&nodes[self.node])
                    && nodes[self.node].parent.is_some_and(|p| ast::is_type_reference_node(&nodes[p]))
                {
                    let parent = nodes[self.node].parent.expect("parent");
                    // PORT: `self.c.borrow_mut()` keeps the borrow field-
                    // scoped so `self.dpw` writes below still compile.
                    let mut checker = self.c.borrow_mut();
                    let t = checker.get_type_at_location(parent);
                    if tsc_checker::exports::is_distributed_type_parameter(&checker.types, t) {
                        self.dpw.write_punctuation("(");
                        self.dpw.write("distributed");
                        self.dpw.write_punctuation(") ");
                    }
                }
            }
            let tp = self.checker().get_declared_type_of_symbol(symbol);
            self.write_symbol_classified(
                symbol,
                self.container,
                SymbolFlags::NONE,
                SYMBOL_FORMAT_FLAGS,
            );
            if let Some(cons) = self.c.borrow_mut().get_constraint_of_type_parameter(tp) {
                self.dpw.write_keyword(" extends ");
                self.write_type_classified(cons, self.container, TYPE_FORMAT_FLAGS);
            }
            // Show context: "in ClassName<T>" or "in funcName<T>(...)"
            let parent_symbol = self.c.borrow().symbol_arena.get_ref(symbol).parent;
            if let Some(parent_symbol) = parent_symbol {
                // Class/Interface type parameter.
                self.dpw.write_keyword(" in ");
                self.write_symbol_classified(
                    parent_symbol,
                    self.container,
                    SymbolFlags::NONE,
                    SYMBOL_FORMAT_FLAGS,
                );
                let parent_type = self.checker().get_declared_type_of_symbol(parent_symbol);
                let parent_params = {
                    let ty = self.c.borrow().types.get(parent_type);
                    ty.as_interface_type()
                        .map(|it| it.local_type_parameters().to_vec())
                        .unwrap_or_default()
                };
                self.write_type_params(&parent_params);
            } else {
                // Method/function type parameter.
                let decl = get_declaration_of_kind_any(
                    self.program,
                    self.c,
                    symbol,
                    Kind::TypeParameter,
                );
                if let Some(decl) = decl {
                    let declaration = self.program.arena_of(decl)[decl].parent;
                    if let Some(declaration) = declaration {
                        let dnodes = self.program.arena_of(declaration);
                        if ast::is_function_like(Some(declaration), &dnodes) {
                            self.dpw.write_keyword(" in ");
                            if dnodes[declaration].kind == Kind::ConstructSignature {
                                self.dpw.write_keyword("new ");
                            } else if dnodes[declaration].kind != Kind::CallSignature
                                && dnodes[declaration].name().is_some()
                            {
                                let decl_symbol = dnodes[declaration].symbol();
                                if let Some(decl_symbol) = decl_symbol {
                                    drop(dnodes);
                                    self.write_symbol_classified(
                                        decl_symbol,
                                        self.container,
                                        SymbolFlags::NONE,
                                        SYMBOL_FORMAT_FLAGS,
                                    );
                                }
                            }
                            let sig =
                                self.checker().get_signature_from_declaration(declaration);
                            self.write_signature_classified(
                                sig,
                                self.container,
                                TYPE_FORMAT_FLAGS
                                    | TypeFormatFlags::WRITE_TYPE_ARGUMENTS_OF_SIGNATURE,
                            );
                        } else if ast::is_type_alias_declaration(&dnodes[declaration]) {
                            self.dpw.write_keyword(" in ");
                            self.dpw.write_keyword("type ");
                            let decl_symbol = dnodes[declaration].symbol();
                            if let Some(decl_symbol) = decl_symbol {
                                drop(dnodes);
                                self.write_symbol_classified(
                                    decl_symbol,
                                    self.container,
                                    SymbolFlags::NONE,
                                    SYMBOL_FORMAT_FLAGS,
                                );
                                let ta_params = self
                                    .checker()
                                    .get_type_alias_type_parameters(decl_symbol);
                                self.write_type_params(&ta_params);
                            }
                        }
                    }
                }
            }
            self.set_declaration(
                self.sym_declarations(symbol)
                    .iter()
                    .copied()
                    .find(|&d| ast::is_type_parameter_declaration(&self.program.arena_of(d)[d])),
            );
        }
        if flags.intersects(SymbolFlags::TYPE_ALIAS) {
            self.write_new_line();
            self.dpw.write_keyword("type ");
            self.write_symbol_classified(
                symbol,
                self.container,
                SymbolFlags::NONE,
                SYMBOL_FORMAT_FLAGS,
            );
            let ta_params = self.checker().get_type_alias_type_parameters(symbol);
            self.write_type_params(&ta_params);
            self.dpw.write_operator(" = ");
            let type_alias_type = {
                let nodes = self.program.arena_of(self.node);
                if nodes[self.node].parent.is_some_and(|p| ast::is_const_type_reference(&nodes[p], &nodes)) {
                    let parent = nodes[self.node].parent.expect("parent");
                    drop(nodes);
                    self.checker().get_type_at_location(parent)
                } else {
                    drop(nodes);
                    self.checker().get_declared_type_of_symbol(symbol)
                }
            };
            self.write_type_classified(
                type_alias_type,
                self.container,
                TYPE_FORMAT_FLAGS | TypeFormatFlags::IN_TYPE_ALIAS,
            );
            self.set_declaration(
                self.sym_declarations(symbol).iter().copied().find(|&d| {
                    let kind = self.program.arena_of(d)[d].kind;
                    kind == Kind::TypeAliasDeclaration || kind == Kind::JSTypeAliasDeclaration
                }),
            );
        }
        if flags.intersects(SymbolFlags::SIGNATURE) {
            self.write_new_line();
            let t = self.checker().get_type_of_symbol(symbol);
            self.write_type_classified(t, self.container, TYPE_FORMAT_FLAGS);
        }
    }

    /// The `signatures := getSignaturesAtLocation(...)` branch shared by the
    /// `Function|Method` arm.
    fn write_function_signatures(
        &mut self,
        symbol: SymbolId,
        prefix: &str,
        is_method: bool,
    ) {
        let signatures =
            get_signatures_at_location(self.program, self.c, symbol, SignatureKind::Call, self.node);
        if signatures.len() == 1 {
            if let Some(d) = self.c.borrow().signature_arena.get(signatures[0]).declaration() {
                if !self
                    .program
                    .arena_of(d)[d]
                    .flags
                    .intersects(NodeFlags::JSDOC)
                {
                    self.set_declaration(Some(d));
                }
            }
        }
        self.write_signatures(&signatures, prefix, is_method, symbol);
    }

    /// The `Class|Interface` arm of `writeSymbol`.
    fn write_class_or_interface(&mut self, flags: SymbolFlags, symbol: SymbolId) {
        let node_kind = self.program.arena_of(self.node)[self.node].kind;
        let this_in_type_query =
            ast::is_this_in_type_query(self.node, &self.program.arena_of(self.node));
        if node_kind == Kind::ThisKeyword || this_in_type_query {
            self.write_new_line();
            self.dpw.write_keyword("this");
        } else if node_kind == Kind::ConstructorKeyword && {
            let nodes = self.program.arena_of(self.node);
            nodes[self.node].parent.is_some_and(|p| {
                ast::is_constructor_declaration(&nodes[p])
                    || ast::is_construct_signature_declaration(&nodes[p])
            })
        } {
            let parent = self.program.arena_of(self.node)[self.node].parent.expect("parent");
            self.set_declaration(Some(parent));
            let sig = self.checker().get_signature_from_declaration(parent);
            self.write_signatures(&[sig], "constructor ", false, symbol);
        } else {
            let mut signatures: Vec<SignatureId> = Vec::new();
            if flags.intersects(SymbolFlags::CLASS)
                && get_call_or_new_expression(self.program, self.node).is_some()
            {
                signatures = get_signatures_at_location(
                    self.program,
                    self.c,
                    symbol,
                    SignatureKind::Construct,
                    self.node,
                );
            }
            if signatures.len() == 1 {
                if let Some(d) = self
                    .c
                    .borrow()
                    .signature_arena
                    .get(signatures[0])
                    .declaration()
                {
                    if !self.program.arena_of(d)[d].flags.intersects(NodeFlags::JSDOC) {
                        self.set_declaration(Some(d));
                    }
                }
                self.write_signatures(&signatures, "constructor ", false, symbol);
            } else {
                self.write_new_line();
                if flags.intersects(SymbolFlags::CLASS) {
                    let class_expression = get_declaration_of_kind_any(
                        self.program,
                        self.c,
                        symbol,
                        Kind::ClassExpression,
                    );
                    if class_expression.is_some() {
                        // Local class expression: show "(local class)" prefix.
                        self.dpw.write_punctuation("(");
                        self.dpw.write("local class");
                        self.dpw.write_punctuation(") ");
                    }
                    if !self.try_expand_symbol(symbol, flags) {
                        if class_expression.is_none() {
                            if self.sym_declarations(symbol).iter().copied().any(|d| {
                                let nodes = self.program.arena_of(d);
                                ast::is_class_declaration(&nodes[d])
                                    && ast::has_abstract_modifier(&nodes[d])
                            }) {
                                self.dpw.write_keyword("abstract ");
                            }
                            self.dpw.write_keyword("class ");
                        }
                        self.write_symbol_classified(
                            symbol,
                            self.container,
                            SymbolFlags::NONE,
                            SYMBOL_FORMAT_FLAGS,
                        );
                        let declared = self.checker().get_declared_type_of_symbol(symbol);
                        let params = {
                            let ty = self.c.borrow().types.get(declared);
                            ty.as_interface_type()
                                .map(|it| it.local_type_parameters().to_vec())
                                .unwrap_or_default()
                        };
                        self.write_type_params(&params);
                    }
                } else {
                    if !self.try_expand_symbol(symbol, flags) {
                        self.dpw.write_keyword("interface ");
                        self.write_symbol_classified(
                            symbol,
                            self.container,
                            SymbolFlags::NONE,
                            SYMBOL_FORMAT_FLAGS,
                        );
                        let declared = self.checker().get_declared_type_of_symbol(symbol);
                        let params = {
                            let ty = self.c.borrow().types.get(declared);
                            ty.as_interface_type()
                                .map(|it| it.local_type_parameters().to_vec())
                                .unwrap_or_default()
                        };
                        self.write_type_params(&params);
                    }
                }
            }
        }
    }
}

/// `builder_arena_index` — the arena synthesized nodes are minted into
/// (local copy of the checker-private helper).
fn builder_arena_index(
    node_builder: &tsc_checker::nodebuilder::NodeBuilder,
    enclosing_declaration: Option<NodeId>,
) -> u32 {
    enclosing_declaration
        .map(|d| d.file_index())
        .unwrap_or_else(|| {
            node_builder
                .impl_
                .as_ref()
                .expect("NodeBuilder without impl")
                .f
                .file_index()
        })
}

/// `getDeclarationOfKind` on a `SymbolId`, resolving each declaration in its
/// own file arena (`ast.GetDeclarationOfKind` reads `declaration.Kind` through
/// pointers in Go, so it works across files).
fn get_declaration_of_kind_any(
    program: &Rc<Program>,
    c: &RefCell<Checker>,
    symbol: SymbolId,
    kind: Kind,
) -> Option<NodeId> {
    let declarations = c.borrow().symbol_arena.get_ref(symbol)
        .declarations
        .clone();
    declarations
        .iter()
        .copied()
        .find(|&d| program.arena_of(d)[d].kind == kind)
}

/// `getQuickInfoAndDeclarationAtLocation` builds classified display parts
/// using `DisplayPartsWriter` when `vs_capability` is true. When
/// `vs_capability` is false, it still builds the plain text string but skips
/// classification runs.
fn get_quick_info_and_declaration_at_location(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    symbol: Option<SymbolId>,
    node: NodeId,
    vc: &mut VerbosityContext,
    vs_capability: bool,
    meaning: SemanticMeaning,
) -> SymbolDisplayInfo {
    let container = {
        let nodes = program.arena_of(node);
        get_container_node(node, &nodes)
    };
    let dpw = new_display_parts_writer(vs_capability, &c.borrow(), program);

    // Source file for printer context.
    let source_file = {
        let nodes = program.arena_of(node);
        ast::get_source_file_of_node(Some(node), &nodes)
    };

    let mut state = QuickInfoState {
        c,
        program,
        dpw,
        vc,
        vs_capability,
        meaning,
        node,
        container,
        source_file,
        first_declaration: None,
        visited_aliases: Set::new(),
        alias_level: 0,
        symbol_was_expanded: false,
    };

    let node_kind = program.arena_of(node)[node].kind;
    if (node_kind == Kind::ThisKeyword
        && ast::is_in_expression_context(node, &program.arena_of(node)))
        || ast::is_this_in_type_query(node, &program.arena_of(node))
    {
        state.dpw.write_keyword("this");
        state.dpw.write_punctuation(": ");
        let t = state.checker().get_type_at_location(node);
        state.write_type_classified(t, container, TYPE_FORMAT_FLAGS);
        return SymbolDisplayInfo {
            display_parts: state.dpw,
            declaration: state.first_declaration,
        };
    }
    let Some(symbol) = symbol else {
        {
            let nodes = program.arena_of(node);
            if should_get_type(&nodes, node) {
                drop(nodes);
                let t = state.checker().get_type_at_location(node);
                state.write_type_classified(t, container, TYPE_FORMAT_FLAGS);
            }
        }
        return SymbolDisplayInfo {
            display_parts: state.dpw,
            declaration: state.first_declaration,
        };
    };

    state.write_symbol(symbol);

    SymbolDisplayInfo {
        display_parts: state.dpw,
        declaration: state.first_declaration,
    }
}

/// `getNodeForQuickInfo`.
fn get_node_for_quick_info(program: &Rc<Program>, node: NodeId) -> NodeId {
    let nodes = program.arena_of(node);
    let Some(parent) = nodes[node].parent else {
        return node;
    };
    if ast::is_new_expression(&nodes[parent]) && nodes[node].pos() == nodes[parent].pos() {
        return nodes[parent].expression().unwrap_or(node);
    }
    if ast::is_named_tuple_member(&nodes[parent]) && nodes[node].pos() == nodes[parent].pos() {
        return parent;
    }
    if ast::is_import_meta(&nodes[parent], &nodes) && nodes[parent].name() == Some(node) {
        return parent;
    }
    if ast::is_jsx_namespaced_name(&nodes[parent]) {
        return parent;
    }
    node
}

/// `getSymbolAtLocationForQuickInfo`.
fn get_symbol_at_location_for_quick_info(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    node: NodeId,
) -> Option<SymbolId> {
    if let Some(object_element) = {
        let nodes = program.arena_of(node);
        get_containing_object_literal_element(node, &nodes)
    } {
        let parent = program.arena_of(object_element)[object_element].parent;
        if let Some(parent) = parent {
            if let Some(contextual_type) = c
                .borrow_mut()
                .get_contextual_type_api(parent, tsc_checker::types::ContextFlags::NONE)
            {
                let properties = c
                    .borrow_mut()
                    .get_property_symbols_from_contextual_type(
                        object_element,
                        contextual_type,
                        false, /*unionSymbolOk*/
                    );
                if properties.len() == 1 {
                    return Some(properties[0]);
                }
            }
        }
    }
    c.borrow_mut().get_symbol_at_location_api(node)
}

/// `getSignaturesAtLocation`.
fn get_signatures_at_location(
    program: &Rc<Program>,
    c: &RefCell<Checker>,
    symbol: SymbolId,
    kind: SignatureKind,
    node: NodeId,
) -> Vec<SignatureId> {
    let signatures = {
        let mut checker = c.borrow_mut();
        let t = checker.get_type_of_symbol(symbol);
        let t = checker.remove_missing_or_undefined_type(t);
        checker.get_signatures_of_type(t, kind)
    };
    if signatures.len() > 1
        || signatures.len() == 1 && {
            !c.borrow()
                .signature_arena
                .get(signatures[0])
                .type_parameters()
                .is_empty()
        }
    {
        if let Some(call_node) = get_call_or_new_expression(program, node) {
            // We have a call or new expression, return the resolved signature.
            if let Some(sig) = c.borrow_mut().get_resolved_signature_api(call_node) {
                return vec![sig];
            }
        }
    }
    signatures
}

/// `getCallOrNewExpression`.
fn get_call_or_new_expression(program: &Rc<Program>, node: NodeId) -> Option<NodeId> {
    let nodes = program.arena_of(node);
    if ast::is_source_file(&nodes[node]) {
        return None;
    }
    let mut node = node;
    if let Some(parent) = nodes[node].parent {
        if ast::is_property_access_expression(&nodes[parent])
            && nodes[parent].name() == Some(node)
        {
            node = parent;
        }
    }
    if let Some(parent) = nodes[node].parent {
        if (ast::is_call_expression(&nodes[parent]) || ast::is_new_expression(&nodes[parent]))
            && nodes[parent].expression() == Some(node)
        {
            return Some(parent);
        }
    }
    None
}

/// `containsTypedefTag`.
fn contains_typedef_tag(nodes: &[Node], jsdoc: NodeId) -> bool {
    if nodes[jsdoc].kind == Kind::JSDoc {
        if let Some(tags) = &nodes[jsdoc].as_js_doc().tags {
            for &tag in &tags.nodes {
                if nodes[tag].kind == Kind::JSDocTypedefTag
                    || nodes[tag].kind == Kind::JSDocCallbackTag
                {
                    return true;
                }
            }
        }
    }
    false
}

/// `writeCode`.
fn write_code(b: &mut String, lang: &str, code: &str) {
    if code.is_empty() {
        return;
    }
    let mut ticks = 3;
    while code.contains(&"`".repeat(ticks)) {
        ticks += 1;
    }
    for _ in 0..ticks {
        b.push('`');
    }
    b.push_str(lang);
    b.push('\n');
    b.push_str(code);
    b.push('\n');
    for _ in 0..ticks {
        b.push('`');
    }
    b.push('\n');
}

/// `writeComments`.
fn write_comments(
    get_mapped_location: &DocumentationLocationMapper<'_>,
    b: &mut String,
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    comments: &[NodeId],
    is_markdown: bool,
) {
    for &comment in comments {
        let nodes = program.arena_of(comment);
        match nodes[comment].kind {
            Kind::JSDocText => {
                let text = nodes[comment].text(&nodes).into_owned();
                b.push_str(&text);
            }
            Kind::JSDocLink | Kind::JSDocLinkPlain => {
                drop(nodes);
                write_jsdoc_link(
                    get_mapped_location,
                    b,
                    program,
                    c,
                    comment,
                    false, /*quote*/
                    is_markdown,
                );
            }
            Kind::JSDocLinkCode => {
                drop(nodes);
                write_jsdoc_link(
                    get_mapped_location,
                    b,
                    program,
                    c,
                    comment,
                    true, /*quote*/
                    is_markdown,
                );
            }
            _ => {}
        }
    }
}

/// `writeJSDocLink`.
fn write_jsdoc_link(
    get_mapped_location: &DocumentationLocationMapper<'_>,
    b: &mut String,
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    link: NodeId,
    quote: bool,
    is_markdown: bool,
) {
    let (name, text) = {
        let nodes = program.arena_of(link);
        (
            nodes[link].name(),
            nodes[link]
                .text(&nodes)
                .trim_matches(' ')
                .to_string(),
        )
    };
    let Some(name) = name else {
        write_quoted_string(b, &text, quote && is_markdown);
        return;
    };
    {
        let nodes = program.arena_of(name);
        let name_text = nodes[name].text(&nodes).into_owned();
        if ast::is_identifier(&nodes[name])
            && (name_text == "http" || name_text == "https")
            && text.starts_with("://")
        {
            let mut link_text = format!("{}{}", name_text, text);
            let mut link_uri = link_text.clone();
            if let Some(comment_pos) = link_text.find(|ch| ch == ' ' || ch == '|') {
                link_uri = link_text[..comment_pos].to_string();
                link_text = trim_comment_prefix(&link_text[comment_pos..]);
                if link_text.is_empty() {
                    link_text = link_uri.clone();
                }
            }
            if is_markdown {
                write_markdown_link(b, &link_text, &link_uri, quote);
            } else {
                write_quoted_string(b, &link_text, false);
                if link_text != link_uri {
                    b.push_str(" (");
                    b.push_str(&link_uri);
                    b.push(')');
                }
            }
            return;
        }
    }
    write_name_link(
        get_mapped_location,
        b,
        program,
        c,
        Some(name),
        &text,
        quote,
        is_markdown,
    );
}

/// `writeNameLink`.
fn write_name_link(
    get_mapped_location: &DocumentationLocationMapper<'_>,
    b: &mut String,
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    name: Option<NodeId>,
    text: &str,
    quote: bool,
    is_markdown: bool,
) {
    let Some(name) = name else {
        write_quoted_string(b, text, quote && is_markdown);
        return;
    };
    let declarations = get_declarations_from_location(program, c, name);
    if !declarations.is_empty() {
        let declaration = declarations[0];
        let (file, node) = {
            let nodes = program.arena_of(declaration);
            let file = ast::get_source_file_of_node(Some(declaration), &nodes)
                .expect("source file of declaration");
            let node = ast::get_name_of_declaration(Some(declaration), &nodes)
                .unwrap_or(declaration);
            (file, node)
        };
        let range = {
            let nodes = program.nodes(file.file_index());
            create_range_from_node(node, file, &nodes)
        };
        let (loc, fidelity) = get_mapped_location(file, range);
        let prefix_len = if text.starts_with("()") { 2 } else { 0 };
        let mut link_text = trim_comment_prefix(&text[prefix_len..]);
        if link_text.is_empty() {
            link_text = format!(
                "{}{}",
                get_entity_name_string(program, name),
                &text[..prefix_len]
            );
        }
        if is_markdown && fidelity.is_single_segment() {
            let link_uri = format!(
                "{}#{},{}-{},{}",
                loc.uri,
                loc.range.start.line + 1,
                loc.range.start.character + 1,
                loc.range.end.line + 1,
                loc.range.end.character + 1
            );
            write_markdown_link(b, &link_text, &link_uri, quote);
        } else {
            write_quoted_string(b, &link_text, false);
        }
        return;
    }
    write_quoted_string(
        b,
        &format!(
            "{}{}{}",
            get_entity_name_string(program, name),
            if !text.is_empty() { " " } else { "" },
            text
        ),
        quote && is_markdown,
    );
}

/// `trimCommentPrefix`.
fn trim_comment_prefix(text: &str) -> String {
    text.trim_start_matches(' ')
        .trim_start_matches('|')
        .trim_start_matches(' ')
        .to_string()
}

/// `writeMarkdownLink`.
fn write_markdown_link(b: &mut String, text: &str, uri: &str, quote: bool) {
    b.push('[');
    write_quoted_string(b, text, quote);
    b.push_str("](");
    b.push_str(uri);
    b.push(')');
}

/// `writeOptionalEntityName`.
fn write_optional_entity_name(b: &mut String, nodes: &[Node], name: Option<NodeId>) {
    if let Some(name) = name {
        b.push(' ');
        write_entity_name_parts(b, nodes, name);
    }
}

/// `writeQuotedString`.
fn write_quoted_string(b: &mut String, s: &str, quote: bool) {
    if quote && !s.contains('`') {
        b.push('`');
        b.push_str(s);
        b.push('`');
    } else {
        b.push_str(s);
    }
}

/// `getEntityNameString`.
fn get_entity_name_string(program: &Rc<Program>, name: NodeId) -> String {
    let mut b = String::new();
    let nodes = program.arena_of(name);
    write_entity_name_parts(&mut b, &nodes, name);
    b
}

/// `writeEntityNameParts`.
fn write_entity_name_parts(b: &mut String, nodes: &[Node], node: NodeId) {
    match nodes[node].kind {
        Kind::Identifier => {
            let text = nodes[node].text(nodes).into_owned();
            b.push_str(&text);
        }
        Kind::QualifiedName => {
            let q = nodes[node].as_qualified_name();
            write_entity_name_parts(b, nodes, q.left.expect("qualified name left"));
            b.push('.');
            write_entity_name_parts(b, nodes, q.right.expect("qualified name right"));
        }
        Kind::PropertyAccessExpression => {
            write_entity_name_parts(b, nodes, nodes[node].expression().expect("expression"));
            b.push('.');
            write_entity_name_parts(b, nodes, nodes[node].name().expect("name"));
        }
        Kind::ParenthesizedExpression | Kind::ExpressionWithTypeArguments => {
            write_entity_name_parts(b, nodes, nodes[node].expression().expect("expression"));
        }
        Kind::JSDocNameReference => {
            write_entity_name_parts(b, nodes, nodes[node].name().expect("name"));
        }
        _ => {}
    }
}

/// `getDeclarationsFromLocation` (local copy — the definition.go helper is
/// sibling-owned).
fn get_declarations_from_location(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    node: NodeId,
) -> Vec<NodeId> {
    {
        let nodes = program.arena_of(node);
        if ast::is_identifier(&nodes[node])
            && nodes[node].parent.is_some_and(|p| ast::is_shorthand_property_assignment(&nodes[p]))
        {
            // Because name in short-hand property assignment has two different meanings: property name and property value,
            // using go-to-definition at such position should go to the variable declaration of the property value rather than
            // go to the declaration of the property name (in this case stay at the same position). However, if go-to-definition
            // is performed at the location of property access, we would like to go to definition of the property in the short-hand
            // assignment. This case and others are handled by the following code.
            // and the contextual type's property declarations
            drop(nodes);
            let shorthand_symbol = c.borrow_mut().get_resolved_symbol(node);
            // PORT: Go checks `shorthandSymbol != nil`; the Rust checker
            // returns `unknown_symbol` for a failed resolution instead.
            let mut declarations: Vec<NodeId> = if shorthand_symbol
                != c.borrow().get_unknown_symbol()
            {
                let arena = c.borrow().symbol_arena.clone();
                arena.get_ref(shorthand_symbol).declarations.clone()
            } else {
                Vec::new()
            };
            let mut contextual_declarations =
                get_declarations_from_object_literal_element(program, c, node);
            declarations.append(&mut contextual_declarations);
            return declarations;
        }

        if ast::is_property_name(&nodes[node])
            && nodes[node].parent.is_some_and(|p| ast::is_binding_element(&nodes[p]))
            && nodes[nodes[node].parent.expect("parent")]
                .parent
                .is_some_and(|p| ast::is_object_binding_pattern(&nodes[p]))
        {
            // If the node is the name of a BindingElement within an ObjectBindingPattern instead of just returning the
            // declaration of the symbol (which is itself), we should try to get to the original type of the
            // ObjectBindingPattern and return the property declaration for the referenced property.
            let parent = nodes[node].parent.expect("parent");
            let grandparent = nodes[parent].parent.expect("grandparent");
            let binding_el = &nodes[parent].as_binding_element();
            let binding_el_matches = binding_el.dot_dot_dot_token.is_none()
                && Some(node) == binding_el.property_name.or(nodes[parent].name());
            if binding_el_matches {
                if let Some(name) = ast::try_get_text_of_property_name(node, &nodes).0 {
                    drop(nodes);
                    let t = c.borrow_mut().get_type_at_location(grandparent);
                    let mut types = vec![t];
                    if c.borrow().types.get(t).is_union() {
                        types = c.borrow().types.get(t).types().to_vec();
                    }
                    let mut result = Vec::new();
                    for union_type in types {
                        if let Some(prop) =
                            c.borrow_mut().get_property_of_type(union_type, &name)
                        {
                            let arena = c.borrow().symbol_arena.clone();
                            result.extend(
                                arena.get_ref(prop).declarations.iter().copied(),
                            );
                        }
                    }
                    return result;
                }
            }
        }
    }

    let node = get_declaration_name_for_keyword(program, node);
    if let Some(symbol) = c.borrow_mut().get_symbol_at_location_api(node) {
        let mut symbol = symbol;
        {
            let arena = c.borrow().symbol_arena.clone();
            let arena = arena.clone();
            let flags = arena[symbol.index()].flags;
            if flags.intersects(SymbolFlags::CLASS)
                && !flags.intersects(SymbolFlags::FUNCTION | SymbolFlags::VARIABLE)
                && {
                    let nodes = program.arena_of(node);
                    nodes[node].kind == Kind::ConstructorKeyword
                }
            {
                if let Some(constructor) = arena[symbol.index()]
                    .members
                    .get(ast::INTERNAL_SYMBOL_NAME_CONSTRUCTOR)
                    .copied()
                {
                    symbol = constructor;
                }
            }
        }
        if c.borrow().symbol_arena.get_ref(symbol)
            .flags
            .intersects(SymbolFlags::ALIAS)
        {
            if let Some(resolved) = c.borrow_mut().get_aliased_symbol(symbol) {
                symbol = resolved;
            }
        }
        let object_literal_element_declarations =
            get_declarations_from_object_literal_element(program, c, node);
        if !object_literal_element_declarations.is_empty() {
            return object_literal_element_declarations;
        }
        let declarations = {
            let arena = c.borrow().symbol_arena.clone();
            arena.get_ref(symbol).declarations.clone()
        };
        if !declarations.is_empty() {
            return declarations;
        }
    }
    let index_infos = c.borrow_mut().get_index_signatures_at_location(node);
    if !index_infos.is_empty() {
        return index_infos;
    }
    Vec::new()
}

/// `getDeclarationsFromObjectLiteralElement` (local copy — definition.go) —
/// returns declarations from the contextual type of an object literal
/// element, if available.
fn get_declarations_from_object_literal_element(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    node: NodeId,
) -> Vec<NodeId> {
    let Some(element) = ({
        let nodes = program.arena_of(node);
        get_containing_object_literal_element(node, &nodes)
    }) else {
        return Vec::new();
    };

    let element_parent = program.arena_of(element)[element].parent;
    let Some(element_parent) = element_parent else {
        return Vec::new();
    };
    let Some(contextual_type) = c
        .borrow_mut()
        .get_contextual_type_api(element_parent, tsc_checker::types::ContextFlags::NONE)
    else {
        return Vec::new();
    };

    let mut properties = c
        .borrow_mut()
        .get_property_symbols_from_contextual_type(element, contextual_type, false /*unionSymbolOk*/);
    {
        let arena = c.borrow().symbol_arena.clone();
        let arena = arena.clone();
        let found = properties.iter().any(|&p| {
            arena[p.index()].value_declaration.is_some_and(|vd| {
                let nodes = program.arena_of(vd);
                nodes[vd].parent.is_some_and(|par| ast::is_object_literal_expression(&nodes[par]))
                    && ast::is_object_literal_element(&nodes[vd])
                    && nodes[vd].name() == Some(node)
            })
        });
        drop(arena);
        if found {
            if let Some(without_node_inferences_type) = c.borrow_mut().get_contextual_type_api(
                element_parent,
                tsc_checker::types::ContextFlags::IGNORE_NODE_INFERENCES,
            ) {
                let without_node_inferences_properties =
                    c.borrow_mut().get_property_symbols_from_contextual_type(
                        element,
                        without_node_inferences_type,
                        false, /*unionSymbolOk*/
                    );
                if !without_node_inferences_properties.is_empty() {
                    properties = without_node_inferences_properties;
                }
            }
        }
    }

    let mut result = Vec::new();
    {
        let arena = c.borrow().symbol_arena.clone();
        let arena = arena.clone();
        for prop in properties {
            result.extend(arena[prop.index()].declarations.iter().copied());
        }
    }
    result
}

/// `getDeclarationNameForKeyword` (local copy — definition.go).
fn get_declaration_name_for_keyword(program: &Rc<Program>, node: NodeId) -> NodeId {
    let nodes = program.arena_of(node);
    let kind = nodes[node].kind;
    if kind >= Kind::FIRST_KEYWORD && kind <= Kind::LAST_KEYWORD {
        if let Some(parent) = nodes[node].parent {
            if ast::is_variable_declaration_list(&nodes[parent]) {
                if let Some(decl) = nodes[parent]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .and_then(|d| d.nodes().first())
                    .copied()
                {
                    if nodes[decl].name().is_some() {
                        return nodes[decl].name().expect("name");
                    }
                }
            } else if nodes[parent].declaration_data().is_some()
                && nodes[parent].name().is_some()
                && nodes[node].pos() < nodes[nodes[parent].name().expect("name")].pos()
            {
                return nodes[parent].name().expect("name");
            }
        }
    }
    node
}
