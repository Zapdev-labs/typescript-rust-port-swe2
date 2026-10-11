// Ported from tsc/internal/ls/sourcedefinition.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - Files parsed on demand by `SourceDefResolver` are NOT in the program's
//   arena map — their `NodeId::file_index()` is freshly allocated by the
//   parser and `program.nodes(file_index)` would panic. Parsed files are
//   kept in `ParsedSourceFile` (own arena + binder symbols) and every node
//   access goes through `SourceDefResolver::with_nodes`/`with_nodes_mut`,
//   which dispatches to the parsed arena by `file_index` first and falls
//   back to the program arena.
// - Because `LanguageService::source_file_range_to_lsp_location_for_feature`
//   would hit the panic above, the resolver carries a local copy plus a
//   local `get_mapped_location`/`create_definition_locations` (the Go code
//   calls the shared ones; behavior is identical).
// - `collections.Set[tspath.RootedFilePath]`/`Set[string]` become
//   `HashSet`s; `declarationKey` dedup is a `HashSet<(RootedFilePath,
//   TextRange)>`.
// - Go's `*ast.SourceFile` results become `NodeId` (the `Kind::SourceFile`
//   node); its arena is resolved lazily via `with_nodes`.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::symbol::Symbol;
use tsc_ast::{self as ast, Kind, ModifierFlags, Node, NodeId};
use tsc_checker::checker_core::Checker;
use tsc_compiler::program::Program;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::context::Context;
use tsc_core::core::ensure_script_kind_from_file_name;
use tsc_core::options_generated::{CompilerOptions, ModuleKind};
use tsc_core::text::{TextPos, TextRange};
use tsc_core::tristate::TS_TRUE;
use tsc_lsconv::converters::{Script, source_file_script};
use tsc_lsproto::{self as lsproto};
use tsc_module::{DefaultResolver, ResolutionHost, ResolverOptions};
use tsc_sourcemap::DocumentPosition;
use tsc_spanmap::{Feature, Fidelity, SpanMap};
use tsc_tspath::{RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

use crate::api::Error;
use crate::definition::{
    combine_definition_responses, get_declarations_from_location, lsp_range_contains,
    try_get_signature_declaration,
};
use crate::findallreferences::get_file_and_start_pos_from_declaration;
use crate::languageservice::LanguageService;
use crate::utilities::*;

/// `type parsedFiles map entry` — a source file parsed on demand by the
/// `sourceDefResolver`, owning its node arena and binder symbol output.
struct ParsedSourceFile {
    file: NodeId,
    nodes: RefCell<Vec<Node>>,
    #[allow(dead_code)]
    symbols: RefCell<Vec<Symbol>>,
}

/// `type sourceDefResolutionHost struct` — implements `module.ResolutionHost`.
struct SourceDefResolutionHost {
    fs: Arc<dyn Vfs>,
    current_directory: RootedDirectoryPath,
}

impl ResolutionHost for SourceDefResolutionHost {
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }
    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.current_directory.clone()
    }
}

/// `type sourceDefResolver struct` — resolves source definitions by mapping
/// .d.ts declarations to their implementation files (.js/.ts). Uses the NoDts
/// module resolver and file parsing, but never acquires the type checker.
struct SourceDefResolver<'a, 'h> {
    ls: &'a LanguageService<'h>,
    fs: Arc<dyn Vfs>,
    options: Rc<CompilerOptions>,
    program: Rc<Program>,
    resolve_from: RootedFilePath,
    resolver: DefaultResolver,
    parsed_files: RefCell<HashMap<RootedFilePath, Option<Rc<ParsedSourceFile>>>>,
    /// `file_index` → parsed arena, so `with_nodes` can resolve `NodeId`s
    /// that do not belong to the program.
    parsed_by_index: RefCell<HashMap<u32, Rc<ParsedSourceFile>>>,
}

impl<'a, 'h> SourceDefResolver<'a, 'h> {
    /// Resolve `node`'s owning arena — a parsed file's arena or the program's.
    fn with_nodes<R>(&self, node: NodeId, f: impl FnOnce(&[Node]) -> R) -> R {
        if let Some(parsed) = self
            .parsed_by_index
            .borrow()
            .get(&node.file_index())
            .cloned()
        {
            let nodes = parsed.nodes.borrow();
            return f(&nodes);
        }
        let nodes = self.program.nodes(node.file_index());
        f(&nodes)
    }

    /// Mutable variant of `with_nodes` for helpers that need `&mut Vec<Node>`
    /// (`astnav::get_touching_property_name`).
    fn with_nodes_mut<R>(&self, node: NodeId, f: impl FnOnce(&mut Vec<Node>) -> R) -> R {
        if let Some(parsed) = self
            .parsed_by_index
            .borrow()
            .get(&node.file_index())
            .cloned()
        {
            let mut nodes = parsed.nodes.borrow_mut();
            return f(&mut nodes);
        }
        let mut nodes = self.program.nodes_mut(node.file_index());
        f(&mut nodes)
    }

    /// `resolveFromCheckerInfo` — map type-checker declarations to source
    /// implementations using only the NoDts module resolver and file parsing.
    fn resolve_from_checker_info(
        &self,
        node: NodeId,
        mut resolved_impl_file: RootedFilePath,
        checker_declarations: &[NodeId],
        module_specifier: &str,
    ) -> Vec<NodeId> {
        // If we don't yet have a forward-resolved implementation file, try to
        // recover a module specifier from the checker (e.g. from the import that
        // brought the symbol into scope, or from the root of an access expression).
        if resolved_impl_file.as_string().is_empty() && !module_specifier.is_empty() {
            resolved_impl_file = self.resolve_implementation(
                module_specifier,
                self.infer_implied_node_format(&self.resolve_from),
            );
        }

        // For property access where the checker found no declarations (e.g.
        // mapped types), search the implementation file for the property name.
        if checker_declarations.is_empty() && !resolved_impl_file.as_string().is_empty() {
            let names = self.get_candidate_source_declaration_names(Some(node), None);
            let results =
                self.search_implementation_file(Some(node), &resolved_impl_file, &names);
            if !results.is_empty() {
                return self.unique_declaration_nodes(results);
            }
        }

        let mut declarations: Vec<NodeId> = Vec::new();
        for &declaration in checker_declarations {
            declarations.extend(
                self.map_declaration_to_source(node, declaration, &resolved_impl_file),
            );
        }
        let declarations = self.unique_declaration_nodes(declarations);
        if has_concrete_source_declarations(self, &declarations) {
            return declarations;
        }
        Vec::new()
    }

    /// `resolveTripleSlashReference` — handle /// <reference path/types="..."/>.
    /// Returns the entry declarations plus the `FileReference`.
    fn resolve_triple_slash_reference(
        &self,
        file: NodeId,
        pos: TextPos,
        program: &Rc<Program>,
    ) -> (Vec<NodeId>, Option<tsc_ast::ast::FileReference>) {
        let reference = {
            let mut nodes = program.nodes_mut(file.file_index());
            get_reference_at_position(&mut nodes, file, pos, program)
        };
        let Some(reference) = reference else {
            return (Vec::new(), None);
        };
        let Some(ref_file) = reference.file else {
            return (Vec::new(), None);
        };

        // If the referenced file is already an implementation file, return it
        // directly.
        let ref_is_declaration = {
            let nodes = program.nodes(ref_file.file_index());
            nodes[ref_file].as_source_file().is_declaration_file
        };
        if !ref_is_declaration {
            let declarations =
                self.with_nodes(ref_file, |nodes| get_source_definition_entry_declarations(ref_file, nodes));
            return (declarations, reference.reference);
        }

        // The referenced file is a .d.ts. Try to find the implementation file
        // using the NoDts module resolver via
        // findImplementationFileFromDtsFileName.
        let dts_file_name = {
            let nodes = program.nodes(ref_file.file_index());
            nodes[ref_file].as_source_file().file_name().clone()
        };
        let preferred_mode = self.infer_implied_node_format(&dts_file_name);
        let implementation_file =
            self.find_implementation_file_from_dts_file_name(&dts_file_name, preferred_mode);
        if implementation_file.as_string().is_empty() {
            return (Vec::new(), None);
        }

        let Some(source_file) = self.get_or_parse_source_file(&implementation_file) else {
            return (Vec::new(), None);
        };
        let declarations = self.with_nodes(source_file, |nodes| {
            get_source_definition_entry_declarations(source_file, nodes)
        });
        (declarations, reference.reference)
    }

    /// `searchImplementationFile` — search an implementation file for
    /// declarations matching `names`.
    fn search_implementation_file(
        &self,
        original_node: Option<NodeId>,
        implementation_file: &RootedFilePath,
        names: &[String],
    ) -> Vec<NodeId> {
        if implementation_file.as_string().is_empty() {
            return Vec::new();
        }
        let Some(source_file) = self.get_or_parse_source_file(implementation_file) else {
            return Vec::new();
        };
        let is_default_import = original_node.is_some_and(|n| {
            self.with_nodes(n, |nodes| is_default_import_name(n, nodes))
        });
        if is_default_import {
            // For default imports, only search for "default" declarations to
            // avoid matching unrelated declarations with the same identifier
            // name.
            let default_declarations = self.find_declarations_in_file(
                implementation_file,
                &["default".to_string()],
                &mut HashSet::new(),
            );
            if !default_declarations.is_empty() {
                return filter_preferred_source_declarations(
                    self,
                    original_node,
                    default_declarations,
                );
            }
            return self.with_nodes(source_file, |nodes| {
                get_source_definition_entry_declarations(source_file, nodes)
            });
        }
        let declarations = self.find_declarations_in_file(
            implementation_file,
            names,
            &mut HashSet::new(),
        );
        if !declarations.is_empty() {
            return filter_preferred_source_declarations(self, original_node, declarations);
        }
        Vec::new()
    }

    /// `mapDeclarationToSource`.
    fn map_declaration_to_source(
        &self,
        original_node: NodeId,
        declaration: NodeId,
        resolved_impl_file: &RootedFilePath,
    ) -> Vec<NodeId> {
        let (file, start_pos) =
            self.with_nodes(declaration, |nodes| {
                get_file_and_start_pos_from_declaration(declaration, nodes)
            });
        let file_name = self.with_nodes(file, |nodes| {
            nodes[file].as_source_file().file_name().clone()
        });

        if let Some(mapped) = self.ls.try_get_source_position(&file_name, start_pos) {
            if let Some(source_file) = self.get_or_parse_source_file(&mapped.file_name) {
                let decl = find_closest_declaration_node(self, source_file, mapped.pos);
                return vec![decl];
            }
        }

        if !file_name.is_declaration_file() {
            return vec![declaration];
        }

        let mut implementation_file = resolved_impl_file.clone();
        if implementation_file.as_string().is_empty() {
            // Reverse-resolve .d.ts path to implementation file. This path is
            // only reached for declarations with no associated module
            // specifier (e.g. globals, ambient declarations, or when forward
            // resolution failed).
            let dts_file_name = self.with_nodes(declaration, |nodes| {
                let file = ast::get_source_file_of_node(Some(declaration), nodes)
                    .expect("source file of declaration");
                nodes[file].as_source_file().file_name().clone()
            });
            let preferred_mode = self.infer_implied_node_format(&dts_file_name);
            implementation_file =
                self.find_implementation_file_from_dts_file_name(&dts_file_name, preferred_mode);
        }

        let names = self.get_candidate_source_declaration_names(
            Some(original_node),
            Some(declaration),
        );
        self.search_implementation_file(Some(original_node), &implementation_file, &names)
    }

    /// `findImplementationFileFromDtsFileName`.
    fn find_implementation_file_from_dts_file_name(
        &self,
        dts_file_name: &RootedFilePath,
        preferred_mode: ResolutionMode,
    ) -> RootedFilePath {
        let js_ext =
            tsc_module::util::try_get_js_extension_for_file_name(dts_file_name, &self.options);
        if !js_ext.is_empty() {
            let candidate = dts_file_name.change_extension(js_ext);
            if self.fs.file_exists(&candidate) {
                return candidate;
            }
        }

        let Some(parts) =
            tsc_modulespecifiers::util::get_node_module_path_parts(dts_file_name)
        else {
            return RootedFilePath::default();
        };

        if parts.has_nested_node_modules || parts.is_direct_node_modules_file {
            return RootedFilePath::default();
        }

        let package_name = tsc_module::util::get_package_name_from_types_package_name(
            &tsc_module::util::unmangle_scoped_package_name(&parts.package_name),
        );
        if package_name.is_empty() {
            return RootedFilePath::default();
        }

        // Try resolving as a package subpath first (e.g. "pkg/dist/utils"), then
        // fall back to the bare package name (e.g. "pkg"). This covers both main
        // entrypoints and deep imports without needing to inspect package.json
        // entrypoints.
        if !parts.package_relative_path.as_string().is_empty() {
            let specifier = tsc_tspath::to_module_specifier(&package_name)
                .resolve_relative(&parts.package_relative_path)
                .remove_file_extension();
            let implementation_file =
                self.resolve_implementation(specifier.as_string(), preferred_mode);
            if !implementation_file.as_string().is_empty() {
                return implementation_file;
            }
        }
        self.resolve_implementation(&package_name, preferred_mode)
    }

    /// `resolveImplementation`.
    fn resolve_implementation(
        &self,
        module_name: &str,
        preferred_mode: ResolutionMode,
    ) -> RootedFilePath {
        self.resolve_implementation_from(module_name, &self.resolve_from, preferred_mode)
    }

    /// `resolveImplementationFrom`.
    fn resolve_implementation_from(
        &self,
        module_name: &str,
        resolve_from_file: &RootedFilePath,
        preferred_mode: ResolutionMode,
    ) -> RootedFilePath {
        let mut modes = vec![preferred_mode];
        if preferred_mode != ModuleKind::ESNext {
            modes.push(ModuleKind::ESNext);
        }
        if preferred_mode != ModuleKind::CommonJS {
            modes.push(ModuleKind::CommonJS);
        }

        for mode in modes {
            let (resolved, _diags) = self.resolver.resolve_module_name(
                module_name,
                resolve_from_file,
                mode,
                None,
            );
            if let Some(resolved) = resolved {
                if resolved.is_resolved()
                    && !resolved.resolved_file_name.is_declaration_file()
                {
                    return resolved.resolved_file_name;
                }
            }
        }
        RootedFilePath::default()
    }

    /// `getOrParseSourceFile`.
    fn get_or_parse_source_file(&self, file_name: &RootedFilePath) -> Option<NodeId> {
        if let Some(source_file) = self.program.get_source_file(file_name) {
            return Some(source_file);
        }
        if let Some(entry) = self.parsed_files.borrow().get(file_name) {
            return entry.as_ref().map(|p| p.file);
        }
        let parsed = self.ls.read_file(file_name).map(|text| {
            let (file, mut nodes) = tsc_parser::parser::parse_source_file(
                SourceFileParseOptions {
                    file_name: file_name.clone(),
                    path_key: self.program.path_key_for_file_name(file_name),
                    ..Default::default()
                },
                &text,
                // A declaration map's `sources` entries are arbitrary strings,
                // so the file name here may not have a recognized extension.
                ensure_script_kind_from_file_name(file_name),
            );
            let mut symbols = Vec::new();
            tsc_binder::binder::bind_source_file(&mut nodes, file, &mut symbols);
            Rc::new(ParsedSourceFile {
                file,
                nodes: RefCell::new(nodes),
                symbols: RefCell::new(symbols),
            })
        });
        if let Some(p) = &parsed {
            self.parsed_by_index
                .borrow_mut()
                .insert(p.file.file_index(), p.clone());
        }
        self.parsed_files
            .borrow_mut()
            .insert(file_name.clone(), parsed.clone());
        parsed.map(|p| p.file)
    }

    /// `inferImpliedNodeFormat` — determine the module format for a source
    /// file that may not be in the program, using the file extension and
    /// nearest package.json "type" field.
    fn infer_implied_node_format(&self, file_name: &RootedFilePath) -> ResolutionMode {
        let mut package_json_type = String::new();
        if let Some(scope) = self
            .resolver
            .get_package_scope_for_path(&file_name.directory())
        {
            if let Some(contents) = &scope.contents {
                if let Some(value) = contents.type_.get_value() {
                    package_json_type = value.clone();
                }
            }
        }
        ast::get_implied_node_format_for_file(file_name, &package_json_type)
    }

    /// `findDeclarationsInFile`.
    fn find_declarations_in_file(
        &self,
        file_name: &RootedFilePath,
        names: &[String],
        seen: &mut HashSet<RootedFilePath>,
    ) -> Vec<NodeId> {
        if file_name.as_string().is_empty() || names.is_empty() {
            return Vec::new();
        }
        if !seen.insert(file_name.clone()) {
            return Vec::new();
        }

        let Some(source_file) = self.get_or_parse_source_file(file_name) else {
            return Vec::new();
        };

        let declarations = self.with_nodes(source_file, |nodes| {
            find_declaration_nodes_by_name(source_file, names, nodes)
        });
        if !declarations.is_empty() && has_concrete_source_declarations(self, &declarations) {
            return declarations;
        }

        let mut forwarded: Vec<NodeId> = Vec::new();
        for forwarded_file in self.get_forwarded_implementation_files(source_file) {
            forwarded.extend(
                self.find_declarations_in_file(&forwarded_file, names, seen),
            );
        }
        if !forwarded.is_empty() {
            if has_concrete_source_declarations(self, &forwarded) {
                return self.unique_declaration_nodes(forwarded);
            }
            let mut all = declarations;
            all.extend(forwarded);
            return self.unique_declaration_nodes(all);
        }
        declarations
    }

    /// `getForwardedImplementationFiles`.
    fn get_forwarded_implementation_files(&self, source_file: NodeId) -> Vec<RootedFilePath> {
        let preferred_mode = self.infer_implied_node_format(&self.with_nodes(source_file, |nodes| {
            nodes[source_file].as_source_file().file_name().clone()
        }));

        let imports: Vec<NodeId> = self.with_nodes(source_file, |nodes| {
            nodes[source_file].as_source_file().imports().to_vec()
        });
        let source_file_name = self.with_nodes(source_file, |nodes| {
            nodes[source_file].as_source_file().file_name().clone()
        });
        let mut files = Vec::new();
        for imp in imports {
            let module_name = self.with_nodes(imp, |nodes| nodes[imp].text(nodes).into_owned());
            let implementation_file = self.resolve_implementation_from(
                &module_name,
                &source_file_name,
                preferred_mode,
            );
            if !implementation_file.as_string().is_empty() {
                files.push(implementation_file);
            }
        }
        files.sort_by(|a, b| a.as_string().cmp(b.as_string()));
        files.dedup_by(|a, b| a.as_string() == b.as_string());
        files
    }

    /// `getCandidateSourceDeclarationNames`.
    fn get_candidate_source_declaration_names(
        &self,
        original_node: Option<NodeId>,
        declaration: Option<NodeId>,
    ) -> Vec<String> {
        let mut names: Vec<String> = Vec::new();
        if let Some(declaration) = declaration {
            self.with_nodes(declaration, |nodes| {
                if let Some(name) = ast::get_name_of_declaration(Some(declaration), nodes) {
                    let text = ast::get_text_of_property_name(name, nodes);
                    if !text.is_empty() {
                        names.push(text);
                    }
                }
                if nodes[declaration].kind == Kind::ExportAssignment {
                    names.push("default".to_string());
                }
                if (ast::is_function_declaration(&nodes[declaration])
                    || ast::is_class_declaration(&nodes[declaration]))
                    && nodes[declaration]
                        .modifier_flags()
                        .intersects(ModifierFlags::EXPORT_DEFAULT)
                {
                    names.push("default".to_string());
                }
                if ast::is_import_specifier(&nodes[declaration])
                    || ast::is_export_specifier(&nodes[declaration])
                {
                    if let Some(prop_name) = nodes[declaration].property_name() {
                        names.push(nodes[prop_name].text(nodes).into_owned());
                    }
                }
            });
        }
        if let Some(original_node) = original_node {
            self.with_nodes(original_node, |nodes| {
                if ast::is_identifier(&nodes[original_node])
                    || ast::is_private_identifier(&nodes[original_node])
                {
                    names.push(nodes[original_node].text(nodes).into_owned());
                }
                if is_default_import_name(original_node, nodes) {
                    names.push("default".to_string());
                }
                if let Some(parent) = nodes[original_node].parent {
                    if ast::is_import_specifier(&nodes[parent])
                        || ast::is_export_specifier(&nodes[parent])
                    {
                        if let Some(prop_name) = nodes[parent].property_name() {
                            names.push(nodes[prop_name].text(nodes).into_owned());
                        }
                    }
                }
            });
        }
        names
    }

    /// `uniqueDeclarationNodes`.
    fn unique_declaration_nodes(&self, nodes_list: Vec<NodeId>) -> Vec<NodeId> {
        let mut seen: HashSet<(RootedFilePath, TextRange)> = HashSet::new();
        let mut result = Vec::with_capacity(nodes_list.len());
        for node in nodes_list {
            let key = self.with_nodes(node, |nodes| {
                let file = ast::get_source_file_of_node(Some(node), nodes);
                let file_name = file
                    .map(|f| nodes[f].as_source_file().file_name().clone())
                    .unwrap_or_default();
                (file_name, nodes[node].loc)
            });
            if !seen.insert(key) {
                continue;
            }
            result.push(node);
        }
        result
    }

    /// `sourceFileRangeToLSPLocationForFeature` — resolver-local variant of
    /// the LS helper that works for parsed (non-program) source files.
    fn source_file_range_to_lsp_location_for_feature(
        &self,
        file: NodeId,
        file_range: TextRange,
        feature: Feature,
    ) -> (lsproto::Location, Fidelity) {
        enum Out {
            Early((lsproto::Location, Fidelity)),
            Mapped(RootedFilePath),
        }
        let out = self.with_nodes(file, |nodes| {
            if !nodes[file].as_source_file().content_mapper().is_empty() {
                let script = source_file_script(file, nodes);
                Out::Early(
                    self.ls
                        .converters
                        .to_lsp_location_for_feature(&script, file_range, feature),
                )
            } else {
                Out::Mapped(nodes[file].as_source_file().file_name().clone())
            }
        });
        match out {
            Out::Early(result) => result,
            Out::Mapped(file_name) => self.get_mapped_location(&file_name, file_range),
        }
    }

    /// `getMappedLocation` — local copy (source_map.rs's is module-private).
    fn get_mapped_location(
        &self,
        file_name: &RootedFilePath,
        file_range: TextRange,
    ) -> (lsproto::Location, Fidelity) {
        let start_pos = self.ls.try_get_source_position(file_name, file_range.pos());
        let Some(start_pos) = start_pos else {
            let script = self.get_script(file_name);
            let (lsp_range, fidelity) =
                self.ls.create_lsp_range_from_range(file_range, &script);
            return (
                lsproto::Location {
                    uri: tsc_lsconv::converters::file_name_to_document_uri(file_name),
                    range: lsp_range,
                },
                fidelity,
            );
        };
        let end_pos = match self.ls.try_get_source_position(file_name, file_range.end()) {
            Some(end_pos)
                if end_pos.file_name == start_pos.file_name
                    && end_pos.pos >= start_pos.pos =>
            {
                end_pos
            }
            _ => DocumentPosition {
                file_name: start_pos.file_name.clone(),
                pos: start_pos.pos + file_range.len(),
            },
        };
        let new_range = TextRange::new(start_pos.pos, end_pos.pos);
        let script = self.get_script(&start_pos.file_name);
        let (lsp_range, fidelity) = self.ls.create_lsp_range_from_range(new_range, &script);
        (
            lsproto::Location {
                uri: tsc_lsconv::converters::file_name_to_document_uri(&start_pos.file_name),
                range: lsp_range,
            },
            fidelity,
        )
    }

    /// `getScript` — a plain-text `lsconv.Script` for files that may not be
    /// in the program.
    fn get_script(&self, file_name: &RootedFilePath) -> SourceDefScript {
        let text = self
            .ls
            .read_file(file_name)
            .expect("file should be readable");
        SourceDefScript {
            file_name: file_name.clone(),
            text,
        }
    }

    /// `createDefinitionLocations` — resolver-local variant that resolves
    /// declaration arenas via `with_nodes` (declarations may live in parsed
    /// files outside the program).
    fn create_definition_locations(
        &self,
        origin_selection_range: lsproto::Range,
        client_supports_link: bool,
        declarations: &[NodeId],
        feature: Feature,
    ) -> lsproto::DefinitionResponse {
        let mut locations: Vec<lsproto::LocationLink> = Vec::new();
        // `fileRange{file, textRange}` dedup — `file` is the source-file `NodeId`.
        let mut location_ranges: Vec<(NodeId, TextRange)> = Vec::new();

        for &decl in declarations {
            let Some((file, name_range, context_range)) = self.with_nodes(decl, |nodes| {
                let file = ast::get_source_file_of_node(Some(decl), nodes)?;
                let name = ast::get_name_of_declaration(Some(decl), nodes).unwrap_or(decl);
                let name_range = if nodes[name].kind == Kind::EmptyStatement {
                    TextRange::new(nodes[name].pos(), nodes[name].pos())
                } else {
                    create_range_from_node(name, file, nodes)
                };
                let context_node =
                    crate::findallreferences::get_context_node(decl, nodes).unwrap_or(decl);
                let context_range =
                    to_context_range(name_range, file, Some(context_node), nodes)
                        .unwrap_or(name_range);
                let context_range = if !name_range.contained_by(&context_range) {
                    TextRange::new(
                        name_range.pos().min(context_range.pos()),
                        name_range.end().max(context_range.end()),
                    )
                } else {
                    context_range
                };
                Some((file, name_range, context_range))
            }) else {
                continue;
            };
            if location_ranges.contains(&(file, name_range)) {
                continue;
            }
            location_ranges.push((file, name_range));
            let (target_selection_loc, selection_fidelity) = self
                .source_file_range_to_lsp_location_for_feature(file, name_range, feature);
            if !selection_fidelity.is_single_segment() {
                continue;
            }
            let (mut target_loc, context_fidelity) =
                self.source_file_range_to_lsp_location_for_feature(
                    file,
                    context_range,
                    feature,
                );
            if context_fidelity.is_none()
                || target_loc.uri != target_selection_loc.uri
                || !lsp_range_contains(&target_loc.range, &target_selection_loc.range)
            {
                target_loc = target_selection_loc.clone();
            }
            locations.push(lsproto::LocationLink {
                origin_selection_range: Some(origin_selection_range.clone()),
                target_selection_range: target_selection_loc.range,
                target_uri: target_loc.uri,
                target_range: target_loc.range,
                ..Default::default()
            });
        }

        if client_supports_link {
            return lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
                definition_links: Some(locations),
                ..Default::default()
            };
        }
        let locations_vec: Vec<lsproto::Location> = locations
            .iter()
            .map(|link| lsproto::Location {
                uri: link.target_uri.clone(),
                range: link.target_selection_range.clone(),
            })
            .collect();
        lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
            locations: Some(locations_vec),
            ..Default::default()
        }
    }
}

/// `type script struct` — a plain-text `lsconv.Script` for files that may not
/// be in the program (mirrors `PlainScript` in source_map.rs, which is
/// module-private).
struct SourceDefScript {
    file_name: RootedFilePath,
    text: String,
}

impl Script for SourceDefScript {
    fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    fn original_file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    fn text(&self) -> &[u8] {
        self.text.as_bytes()
    }

    fn original_text(&self) -> &[u8] {
        self.text.as_bytes()
    }

    fn span_map(&self) -> Option<Arc<SpanMap>> {
        None
    }
}

impl<'h> LanguageService<'h> {
    /// `ProvideSourceDefinition`.
    pub fn provide_source_definition(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        position: lsproto::Position,
    ) -> Result<lsproto::DefinitionResponse, Error> {
        let (program, file) = self.get_program_and_file(document_uri);
        let nodes = program.nodes(file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            file,
            &nodes,
            position,
            Feature::Definition,
        );
        let mut results: Vec<lsproto::DefinitionResponse> = Vec::with_capacity(positions.len());
        for mapped in &positions {
            if mapped.fidelity.is_single_segment() {
                results.push(self.provide_source_definition_at_position(
                    ctx,
                    &program,
                    mapped.script.file,
                    mapped.position,
                )?);
            }
        }
        Ok(combine_definition_responses(
            results,
            lsproto::get_client_capabilities(ctx)
                .text_document
                .definition
                .link_support,
        ))
    }

    /// `provideSourceDefinitionAtPosition`.
    fn provide_source_definition_at_position(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        file: NodeId,
        text_pos: TextPos,
    ) -> Result<lsproto::DefinitionResponse, Error> {
        let caps = lsproto::get_client_capabilities(ctx);
        let client_supports_link = caps.text_document.definition.link_support;

        let pos = text_pos;
        let file_name = {
            let nodes = program.nodes(file.file_index());
            nodes[file].as_source_file().file_name().clone()
        };
        let resolver = self.new_source_def_resolver(program, file_name);
        let node = {
            let mut nodes = program.nodes_mut(file.file_index());
            tsc_astnav::tokens::get_touching_property_name(&mut nodes, file, pos)
        }
        .expect("GetTouchingPropertyName should return a node");

        let nodes = program.nodes(file.file_index());
        if ast::is_source_file(&nodes[node]) {
            // Triple-slash directives are comments, not AST nodes, so
            // GetTouchingPropertyName returns the SourceFile node.
            let (declarations, reference) =
                resolver.resolve_triple_slash_reference(file, pos, program);
            if !declarations.is_empty() {
                let reference = reference.expect("FileReference for triple-slash result");
                let (origin_selection_range, _fidelity) = self.create_lsp_range_from_bounds(
                    reference.text_range.pos(),
                    reference.text_range.end(),
                    file,
                );
                drop(nodes);
                return Ok(resolver.create_definition_locations(
                    origin_selection_range,
                    client_supports_link,
                    &declarations,
                    Feature::Definition,
                ));
            }
            drop(nodes);
            return Ok(lsproto::LocationOrLocationsOrDefinitionLinksOrNull::default());
        }

        let (origin_selection_range, _fidelity) = self.create_lsp_range_from_node(node, file);

        let containing_module_specifier = find_containing_module_specifier(node, &nodes);
        if containing_module_specifier.is_some_and(|ms| {
            nodes[ms]
                .parent
                .is_some_and(|p| ast::is_source_phase_import(&nodes[p], &nodes))
        }) {
            drop(nodes);
            return Ok(self.provide_definition_at_position(
                ctx,
                program,
                file,
                text_pos,
                client_supports_link,
            ));
        }

        // If the cursor is directly on a module specifier string, resolve to
        // the implementation file's entry point.
        if containing_module_specifier == Some(node) {
            let specifier = containing_module_specifier.expect("module specifier");
            let specifier_mode =
                program.get_mode_for_usage_location(&program.file_has_file_name(file), specifier);
            let specifier_text = nodes[specifier].text(&nodes).into_owned();
            drop(nodes);
            let implementation_file =
                resolver.resolve_implementation(&specifier_text, specifier_mode);
            if !implementation_file.as_string().is_empty() {
                if let Some(source_file) =
                    resolver.get_or_parse_source_file(&implementation_file)
                {
                    let declarations = resolver.with_nodes(source_file, |sf_nodes| {
                        get_source_definition_entry_declarations(source_file, sf_nodes)
                    });
                    return Ok(resolver.create_definition_locations(
                        origin_selection_range,
                        client_supports_link,
                        &declarations,
                        Feature::Definition,
                    ));
                }
            }
            return Ok(self.provide_definition_at_position(
                ctx,
                program,
                file,
                text_pos,
                client_supports_link,
            ));
        }

        // Phase 1: Syntactic fast path — when the cursor is inside an
        // import/require/export, forward-resolve the module specifier to an
        // implementation file and search it directly. This avoids acquiring
        // the type checker entirely when the fast path succeeds.
        let mut resolved_impl_file = RootedFilePath::default();
        if let Some(containing_module_specifier) = containing_module_specifier {
            let specifier_mode = program.get_mode_for_usage_location(
                &program.file_has_file_name(file),
                containing_module_specifier,
            );
            let specifier_text = nodes[containing_module_specifier].text(&nodes).into_owned();
            resolved_impl_file =
                resolver.resolve_implementation(&specifier_text, specifier_mode);
        }

        if !resolved_impl_file.as_string().is_empty() {
            let names = resolver.get_candidate_source_declaration_names(Some(node), None);
            let module_results =
                resolver.search_implementation_file(Some(node), &resolved_impl_file, &names);
            if !module_results.is_empty()
                && (!ast::is_part_of_type_node(node, &nodes)
                    && !ast::is_part_of_type_only_import_or_export_declaration(node, &nodes)
                    || has_concrete_source_declarations(&resolver, &module_results))
            {
                let declarations = resolver.unique_declaration_nodes(module_results);
                drop(nodes);
                return Ok(resolver.create_definition_locations(
                    origin_selection_range,
                    client_supports_link,
                    &declarations,
                    Feature::Definition,
                ));
            }
        }
        drop(nodes);

        // Phase 2: Type checker path — acquire the checker for the original
        // file and use its declarations and module specifier to map to source
        // implementations. This is the only point where the checker is used;
        // after this, only the NoDts module resolver and file parsing are
        // needed.
        let (checker_declarations, module_specifier) =
            get_source_def_checker_info(ctx, program, file, node);

        // Phase 3: Map checker results to source definitions.
        let declarations = resolver.resolve_from_checker_info(
            node,
            resolved_impl_file.clone(),
            &checker_declarations,
            &module_specifier,
        );
        if declarations.is_empty() {
            // If we resolved an implementation file from an import/export but
            // couldn't find specific declarations, fall back to the file entry
            // point rather than the standard definition provider — unless the
            // checker found declarations that are all type-only (e.g.
            // interfaces), in which case the .d.ts definition is more
            // appropriate.
            if containing_module_specifier.is_some()
                && !resolved_impl_file.as_string().is_empty()
                && !has_concrete_source_declarations(&resolver, &checker_declarations)
            {
                if let Some(source_file) =
                    resolver.get_or_parse_source_file(&resolved_impl_file)
                {
                    let entry_declarations = resolver.with_nodes(source_file, |sf_nodes| {
                        get_source_definition_entry_declarations(source_file, sf_nodes)
                    });
                    return Ok(resolver.create_definition_locations(
                        origin_selection_range,
                        client_supports_link,
                        &entry_declarations,
                        Feature::Definition,
                    ));
                }
            }
            return Ok(self.provide_definition_at_position(
                ctx,
                program,
                file,
                text_pos,
                client_supports_link,
            ));
        }
        Ok(resolver.create_definition_locations(
            origin_selection_range,
            client_supports_link,
            &declarations,
            Feature::Definition,
        ))
    }

    /// `newSourceDefResolver`.
    fn new_source_def_resolver<'a>(
        &'a self,
        program: &Rc<Program>,
        resolve_from: RootedFilePath,
    ) -> SourceDefResolver<'a, 'h> {
        let options = program.options();
        let mut no_dts_options = (*options).clone();
        no_dts_options.no_dts_resolution = TS_TRUE;
        SourceDefResolver {
            ls: self,
            fs: program.host().fs().clone(),
            options,
            program: program.clone(),
            resolve_from,
            resolver: DefaultResolver::new(ResolverOptions {
                host: Arc::new(SourceDefResolutionHost {
                    fs: program.host().fs().clone(),
                    current_directory: program.base_directory(),
                }),
                compiler_options: Arc::new(no_dts_options),
                typings_location: program.get_global_typings_cache_location(),
                project_name: String::new(),
                extra_extensions: program
                    .command_line()
                    .content_mapper_extensions()
                    .to_vec(),
                package_json_cache: None,
            }),
            parsed_files: RefCell::new(HashMap::new()),
            parsed_by_index: RefCell::new(HashMap::new()),
        }
    }
}

/// `getSourceDefCheckerInfo` — acquires the type checker for `file` and
/// returns the definition declarations for `node` along with the module
/// specifier of the import that brought the symbol into scope (empty if not
/// applicable).
fn get_source_def_checker_info(
    ctx: &Context,
    program: &Rc<Program>,
    file: NodeId,
    node: NodeId,
) -> (Vec<NodeId>, String) {
    let (c, done) = program.get_type_checker_for_file(ctx.clone(), file);
    let result = get_source_def_checker_info_worker(program, &c, file, node);
    drop(c);
    done();
    result
}

fn get_source_def_checker_info_worker(
    program: &Rc<Program>,
    c: &Rc<RefCell<Checker>>,
    file: NodeId,
    node: NodeId,
) -> (Vec<NodeId>, String) {
    let mut declarations = get_declarations_from_location(program, c, node);
    let nodes = program.nodes(file.file_index());
    let is_property_name = nodes[node]
        .parent
        .is_some_and(|p| ast::is_access_expression(&nodes[p]) && nodes[p].name() == Some(node));
    if declarations.is_empty() && is_property_name {
        if let Some(left) = nodes[node].parent.and_then(|p| nodes[p].expression()) {
            let text = nodes[node].text(&nodes).into_owned();
            drop(nodes);
            let t = c.borrow_mut().get_type_at_location(left);
            if let Some(prop) = c.borrow_mut().get_property_of_type(t, &text) {
                declarations = c.borrow().symbol_arena.borrow()[prop.index()]
                    .declarations
                    .clone();
            }
        }
    }
    if let Some(called_declaration) = try_get_signature_declaration(c, node, program) {
        let non_function_declarations: Vec<NodeId> = declarations
            .iter()
            .copied()
            .filter(|&d| {
                !ast::is_function_like(Some(d), &program.arena_of(d))
            })
            .collect();
        declarations = non_function_declarations;
        declarations.push(called_declaration);
    }

    // Extract module specifier from the import that brought this symbol into
    // scope. For property access (obj.prop), walk up the access chain to the
    // root expression's symbol.
    let mut module_specifier = String::new();
    let mut resolve_node = node;
    {
        let nodes = program.nodes(file.file_index());
        if is_property_name {
            let mut expr = nodes[node].parent.and_then(|p| nodes[p].expression());
            while let Some(e) = expr {
                if !ast::is_access_expression(&nodes[e]) {
                    break;
                }
                expr = nodes[e].expression();
            }
            if expr.is_some() {
                resolve_node = expr.expect("expr");
            }
        }
    }
    if let Some(sym) = c.borrow_mut().get_symbol_at_location_api(resolve_node) {
        let decls = c.borrow().symbol_arena.borrow()[sym.index()]
            .declarations
            .clone();
        for d in decls {
            let d_nodes = program.arena_of(d);
            if !ast::is_import_specifier(&d_nodes[d])
                && !ast::is_import_clause(&d_nodes[d])
                && !ast::is_namespace_import(&d_nodes[d])
                && !ast::is_import_equals_declaration(&d_nodes[d])
            {
                continue;
            }
            if let Some(spec) =
                tsc_checker::nodebuilderimpl::try_get_module_specifier_from_declaration(d, &d_nodes)
            {
                module_specifier = d_nodes[spec].text(&d_nodes).into_owned();
                break;
            }
        }
    }

    (declarations, module_specifier)
}

/// `isDefaultImportName`.
fn is_default_import_name(node: NodeId, nodes: &[Node]) -> bool {
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    if !ast::is_import_clause(&nodes[parent]) || nodes[parent].name() != Some(node) {
        return false;
    }
    let Some(grandparent) = nodes[parent].parent else {
        return false;
    };
    ast::is_default_import(&nodes[grandparent], nodes)
}

/// `getSourceDefinitionEntryNode`.
fn get_source_definition_entry_node(source_file: NodeId, nodes: &[Node]) -> NodeId {
    if let Some(first) = nodes[source_file]
        .as_source_file()
        .statements
        .as_ref()
        .and_then(|st| st.nodes().first())
    {
        return *first;
    }
    source_file
}

/// `getSourceDefinitionEntryDeclarations`.
fn get_source_definition_entry_declarations(
    source_file: NodeId,
    nodes: &[Node],
) -> Vec<NodeId> {
    vec![get_source_definition_entry_node(source_file, nodes)]
}

/// `findContainingModuleSpecifier`.
fn find_containing_module_specifier(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let mut current = Some(node);
    while let Some(n) = current {
        if ast::is_any_import_or_re_export(&nodes[n])
            || ast::is_require_call(&nodes[n], true /*requireStringLiteralLikeArgument*/, nodes)
            || ast::is_import_call(&nodes[n], nodes)
        {
            if let Some(module_specifier) = ast::get_external_module_name(&nodes[n], nodes) {
                if ast::is_string_literal_like(&nodes[module_specifier]) {
                    return Some(module_specifier);
                }
            }
        }
        current = nodes[n].parent;
    }
    None
}

/// `findDeclarationNodesByName`.
fn find_declaration_nodes_by_name(
    source_file: NodeId,
    names: &[String],
    nodes: &[Node],
) -> Vec<NodeId> {
    let mut deduped: Vec<String> = Vec::new();
    for name in names {
        if !name.is_empty() && !deduped.contains(name) {
            deduped.push(name.clone());
        }
    }
    if deduped.is_empty() {
        return Vec::new();
    }

    let mut wanted: HashSet<&str> = HashSet::new();
    let mut want_default = false;
    for name in &deduped {
        if name == "default" {
            want_default = true;
            continue;
        }
        wanted.insert(name.as_str());
    }

    struct State {
        candidates: Vec<(NodeId, usize)>,
        min_depth: usize,
        wanted: HashSet<String>,
        want_default: bool,
    }
    let mut state = State {
        candidates: Vec::new(),
        min_depth: usize::MAX,
        wanted: wanted.iter().map(|s| s.to_string()).collect(),
        want_default,
    };

    fn visit(node: NodeId, nodes: &[Node], state: &mut State) -> bool {
        let mut matched = false;
        if let Some(name) = ast::get_name_of_declaration(Some(node), nodes) {
            let text = ast::get_text_of_property_name(name, nodes);
            if !text.is_empty() && state.wanted.contains(&text) {
                matched = true;
            }
        }
        if state.want_default && nodes[node].kind == Kind::ExportAssignment {
            matched = true;
        }
        if state.want_default
            && (ast::is_function_declaration(&nodes[node])
                || ast::is_class_declaration(&nodes[node]))
            && nodes[node]
                .modifier_flags()
                .intersects(ModifierFlags::EXPORT_DEFAULT)
        {
            matched = true;
        }
        if matched {
            let depth = get_container_depth(node, nodes);
            state.candidates.push((node, depth));
            if depth < state.min_depth {
                state.min_depth = depth;
            }
        }
        nodes[node].for_each_child(nodes, &mut |child| visit(child, nodes, state))
    }

    visit(source_file, nodes, &mut state);

    // Only keep declarations at the shallowest depth, like
    // getTopMostDeclarationNamesInFile.
    let min_depth = state.min_depth;
    let declarations: Vec<NodeId> = state
        .candidates
        .iter()
        .filter(|(_, depth)| *depth == min_depth)
        .map(|(node, _)| *node)
        .collect();
    declarations
}

/// `getContainerDepth` — counts the number of container nodes above a
/// declaration, matching the behavior of `getDepth` in
/// `getTopMostDeclarationNamesInFile`.
fn get_container_depth(node: NodeId, nodes: &[Node]) -> usize {
    let mut depth = 0;
    let mut current = Some(node);
    while let Some(n) = current {
        current = get_container_node(n, nodes);
        depth += 1;
    }
    depth
}

/// `filterPreferredSourceDeclarations`.
fn filter_preferred_source_declarations(
    resolver: &SourceDefResolver,
    original_node: Option<NodeId>,
    declarations: Vec<NodeId>,
) -> Vec<NodeId> {
    if declarations.len() <= 1 || original_node.is_none() {
        return declarations;
    }
    let preferred =
        get_property_like_source_declarations(resolver, original_node.expect("original_node"), &declarations);
    if !preferred.is_empty() {
        return preferred;
    }
    let preferred: Vec<NodeId> = declarations
        .iter()
        .copied()
        .filter(|&d| is_concrete_source_declaration(resolver, d))
        .collect();
    if !preferred.is_empty() {
        return preferred;
    }
    declarations
}

/// `getPropertyLikeSourceDeclarations`.
fn get_property_like_source_declarations(
    resolver: &SourceDefResolver,
    original_node: NodeId,
    declarations: &[NodeId],
) -> Vec<NodeId> {
    let is_access_name = resolver.with_nodes(original_node, |nodes| {
        nodes[original_node].parent.is_some_and(|p| {
            ast::is_access_expression(&nodes[p]) && nodes[p].name() == Some(original_node)
        })
    });
    if !is_access_name {
        return Vec::new();
    }
    declarations
        .iter()
        .copied()
        .filter(|&node| {
            resolver.with_nodes(node, |nodes| {
                matches!(
                    nodes[node].kind,
                    Kind::PropertyAssignment
                        | Kind::ShorthandPropertyAssignment
                        | Kind::PropertyDeclaration
                        | Kind::PropertySignature
                        | Kind::MethodDeclaration
                        | Kind::MethodSignature
                        | Kind::GetAccessor
                        | Kind::SetAccessor
                        | Kind::EnumMember
                )
            })
        })
        .collect()
}

/// `hasConcreteSourceDeclarations`.
fn has_concrete_source_declarations(
    resolver: &SourceDefResolver,
    declarations: &[NodeId],
) -> bool {
    declarations
        .iter()
        .any(|&d| is_concrete_source_declaration(resolver, d))
}

/// `isConcreteSourceDeclaration`.
fn is_concrete_source_declaration(resolver: &SourceDefResolver, node: NodeId) -> bool {
    resolver.with_nodes(node, |nodes| {
        if !ast::is_declaration(&nodes[node]) || nodes[node].kind == Kind::ExportAssignment {
            return false;
        }
        if (ast::is_binary_expression(&nodes[node]) || ast::is_call_expression(&nodes[node]))
            && ast::get_assignment_declaration_kind(node, nodes)
                != ast::JsDeclarationKind::None
        {
            return false;
        }
        !matches!(
            nodes[node].kind,
            Kind::Parameter
                | Kind::TypeParameter
                | Kind::BindingElement
                | Kind::ImportClause
                | Kind::ImportSpecifier
                | Kind::NamespaceImport
                | Kind::ExportSpecifier
                | Kind::PropertyAccessExpression
                | Kind::ElementAccessExpression
        )
    })
}

/// `findClosestDeclarationNode`.
fn find_closest_declaration_node(
    resolver: &SourceDefResolver,
    source_file: NodeId,
    pos: TextPos,
) -> NodeId {
    let node = resolver.with_nodes_mut(source_file, |nodes| {
        tsc_astnav::tokens::get_touching_property_name(nodes, source_file, pos)
    });
    if let Some(node) = node {
        let found = resolver.with_nodes(node, |nodes| {
            let mut current = Some(node);
            while let Some(n) = current {
                if ast::is_declaration(&nodes[n]) || nodes[n].kind == Kind::ExportAssignment {
                    return Some(n);
                }
                current = nodes[n].parent;
            }
            None
        });
        if let Some(found) = found {
            return found;
        }
    }
    resolver.with_nodes(source_file, |nodes| {
        get_source_definition_entry_node(source_file, nodes)
    })
}
