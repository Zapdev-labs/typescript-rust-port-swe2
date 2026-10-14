// Ported from tsc/internal/ls/file_rename.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::{self as ast, ArenaCell, Node, NodeId, SymbolId, TokenFlags};
use tsc_checker::checker_core::Checker;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_debug as debug;
use tsc_lsconv::{self as lsconv, converters::source_file_script, converters::Converters};
use tsc_lsproto::{self as lsproto};
use tsc_modulespecifiers::{self as modulespecifiers};
use tsc_scanner::scanner;
use tsc_tsoptions::{self as tsoptions};
use tsc_tspath::{self as tspath, CaseSensitivity, RootedDirectoryPath, RootedFilePath};

use crate::change;
use crate::languageservice::LanguageService;

/// `type pathUpdater func(path tspath.RootedFilePath) (tspath.RootedFilePath,
/// bool)`. Returned `None` maps to Go's `("", false)`.
struct PathUpdater {
    old_path: RootedFilePath,
    new_path: RootedFilePath,
    old_dir: RootedDirectoryPath,
    new_dir: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
}

impl PathUpdater {
    fn call(&self, path: &RootedFilePath) -> Option<RootedFilePath> {
        if self.case_sensitivity.compare_file_paths(path, &self.old_path) == 0 {
            return Some(self.new_path.clone());
        }
        if let Some(relative_path) = self
            .case_sensitivity
            .relative_file_path_from_directory(&self.old_dir, path)
        {
            return Some(self.new_dir.resolve_relative_file(&relative_path));
        }
        None
    }
}

/// `type toImport struct`.
struct ToImport {
    new_file_name: RootedFilePath,
    updated: bool,
}

/// `type movedFile struct` — only `sourceFile.FileName()` and `newFileName`
/// are ever read, so the file name snapshot replaces the `*ast.SourceFile`.
struct MovedFile {
    file_name: RootedFilePath,
    new_file_name: RootedFilePath,
}

impl<'h> LanguageService<'h> {
    /// `GetEditsForFileRename`.
    pub fn get_edits_for_file_rename(
        &self,
        ctx: &Context,
        old_uri: &lsproto::DocumentUri,
        new_uri: &lsproto::DocumentUri,
    ) -> Vec<lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile> {
        let program = self.get_program();
        // `oldURI.FileName()` already returns a rooted path; Go's extra
        // `RootedPath`/`RootedFilePathFromPath` conversions are identities.
        let old_file = old_uri.file_name();
        let new_file = new_uri.file_name();

        let old_to_new = self.create_path_updater(&old_file, &new_file);

        let mut change_tracker = change::new_tracker(
            ctx.clone(),
            &program.options(),
            self.format_options(),
            &self.converters,
        );
        self.update_tsconfig_files(
            &program,
            &mut change_tracker,
            &old_to_new,
            &old_file,
            &new_file,
        );
        self.update_imports_for_file_rename(&program, &mut change_tracker, &old_to_new);

        let mut document_changes: Vec<
            lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile,
        > = Vec::new();

        // When renaming e.g. `foo.d.css.ts` -> `bar.d.css.ts`, also rename `foo.css` -> `bar.css` if it exists.
        if old_file.is_declaration_file() && new_file.is_declaration_file() {
            let dts_ext = old_file.declaration_file_extension();
            let original_extensions =
                tspath::get_possible_original_input_extension_for_extension(dts_ext);
            for ext in &original_extensions {
                let old_original_path = old_file.change_full_extension(ext);
                if self.host.file_exists(&old_original_path) {
                    let new_dts_ext = new_file.declaration_file_extension();
                    let new_original_extensions =
                        tspath::get_possible_original_input_extension_for_extension(new_dts_ext);
                    if new_original_extensions.contains(ext) {
                        let new_original_path = new_file.change_full_extension(ext);
                        document_changes.push(
                            lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile {
                                rename_file: Some(lsproto::RenameFile {
                                    kind: lsproto::StringLiteralRename,
                                    annotation_id: None,
                                    options: None,
                                    old_uri: lsconv::file_name_to_document_uri(
                                        &old_original_path,
                                    ),
                                    new_uri: lsconv::file_name_to_document_uri(
                                        &new_original_path,
                                    ),
                                }),
                                ..Default::default()
                            },
                        );
                    }
                }
            }
        }

        let (changes, _unmappable) = change_tracker.get_changes();
        for (file_name, edits) in &changes {
            let uri = lsconv::file_name_to_document_uri(file_name);
            let mut lsp_edits = Vec::with_capacity(edits.len());
            for edit in edits {
                lsp_edits.push(lsproto::TextEditOrAnnotatedTextEditOrSnippetTextEdit {
                    text_edit: Some(edit.clone()),
                    ..Default::default()
                });
            }
            document_changes.push(
                lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile {
                    text_document_edit: Some(lsproto::TextDocumentEdit {
                        text_document: lsproto::OptionalVersionedTextDocumentIdentifier {
                            uri,
                            ..Default::default()
                        },
                        edits: Some(lsp_edits),
                    }),
                    ..Default::default()
                },
            );
        }

        document_changes
    }

    /// `createPathUpdater` — the Go closure becomes a struct holding the
    /// captured paths and case sensitivity.
    fn create_path_updater(
        &self,
        old_path: &RootedFilePath,
        new_path: &RootedFilePath,
    ) -> PathUpdater {
        PathUpdater {
            old_dir: old_path.directory(),
            new_dir: new_path.directory(),
            old_path: old_path.clone(),
            new_path: new_path.clone(),
            case_sensitivity: self.case_sensitivity(),
        }
    }

    /// `updateTsconfigFiles`.
    fn update_tsconfig_files(
        &self,
        program: &Program,
        change_tracker: &mut change::Tracker<'_, '_>,
        old_to_new: &PathUpdater,
        old_path: &RootedFilePath,
        new_path: &RootedFilePath,
    ) {
        let command_line = program.command_line().clone();
        let Some(config) = command_line.config_file.clone() else {
            return;
        };

        let config_file = config.source_file;
        if config_file == NodeId::NONE {
            return;
        }
        let config_dir = config.nodes[config_file]
            .as_source_file()
            .file_name()
            .directory();
        let Some(json_object_literal) =
            get_ts_config_object_literal_expression(config_file, &config.nodes)
        else {
            return;
        };

        // The tsconfig file owns a standalone arena (`TsConfigSourceFile.nodes`)
        // rather than a program `ArenaCell`; the tracker only needs a cell it
        // can copy-on-write while deriving text edits, so wrap a clone.
        let config_nodes = Rc::new(ArenaCell::new(config.nodes.clone()));
        let arena = config_nodes.snapshot();
        let case_sensitivity = self.case_sensitivity();
        let converters = &self.converters;

        for_each_object_property(&arena, json_object_literal, &mut |property, property_name| {
            match property_name {
                "files" | "include" | "exclude" => {
                    let found_exact_match = update_paths_property(
                        &config_nodes,
                        &arena,
                        config_file,
                        &config_dir,
                        property,
                        change_tracker,
                        old_to_new,
                        converters,
                        case_sensitivity,
                    );
                    let initializer = arena[property].as_property_assignment().initializer;
                    let is_array_literal = initializer
                        .is_some_and(|init| ast::is_array_literal_expression(&arena[init]));
                    if found_exact_match || property_name != "include" || !is_array_literal {
                        return;
                    }
                    let (old_spec, is_default) =
                        command_line.get_matched_include_spec(old_path);
                    if !old_spec.is_empty() && !is_default {
                        let (new_spec, _) = command_line.get_matched_include_spec(new_path);
                        if new_spec.is_empty() {
                            if let Some(elements) =
                                initializer.and_then(|init| arena[init].elements())
                            {
                                if !elements.is_empty() {
                                    let last = *elements.last().unwrap();
                                    let new_path_text = match case_sensitivity
                                        .relative_path_from_directory(&config_dir, new_path)
                                    {
                                        Some(relative_path) => {
                                            relative_path.as_string().to_string()
                                        }
                                        None => new_path.as_string().to_string(),
                                    };
                                    let new_node = {
                                        let mut guard = change_tracker
                                            .borrow_nodes(&config_nodes, config_file);
                                        change_tracker
                                            .node_factory(config_file)
                                            .new_string_literal(
                                                &mut guard,
                                                &new_path_text,
                                                TokenFlags::NONE,
                                            )
                                    };
                                    change_tracker.insert_node_after(
                                        &config_nodes,
                                        config_file,
                                        last,
                                        new_node,
                                    );
                                }
                            }
                        }
                    }
                }
                "compilerOptions" => {
                    let Some(compiler_options) =
                        arena[property].as_property_assignment().initializer
                    else {
                        return;
                    };
                    if !ast::is_object_literal_expression(&arena[compiler_options]) {
                        return;
                    }
                    for_each_object_property(
                        &arena,
                        compiler_options,
                        &mut |property, property_name| {
                            if let Some(option) = tsoptions::tsconfigparsing::name_map_get(
                                tsoptions::tsconfigparsing::command_line_compiler_options_map(),
                                property_name,
                            ) {
                                let element_option = option.elements();
                                if option.path_kind.is_rooted()
                                    || (option.kind
                                        == tsoptions::commandlineoption::CommandLineOptionKind::LIST
                                        && element_option
                                            .is_some_and(|e| e.path_kind.is_rooted()))
                                {
                                    update_paths_property(
                                        &config_nodes,
                                        &arena,
                                        config_file,
                                        &config_dir,
                                        property,
                                        change_tracker,
                                        old_to_new,
                                        converters,
                                        case_sensitivity,
                                    );
                                    return;
                                }
                            }

                            let Some(paths) =
                                arena[property].as_property_assignment().initializer
                            else {
                                return;
                            };
                            if property_name != "paths"
                                || !ast::is_object_literal_expression(&arena[paths])
                            {
                                return;
                            }
                            for_each_object_property(
                                &arena,
                                paths,
                                &mut |paths_property, _| {
                                    let Some(initializer) = arena[paths_property]
                                        .as_property_assignment()
                                        .initializer
                                    else {
                                        return;
                                    };
                                    if !ast::is_array_literal_expression(&arena[initializer])
                                    {
                                        return;
                                    }
                                    let elements = arena[initializer]
                                        .elements()
                                        .map(|e| e.to_vec())
                                        .unwrap_or_default();
                                    for element in elements {
                                        try_update_config_string(
                                            &config_nodes,
                                            &arena,
                                            config_file,
                                            &config_dir,
                                            element,
                                            change_tracker,
                                            old_to_new,
                                            converters,
                                            case_sensitivity,
                                        );
                                    }
                                },
                            );
                        },
                    );
                }
                _ => {}
            }
        });
    }

    /// `updateRelativePath`.
    fn update_relative_path(
        &self,
        old_to_new: &PathUpdater,
        old_import_from_path: &RootedFilePath,
        new_import_from_path: &RootedFilePath,
        relative_specifier: &tspath::ModuleSpecifier,
    ) -> tspath::ModuleSpecifier {
        let old_absolute = old_import_from_path
            .directory()
            .resolve_file(relative_specifier.as_string());
        let new_absolute = old_to_new.call(&old_absolute).unwrap_or(old_absolute);
        relative_import_path_from_directory(
            &new_import_from_path.directory(),
            &new_absolute,
            self.case_sensitivity(),
        )
    }

    /// `updateImportsForFileRename`.
    fn update_imports_for_file_rename(
        &self,
        program: &Rc<Program>,
        change_tracker: &mut change::Tracker<'_, '_>,
        old_to_new: &PathUpdater,
    ) {
        let all_files = program.source_files();
        let (checker, _done) = program.get_type_checker(Context::background());
        let module_specifier_preferences =
            self.user_preferences().module_specifier_preferences();

        let mut moved_files: Vec<MovedFile> = Vec::new();
        for &source_file in &all_files {
            let nodes = program.nodes(source_file.file_index());
            let source_file_data = nodes[source_file].as_source_file();
            let original_file_name = source_file_data.original_file_name(&nodes).clone();
            let file_name = source_file_data.file_name().clone();
            drop(nodes);
            if let Some(new_file_name) = old_to_new.call(&original_file_name) {
                moved_files.push(MovedFile {
                    file_name,
                    new_file_name,
                });
            }
        }

        for &source_file in &all_files {
            let arena = program.arena_handle(source_file.file_index());
            let nodes = arena.snapshot();
            let source_file_data = nodes[source_file].as_source_file();
            let old_file_name = source_file_data.original_file_name(&nodes).clone();
            let referenced_files = source_file_data.referenced_files.to_vec();
            let imports = source_file_data.imports().to_vec();
            drop(nodes);

            let (new_import_from_path, file_moved) = match old_to_new.call(&old_file_name) {
                Some(new_from_old) => (new_from_old, true),
                None => (old_file_name.clone(), false),
            };

            for file_reference in &referenced_files {
                if !tspath::is_external_module_name_relative(&file_reference.file_name) {
                    continue;
                }
                let updated = self.update_relative_path(
                    old_to_new,
                    &old_file_name,
                    &new_import_from_path,
                    &tspath::to_module_specifier(&file_reference.file_name),
                );
                if updated.as_string() != file_reference.file_name {
                    change_tracker.replace_text_range_with_text(
                        &arena,
                        source_file,
                        file_reference.text_range,
                        updated.as_string(),
                    );
                }
            }

            for import_string_literal in imports {
                let nodes = arena.snapshot();
                let updated = self.get_updated_import_specifier(
                    program,
                    &checker,
                    &nodes,
                    source_file,
                    import_string_literal,
                    old_to_new,
                    &moved_files,
                    &new_import_from_path,
                    file_moved,
                    &module_specifier_preferences,
                );
                if !updated.is_empty()
                    && updated != nodes[import_string_literal].text(&nodes).as_ref()
                {
                    let text_range =
                        create_string_text_range(&nodes, source_file, import_string_literal);
                    drop(nodes);
                    change_tracker.replace_text_range_with_text(
                        &arena,
                        source_file,
                        text_range,
                        &updated,
                    );
                }
            }
        }
    }

    /// `getUpdatedImportSpecifier` — we assume the source file did not move
    /// to a different program.
    #[allow(clippy::too_many_arguments)]
    fn get_updated_import_specifier(
        &self,
        program: &Rc<Program>,
        checker: &Rc<RefCell<Checker>>,
        nodes: &[Node],
        source_file: NodeId,
        import_literal: NodeId,
        old_to_new: &PathUpdater,
        moved_files: &[MovedFile],
        new_import_from_path: &RootedFilePath,
        importing_source_file_moved: bool,
        user_preferences: &modulespecifiers::UserPreferences,
    ) -> String {
        let imported_module_symbol = checker
            .borrow_mut()
            .get_symbol_at_location_api(import_literal);
        if is_ambient_module_symbol(program, imported_module_symbol) {
            return String::new();
        }

        let target = get_source_file_to_import(program, source_file, import_literal, old_to_new);
        let literal_text = nodes[import_literal].text(nodes).into_owned();

        let Some(target) = target else {
            // First fall back: try every file affected by the rename to see if any of them would match the import specifier, and if so, obtain the updated specifier for that file.
            let updated = get_updated_import_specifier_from_moved_source_files(
                program,
                nodes,
                source_file,
                import_literal,
                moved_files,
                new_import_from_path,
                user_preferences,
            );
            if !updated.is_empty() && updated != literal_text {
                return updated;
            }
            // Fall back to a regular path update for unresolved module.
            if tspath::is_external_module_name_relative(&literal_text) {
                return self
                    .update_relative_path(
                        old_to_new,
                        nodes[source_file].as_source_file().file_name(),
                        new_import_from_path,
                        &tspath::to_module_specifier(&literal_text),
                    )
                    .as_string()
                    .to_string();
            }
            return String::new();
        };

        // Optimization: neither the importing or imported file changed.
        if !target.updated
            && !(importing_source_file_moved
                && tspath::is_external_module_name_relative(&literal_text))
        {
            return String::new();
        }

        let updated = modulespecifiers::update_module_specifier(
            &program.options(),
            program.as_ref(),
            nodes[source_file].as_source_file(),
            new_import_from_path,
            &tspath::to_module_specifier(&literal_text),
            &target.new_file_name,
            user_preferences,
            &modulespecifiers::ModuleSpecifierOptions {
                override_import_mode: program.get_mode_for_usage_location(
                    &program.file_has_file_name(source_file),
                    import_literal,
                ),
            },
            nodes,
            &|_| None,
        );
        updated.as_string().to_string()
    }
}

/// `getSourceFileToImport`.
fn get_source_file_to_import(
    program: &Program,
    source_file: NodeId,
    import_literal: NodeId,
    old_to_new: &PathUpdater,
) -> Option<ToImport> {
    if let Some(resolved) =
        program.get_resolved_module_from_module_specifier(source_file, import_literal)
    {
        if resolved.is_resolved() {
            let old_file_name = resolved.resolved_file_name;
            if let Some(new_file_name) = old_to_new.call(&old_file_name) {
                return Some(ToImport {
                    new_file_name,
                    updated: true,
                });
            }
            return Some(ToImport {
                new_file_name: old_file_name,
                updated: false,
            });
        }
    }
    None
}

/// `getUpdatedImportSpecifierFromMovedSourceFiles` — as a fall back for
/// unresolved modules, check every file affected by the rename to see if any
/// of them would match the import specifier, and if so, obtain the updated
/// specifier for that file.
fn get_updated_import_specifier_from_moved_source_files(
    program: &Rc<Program>,
    nodes: &[Node],
    source_file: NodeId,
    import_literal: NodeId,
    moved_files: &[MovedFile],
    importing_source_file_name: &RootedFilePath,
    user_preferences: &modulespecifiers::UserPreferences,
) -> String {
    let resolution_mode = program.get_mode_for_usage_location(
        &program.file_has_file_name(source_file),
        import_literal,
    );
    for candidate in moved_files {
        let old_specifier = modulespecifiers::update_module_specifier(
            &program.options(),
            program.as_ref(),
            nodes[source_file].as_source_file(),
            importing_source_file_name,
            &tspath::to_module_specifier(nodes[import_literal].text(nodes).as_ref()),
            &candidate.file_name,
            user_preferences,
            &modulespecifiers::ModuleSpecifierOptions {
                override_import_mode: resolution_mode,
            },
            nodes,
            &|_| None,
        );
        if old_specifier.as_string() != nodes[import_literal].text(nodes).as_ref() {
            continue;
        }

        return modulespecifiers::update_module_specifier(
            &program.options(),
            program.as_ref(),
            nodes[source_file].as_source_file(),
            importing_source_file_name,
            &tspath::to_module_specifier(nodes[import_literal].text(nodes).as_ref()),
            &candidate.new_file_name,
            user_preferences,
            &modulespecifiers::ModuleSpecifierOptions {
                override_import_mode: resolution_mode,
            },
            nodes,
            &|_| None,
        )
        .as_string()
        .to_string();
    }
    String::new()
}

/// `createStringTextRange`.
fn create_string_text_range(nodes: &[Node], source_file: NodeId, node: NodeId) -> TextRange {
    TextRange::new(
        scanner::get_token_pos_of_node(
            node,
            nodes[source_file].as_source_file(),
            false, /*includeJSDoc*/
            nodes,
        ) + 1,
        nodes[node].end() - 1,
    )
}

/// `getTsConfigObjectLiteralExpression`.
fn get_ts_config_object_literal_expression(
    ts_config_source_file: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    let statements = nodes[ts_config_source_file]
        .as_source_file()
        .statements
        .as_ref()?;
    let first = *statements.nodes.first()?;
    let expression = nodes[first].expression()?;
    if ast::is_object_literal_expression(&nodes[expression]) {
        return Some(expression);
    }
    None
}

/// `forEachObjectProperty` — `cb` receives each `(property, propertyName)`
/// pair for `PropertyAssignment` members whose name has text.
fn for_each_object_property(
    nodes: &[Node],
    object_literal: NodeId,
    cb: &mut impl FnMut(NodeId, &str),
) {
    let Some(properties) = nodes[object_literal]
        .as_object_literal_expression()
        .properties
        .as_ref()
    else {
        return;
    };
    for &property in properties.nodes.iter() {
        if !ast::is_property_assignment(&nodes[property]) {
            continue;
        }
        if let Some(name) = nodes[property].name() {
            if let (Some(text), true) = ast::try_get_text_of_property_name(name, nodes) {
                cb(property, &text);
            }
        }
    }
}

/// `relativePathFromDirectory`.
fn relative_path_from_directory(
    from_directory: &RootedDirectoryPath,
    to: &RootedFilePath,
    case_sensitivity: CaseSensitivity,
) -> tspath::FileSpec {
    if let Some(relative_path) =
        case_sensitivity.relative_path_from_directory(from_directory, to)
    {
        return tspath::to_file_spec(relative_path.as_string());
    }
    tspath::to_file_spec(to.as_string())
}

/// `relativeImportPathFromDirectory`.
fn relative_import_path_from_directory(
    from_directory: &RootedDirectoryPath,
    to: &RootedFilePath,
    case_sensitivity: CaseSensitivity,
) -> tspath::ModuleSpecifier {
    if let Some(relative_path) =
        case_sensitivity.relative_path_from_directory(from_directory, to)
    {
        return relative_path.as_module_specifier();
    }
    to.as_module_specifier()
}

/// `updatePathsProperty` — returns whether any element produced an exact path
/// match (`foundExactMatch`).
#[allow(clippy::too_many_arguments)]
fn update_paths_property(
    config_nodes: &Rc<ArenaCell>,
    arena: &[Node],
    config_file: NodeId,
    config_dir: &RootedDirectoryPath,
    property: NodeId,
    change_tracker: &mut change::Tracker<'_, '_>,
    old_to_new: &PathUpdater,
    converters: &Converters<'_>,
    case_sensitivity: CaseSensitivity,
) -> bool {
    let initializer = arena[property].as_property_assignment().initializer;
    let elements: Vec<NodeId> = match initializer {
        Some(init) if ast::is_array_literal_expression(&arena[init]) => {
            arena[init].elements().map(|e| e.to_vec()).unwrap_or_default()
        }
        Some(init) => vec![init],
        None => Vec::new(),
    };

    let mut found_exact_match = false;
    for element in elements {
        found_exact_match = try_update_config_string(
            config_nodes,
            arena,
            config_file,
            config_dir,
            element,
            change_tracker,
            old_to_new,
            converters,
            case_sensitivity,
        ) || found_exact_match;
    }
    found_exact_match
}

/// `tryUpdateConfigString`.
#[allow(clippy::too_many_arguments)]
fn try_update_config_string(
    config_nodes: &Rc<ArenaCell>,
    arena: &[Node],
    config_file: NodeId,
    config_dir: &RootedDirectoryPath,
    element: NodeId,
    change_tracker: &mut change::Tracker<'_, '_>,
    old_to_new: &PathUpdater,
    converters: &Converters<'_>,
    case_sensitivity: CaseSensitivity,
) -> bool {
    if !ast::is_string_literal(&arena[element]) {
        return false;
    }

    let element_file_name = config_dir.resolve_file(arena[element].text(arena).as_ref());
    let Some(updated) = old_to_new.call(&element_file_name) else {
        return false;
    };

    let text_range = TextRange::new(
        scanner::get_token_pos_of_node(
            element,
            arena[config_file].as_source_file(),
            false, /*includeJSDoc*/
            arena,
        ) + 1,
        arena[element].end() - 1,
    );
    let (lsp_range, fidelity) =
        converters.to_lsp_range(&source_file_script(config_file, arena), text_range);
    debug::assert_!(fidelity.is_exact(), "config files are not content-mapped");
    change_tracker.replace_range_with_text(
        config_nodes,
        config_file,
        lsp_range,
        relative_path_from_directory(config_dir, &updated, case_sensitivity).as_string(),
    );
    true
}

/// `isAmbientModuleSymbol`.
fn is_ambient_module_symbol(program: &Program, symbol: Option<SymbolId>) -> bool {
    let Some(symbol) = symbol else {
        return false;
    };
    let declarations = {
        let symbols = program.symbols.clone();
        symbols[symbol.index()].declarations.clone()
    };
    declarations.iter().any(|&decl| {
        let nodes = program.nodes(decl.file_index());
        ast::is_module_with_string_literal_name(&nodes[decl], &nodes)
    })
}
