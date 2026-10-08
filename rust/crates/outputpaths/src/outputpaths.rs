// Ported from tsc/internal/outputpaths/outputpaths.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::Node;
use tsc_ast::ast_generated::SourceFile;
use tsc_ast::ids::NodeId;
use tsc_ast::utilities::is_json_source_file;
use tsc_core::options_generated::{CompilerOptions, JsxEmit};
use tsc_core::tristate::TS_TRUE;
use tsc_tspath::{self as tspath, CaseSensitivity, RootedDirectoryPath, RootedFilePath};

/// `type OutputPathsHost interface`.
///
// PORT: Go returns `[]string` from ContentMapperExtensions; the trait returns
// a borrowed slice instead of a copy.
pub trait OutputPathsHost {
    /// `CommonSourceDirectory()`.
    fn common_source_directory(&self) -> RootedDirectoryPath;
    /// `ContentMapperExtensions()`.
    fn content_mapper_extensions(&self) -> &[String];
    /// `CaseSensitivity()`.
    fn case_sensitivity(&self) -> CaseSensitivity;
}

/// `type OutputPaths struct`.
///
// PORT: Go's fields are unexported and the accessors return RootedFilePath by
// value; the accessors here return `&RootedFilePath` to avoid cloning the
// underlying String.
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct OutputPaths {
    js_file_path: RootedFilePath,
    source_map_file_path: RootedFilePath,
    declaration_file_path: RootedFilePath,
    declaration_map_path: RootedFilePath,
}

impl OutputPaths {
    /// `DeclarationFilePath` — implements declarations.OutputPaths.
    pub fn declaration_file_path(&self) -> &RootedFilePath {
        &self.declaration_file_path
    }

    /// `JsFilePath` — implements declarations.OutputPaths.
    pub fn js_file_path(&self) -> &RootedFilePath {
        &self.js_file_path
    }

    /// `SourceMapFilePath`.
    pub fn source_map_file_path(&self) -> &RootedFilePath {
        &self.source_map_file_path
    }

    /// `DeclarationMapPath`.
    pub fn declaration_map_path(&self) -> &RootedFilePath {
        &self.declaration_map_path
    }
}

/// `type ForceEmitPaths struct`.
#[derive(Clone, Copy, Default)]
pub struct ForceEmitPaths {
    pub dts: bool,
    pub js: bool,
    pub declaration_map: bool,
}

/// `GetOutputPathsFor`.
///
// PORT: `*ast.SourceFile` parameters become `NodeId` (the node's arena id),
// resolved through `nodes` appended to the Go parameter list. Go returns
// `*OutputPaths`; the value is always allocated, so this returns `OutputPaths`.
pub fn get_output_paths_for(
    source_file: NodeId,
    options: &CompilerOptions,
    host: &impl OutputPathsHost,
    force: ForceEmitPaths,
    nodes: &[Node],
) -> OutputPaths {
    let file = nodes[source_file].as_source_file();
    // `FileName()` reads `parseOptions.FileName`, as in Go.
    let file_name = file.file_name().clone();
    let own_output_file_path = get_own_emit_output_file_path_for_file_name(
        &file_name,
        options,
        host,
        get_output_extension_for_file_name(&file_name, options.jsx),
    );
    let is_json_file = is_json_source_file(file);
    // If json file emits to the same location skip writing it, if emitDeclarationOnly skip writing it
    let is_json_emitted_to_same_location = is_json_file
        && host
            .case_sensitivity()
            .compare_file_paths(&file_name, &own_output_file_path)
            == 0;
    let mut paths = OutputPaths::default();
    if content_mapper(file).is_empty()
        && (force.js || options.emit_declaration_only != TS_TRUE)
        && !is_json_emitted_to_same_location
    {
        paths.js_file_path = own_output_file_path;
        if !is_json_source_file(file) {
            paths.source_map_file_path = get_source_map_file_path(&paths.js_file_path, options);
        }
    }
    if force.dts || options.get_emit_declarations() && !is_json_file {
        paths.declaration_file_path =
            get_declaration_emit_output_file_path_for_file_name(&file_name, options, host);
        if options.get_are_declaration_maps_enabled()
            || force.declaration_map && options.declaration_map.is_true()
        {
            paths.declaration_map_path = paths.declaration_file_path.append_suffix(".map");
        }
    }
    paths
}

// PORT(deferred): `SourceFile.ContentMapper()` — the Rust SourceFile does not
// yet carry `content_mapper_info` (contentmapper is deferred; see
// ast/diagnostic.rs), so every file is treated as unmapped and this returns "".
fn content_mapper(_file: &SourceFile) -> &'static str {
    ""
}

/// `ForEachEmittedFile`.
///
// PORT: `sourceFiles []*ast.SourceFile` is `&[NodeId]` resolved through
// `nodes`; the action's `*ast.SourceFile` is likewise `NodeId`.
pub fn for_each_emitted_file(
    host: &impl OutputPathsHost,
    options: &CompilerOptions,
    mut action: impl FnMut(&OutputPaths, NodeId) -> bool,
    source_files: &[NodeId],
    force_dts_emit: bool,
    nodes: &[Node],
) -> bool {
    for &source_file in source_files {
        let paths = get_output_paths_for(
            source_file,
            options,
            host,
            ForceEmitPaths {
                dts: force_dts_emit,
                ..Default::default()
            },
            nodes,
        );
        if action(&paths, source_file) {
            return true;
        }
    }
    false
}

/// `GetOutputJSFileName`.
///
// PORT: Go's `return ""` is `RootedFilePath::default()` (the empty sentinel).
pub fn get_output_js_file_name(
    input_file_name: &RootedFilePath,
    options: &CompilerOptions,
    host: &impl OutputPathsHost,
) -> RootedFilePath {
    if options.emit_declaration_only.is_true() || is_content_mapped_file_name(input_file_name, host)
    {
        return RootedFilePath::default();
    }
    let output_file_name = get_output_js_file_name_worker(input_file_name, options, host);
    if !output_file_name.extension_is(tspath::EXTENSION_JSON)
        || host
            .case_sensitivity()
            .compare_file_paths(input_file_name, &output_file_name)
            != 0
    {
        return output_file_name;
    }

    RootedFilePath::default()
}

/// `isContentMappedFileName`.
fn is_content_mapped_file_name(file_name: &RootedFilePath, host: &impl OutputPathsHost) -> bool {
    !file_name
        .longest_extension(&content_mapper_extensions(host), host.case_sensitivity())
        .is_empty()
}

// PORT: `host.ContentMapperExtensions()` is `&[String]`; `LongestExtension`
// takes `&[&str]`, so collect the borrowed slice.
fn content_mapper_extensions<'a>(host: &'a impl OutputPathsHost) -> Vec<&'a str> {
    host.content_mapper_extensions()
        .iter()
        .map(String::as_str)
        .collect()
}

/// `GetOutputJSFileNameWorker`.
pub fn get_output_js_file_name_worker(
    input_file_name: &RootedFilePath,
    options: &CompilerOptions,
    host: &impl OutputPathsHost,
) -> RootedFilePath {
    get_output_file_name_without_changing_extension(input_file_name, &options.out_dir, host)
        .change_extension(get_output_extension_for_file_name(
            input_file_name,
            options.jsx,
        ))
}

/// `GetOutputDeclarationFileNameWorker`.
pub fn get_output_declaration_file_name_worker(
    input_file_name: &RootedFilePath,
    options: &CompilerOptions,
    host: &impl OutputPathsHost,
) -> RootedFilePath {
    let mut dir = &options.declaration_dir;
    if dir.is_empty() {
        dir = &options.out_dir;
    }
    let path = get_output_file_name_without_changing_extension(input_file_name, dir, host);
    change_to_declaration_extension(&path, host)
}

/// `GetOutputExtension`.
///
// PORT: the returned string is always one of the tspath::EXTENSION_* constants,
// so the result is `&'static str`.
pub fn get_output_extension(file_name: &str, jsx: JsxEmit) -> &'static str {
    if tspath::file_extension_is(file_name, tspath::EXTENSION_JSON) {
        return tspath::EXTENSION_JSON;
    }
    if jsx == JsxEmit::Preserve
        && tspath::file_extension_is_one_of(
            file_name,
            &[tspath::EXTENSION_JSX, tspath::EXTENSION_TSX],
        )
    {
        return tspath::EXTENSION_JSX;
    }
    if tspath::file_extension_is_one_of(file_name, &[tspath::EXTENSION_MTS, tspath::EXTENSION_MJS])
    {
        return tspath::EXTENSION_MJS;
    }
    if tspath::file_extension_is_one_of(file_name, &[tspath::EXTENSION_CTS, tspath::EXTENSION_CJS])
    {
        return tspath::EXTENSION_CJS;
    }
    tspath::EXTENSION_JS
}

/// `GetOutputExtensionForFileName`.
pub fn get_output_extension_for_file_name(
    file_name: &RootedFilePath,
    jsx: JsxEmit,
) -> &'static str {
    get_output_extension(file_name.as_string(), jsx)
}

/// `getDeclarationEmitOutputFilePathForFileName`.
fn get_declaration_emit_output_file_path_for_file_name(
    file: &RootedFilePath,
    options: &CompilerOptions,
    host: &impl OutputPathsHost,
) -> RootedFilePath {
    let mut output_dir = RootedDirectoryPath::default();
    if !options.declaration_dir.is_empty() {
        output_dir = options.declaration_dir.clone();
    } else if !options.out_dir.is_empty() {
        output_dir = options.out_dir.clone();
    }

    if !output_dir.is_empty() {
        return change_to_declaration_extension(
            &get_source_file_name_in_new_dir(
                file,
                &output_dir,
                &host.common_source_directory(),
                host.case_sensitivity(),
            ),
            host,
        );
    }
    change_to_declaration_extension(file, host)
}

/// `ChangeToDeclarationExtension`.
///
// PORT: Go passes `tspath.CaseSensitive` (not the host's sensitivity) to
// LongestExtension and AnyExtension; `nil` extensions is `&[]`.
pub fn change_to_declaration_extension(
    path: &RootedFilePath,
    host: &impl OutputPathsHost,
) -> RootedFilePath {
    let extension = path.longest_extension(
        &content_mapper_extensions(host),
        CaseSensitivity::CaseSensitive,
    );
    if !extension.is_empty() {
        return path
            .remove_extension(extension)
            .append_suffix(&format!(".d{extension}.ts"));
    }
    let mut path_without_extension = path.remove_file_extension();
    if path_without_extension.as_string() == path.as_string() {
        let extension = path.any_extension(&[], CaseSensitivity::CaseSensitive);
        if !extension.is_empty() {
            path_without_extension = path.remove_extension(&extension);
        }
    }
    path_without_extension.append_suffix(&path.declaration_emit_extension())
}

/// `getOutputFileNameWithoutChangingExtension`.
fn get_output_file_name_without_changing_extension(
    input_file_name: &RootedFilePath,
    output_directory: &RootedDirectoryPath,
    host: &impl OutputPathsHost,
) -> RootedFilePath {
    if !output_directory.is_empty() {
        let relative_path = host
            .case_sensitivity()
            .relative_path_from_directory(&host.common_source_directory(), input_file_name);
        let Some(relative_path) = relative_path else {
            return input_file_name.clone();
        };

        return output_directory.resolve_relative_file(&relative_path);
    }
    input_file_name.clone()
}

/// `GetSourceFileNameInNewDir`.
pub fn get_source_file_name_in_new_dir(
    file_name: &RootedFilePath,
    new_dir_path: &RootedDirectoryPath,
    common_source_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> RootedFilePath {
    if file_name.as_path() == common_source_directory.as_path() {
        return file_name.clone();
    }
    if let Some(relative_path) =
        case_sensitivity.relative_file_path_from_directory(common_source_directory, file_name)
    {
        return new_dir_path.resolve_relative_file(&relative_path);
    }
    file_name.clone()
}

/// `getOwnEmitOutputFilePathForFileName`.
fn get_own_emit_output_file_path_for_file_name(
    file_name: &RootedFilePath,
    options: &CompilerOptions,
    host: &impl OutputPathsHost,
    extension: &str,
) -> RootedFilePath {
    let emit_output_file_path = if !options.out_dir.is_empty() {
        get_source_file_name_in_new_dir(
            file_name,
            &options.out_dir,
            &host.common_source_directory(),
            host.case_sensitivity(),
        )
    } else {
        file_name.clone()
    };
    emit_output_file_path
        .remove_file_extension()
        .append_suffix(extension)
}

/// `GetSourceMapFilePath`.
///
// PORT: Go's `return ""` is `RootedFilePath::default()` (the empty sentinel).
pub fn get_source_map_file_path(
    js_file_path: &RootedFilePath,
    options: &CompilerOptions,
) -> RootedFilePath {
    if options.source_map.is_true() && !options.inline_source_map.is_true() {
        return js_file_path.append_suffix(".map");
    }
    RootedFilePath::default()
}

/// `GetBuildInfoFileName`.
///
// PORT: Go's `return ""` is `RootedFilePath::default()` (the empty sentinel).
pub fn get_build_info_file_name(
    options: &CompilerOptions,
    case_sensitivity: CaseSensitivity,
) -> RootedFilePath {
    if !options.is_incremental() && !options.build.is_true() {
        return RootedFilePath::default();
    }
    if !options.ts_build_info_file.is_empty() {
        return options.ts_build_info_file.clone();
    }
    if options.config_file_path.is_empty() {
        return RootedFilePath::default();
    }
    let config_file_name = &options.config_file_path;
    let build_info_file_name;
    if !options.out_dir.is_empty() {
        if !options.root_dir.is_empty() {
            match case_sensitivity.relative_path_from_directory(&options.root_dir, config_file_name)
            {
                Some(relative_path) => {
                    build_info_file_name = options.out_dir.resolve_relative_file(&relative_path);
                }
                None => {
                    build_info_file_name = config_file_name.clone();
                }
            }
        } else {
            build_info_file_name = options.out_dir.resolve_file(config_file_name.base_name());
        }
    } else {
        build_info_file_name = config_file_name.clone();
    }
    build_info_file_name
        .remove_file_extension()
        .append_suffix(tspath::EXTENSION_TS_BUILD_INFO)
}
