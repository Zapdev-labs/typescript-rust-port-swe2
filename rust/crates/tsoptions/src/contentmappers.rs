// Ported from tsc/internal/tsoptions/contentmappers.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_ast::diagnostic::{DiagnosticRef, new_compiler_diagnostic};
use tsc_contentmapper::Manifest;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::options_generated::ModuleResolutionKind;
use tsc_diagnostics::{self as diagnostics};
use tsc_module::{self as module, ResolutionHost};
use tsc_packagejson as packagejson;
use tsc_tspath::{self as tspath, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

use crate::value::Value;

/// `contentMapperResolutionHost`.
pub(crate) struct ContentMapperResolutionHost {
    fs: Arc<dyn Vfs>,
    current_directory: RootedDirectoryPath,
}

impl ResolutionHost for ContentMapperResolutionHost {
    /// `(h) FS`.
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }

    /// `(h) GetCurrentDirectory`.
    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.current_directory.clone()
    }
}

/// `resolveContentMapperManifest` — locates `package_name` in node_modules
/// (walking up from the directory of `containing_file` via node module
/// resolution) and reads its package.json to produce the mapper's manifest
/// and package directory. It never executes the package. On failure it
/// returns a diagnostic describing why the mapper could not be resolved.
pub(crate) fn resolve_content_mapper_manifest(
    fs: &Arc<dyn Vfs>,
    containing_file: &RootedFilePath,
    package_name: &str,
) -> (Option<Manifest>, RootedDirectoryPath, Option<DiagnosticRef>) {
    let resolver = module::DefaultResolver::new(module::ResolverOptions {
        host: Arc::new(ContentMapperResolutionHost {
            fs: fs.clone(),
            current_directory: containing_file.directory(),
        }),
        compiler_options: Arc::new(CompilerOptions {
            module_resolution: ModuleResolutionKind::Bundler,
            ..CompilerOptions::default()
        }),
        typings_location: RootedDirectoryPath::default(),
        project_name: String::new(),
        extra_extensions: Vec::new(),
        package_json_cache: None,
    });
    let resolved = resolver.resolve_package_directory(
        package_name,
        containing_file,
        tsc_core::compileroptions::RESOLUTION_MODE_NONE,
        None,
    );
    let Some(resolved) = resolved else {
        return (
            None,
            RootedDirectoryPath::default(),
            Some(new_compiler_diagnostic(
                &diagnostics::The_content_mapper_package_0_could_not_be_resolved,
                &[Value::Str(package_name.into())],
            )),
        );
    };
    if resolved.resolved_file_name.as_string().is_empty() {
        return (
            None,
            RootedDirectoryPath::default(),
            Some(new_compiler_diagnostic(
                &diagnostics::The_content_mapper_package_0_could_not_be_resolved,
                &[Value::Str(package_name.into())],
            )),
        );
    }
    let package_directory =
        tspath::rooted_directory_path_from_path(resolved.resolved_file_name.as_path());

    let package_json_path = package_directory.resolve_file("package.json");
    let Some(contents) = fs.read_file(&package_json_path) else {
        return (
            None,
            package_directory,
            Some(new_compiler_diagnostic(
                &diagnostics::The_content_mapper_package_0_could_not_be_resolved,
                &[Value::Str(package_name.into())],
            )),
        );
    };
    let fields = packagejson::parse(contents.as_bytes());
    let Ok(fields) = fields else {
        return (
            None,
            package_directory,
            Some(new_compiler_diagnostic(
                &diagnostics::The_package_json_of_the_content_mapper_package_0_could_not_be_parsed,
                &[Value::Str(package_name.into())],
            )),
        );
    };
    let name = fields.name.get_value().cloned().unwrap_or_default();
    if name.is_empty() {
        return (
            None,
            package_directory,
            Some(new_compiler_diagnostic(
                &diagnostics::The_package_json_of_the_content_mapper_package_0_does_not_specify_a_name,
                &[Value::Str(package_name.into())],
            )),
        );
    }
    let version = fields.version.get_value().cloned().unwrap_or_default();

    // A content mapper package must declare how to run it: a
    // "typescript.contentMapper" object with a non-empty "exec" array of
    // strings.
    let Some(cm) = fields.content_mapper.get_value() else {
        return (
            None,
            package_directory,
            Some(new_compiler_diagnostic(
                &diagnostics::The_package_json_of_the_content_mapper_package_0_does_not_declare_a_typescript_contentMapper_object,
                &[Value::Str(package_name.into())],
            )),
        );
    };
    let exec = cm.exec.get_value().cloned();
    if exec.as_ref().is_none_or(|e| e.is_empty()) {
        return (
            None,
            package_directory,
            Some(new_compiler_diagnostic(
                &diagnostics::The_typescript_contentMapper_exec_of_the_content_mapper_package_0_must_be_a_non_empty_array_of_strings,
                &[Value::Str(package_name.into())],
            )),
        );
    }
    let compiler_options = cm.compiler_options.get_value().cloned();
    let dynamic_config = cm.dynamic_config.get_value().copied().unwrap_or_default();
    (
        Some(Manifest {
            name,
            version,
            exec,
            compiler_options,
            dynamic_config,
        }),
        package_directory,
        None,
    )
}
