// Ported from tsc/internal/core/compileroptions.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::LazyLock;
use tsc_tspath as tspath;

use crate::options_generated::{
    CompilerOptions, JsxEmit, ModuleDetectionKind, ModuleKind, ModuleResolutionKind, NewLineKind,
    ScriptTarget,
};
use crate::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN, Tristate};

// PORT: Go's `noCopy` marker struct is unneeded: Rust never copies structs
// implicitly.

// PORT: Go's `var EmptyCompilerOptions = &CompilerOptions{}` is a shared
// pointer; use `&EMPTY_COMPILER_OPTIONS` (a LazyLock).
pub static EMPTY_COMPILER_OPTIONS: LazyLock<CompilerOptions> =
    LazyLock::new(CompilerOptions::default);

impl CompilerOptions {
    pub fn get_emit_script_target(&self) -> ScriptTarget {
        if self.target != ScriptTarget::None {
            return self.target;
        }
        ScriptTarget::LATEST_STANDARD
    }

    pub fn get_emit_module_kind(&self) -> ModuleKind {
        if self.module != ModuleKind::None {
            return self.module;
        }

        let target = self.get_emit_script_target();
        if target == ScriptTarget::ESNext {
            return ModuleKind::ESNext;
        }
        if target >= ScriptTarget::ES2022 {
            return ModuleKind::ES2022;
        }
        if target >= ScriptTarget::ES2020 {
            return ModuleKind::ES2020;
        }
        if target >= ScriptTarget::ES2015 {
            return ModuleKind::ES2015;
        }
        ModuleKind::CommonJS
    }

    pub fn get_module_resolution_kind(&self) -> ModuleResolutionKind {
        match self.module_resolution {
            ModuleResolutionKind::Unknown
            | ModuleResolutionKind::Classic
            | ModuleResolutionKind::Node10 => match self.get_emit_module_kind() {
                ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 => {
                    ModuleResolutionKind::Node16
                }
                ModuleKind::NodeNext => ModuleResolutionKind::NodeNext,
                _ => ModuleResolutionKind::Bundler,
            },
            _ => self.module_resolution,
        }
    }

    pub fn get_emit_module_detection_kind(&self) -> ModuleDetectionKind {
        if self.module_detection != ModuleDetectionKind::None {
            return self.module_detection;
        }
        let module_kind = self.get_emit_module_kind();
        if ModuleKind::Node16 <= module_kind && module_kind <= ModuleKind::NodeNext {
            return ModuleDetectionKind::Force;
        }
        ModuleDetectionKind::Auto
    }

    pub fn get_resolve_package_json_exports(&self) -> bool {
        self.resolve_package_json_exports.is_true_or_unknown()
    }

    pub fn get_resolve_package_json_imports(&self) -> bool {
        self.resolve_package_json_imports.is_true_or_unknown()
    }

    pub fn get_allow_importing_ts_extensions(&self) -> bool {
        self.allow_importing_ts_extensions.is_true()
            || self.rewrite_relative_import_extensions.is_true()
    }

    pub fn allow_importing_ts_extensions_from(&self, file_name: &tspath::RootedFilePath) -> bool {
        self.get_allow_importing_ts_extensions() || file_name.is_declaration_file()
    }

    pub fn get_resolve_json_module(&self) -> bool {
        if self.resolve_json_module != TS_UNKNOWN {
            return self.resolve_json_module == TS_TRUE;
        }
        match self.get_emit_module_kind() {
            // TODO in 6.0: add Node16/Node18
            ModuleKind::Node20 | ModuleKind::NodeNext => return true,
            _ => {}
        }
        self.get_module_resolution_kind() == ModuleResolutionKind::Bundler
    }

    pub fn should_preserve_const_enums(&self) -> bool {
        self.preserve_const_enums == TS_TRUE || self.get_isolated_modules()
    }

    pub fn get_allow_js(&self) -> bool {
        if self.allow_js != TS_UNKNOWN {
            return self.allow_js == TS_TRUE;
        }
        self.check_js == TS_TRUE
    }

    pub fn get_jsx_transform_enabled(&self) -> bool {
        let jsx = self.jsx;
        jsx == JsxEmit::React || jsx == JsxEmit::ReactJSX || jsx == JsxEmit::ReactJSXDev
    }

    pub fn get_strict_option_value(&self, value: Tristate) -> bool {
        if value != TS_UNKNOWN {
            return value == TS_TRUE;
        }
        self.strict != TS_FALSE
    }

    // PORT: Go returns a nil-able `[]RootedDirectoryPath`; `Option<Vec<_>>`
    // preserves the `TypeRoots == nil` state (None) from the config.
    pub fn get_effective_type_roots(
        &self,
        current_directory: &tspath::RootedDirectoryPath,
    ) -> (Option<Vec<tspath::RootedDirectoryPath>>, bool) {
        if self.type_roots.is_some() {
            return (self.type_roots.clone(), true);
        }
        let base_dir;
        if !self.config_file_path.is_empty() {
            base_dir = self.config_file_path.directory();
        } else {
            base_dir = current_directory.clone();
            if base_dir.is_empty() {
                // This was accounted for in the TS codebase, but only for third-party API usage
                // where the module resolution host does not provide a getCurrentDirectory().
                panic!(
                    "cannot get effective type roots without a config file path or current directory"
                );
            }
        }

        let mut type_roots: Vec<tspath::RootedDirectoryPath> =
            Vec::with_capacity(base_dir.as_string().matches('/').count());
        base_dir.for_each_ancestor_directory(|dir| {
            type_roots.push(dir.resolve_directory("node_modules/@types"));
            ((), false)
        });
        (Some(type_roots), false)
    }

    // UsesWildcardTypes returns true if this option's types array includes "*"
    pub fn uses_wildcard_types(&self) -> bool {
        self.types
            .as_deref()
            .is_some_and(|types| types.iter().any(|t| t == "*"))
    }

    pub fn get_isolated_modules(&self) -> bool {
        self.isolated_modules == TS_TRUE || self.verbatim_module_syntax == TS_TRUE
    }

    pub fn is_incremental(&self) -> bool {
        self.incremental.is_true() || self.composite.is_true()
    }

    pub fn get_emit_standard_class_fields(&self) -> bool {
        self.use_define_for_class_fields != TS_FALSE
            && self.get_emit_script_target() >= ScriptTarget::ES2022
    }

    pub fn get_use_define_for_class_fields(&self) -> bool {
        if self.use_define_for_class_fields == TS_UNKNOWN {
            return self.get_emit_script_target() >= ScriptTarget::ES2022;
        }
        self.use_define_for_class_fields == TS_TRUE
    }

    pub fn get_emit_declarations(&self) -> bool {
        self.declaration.is_true() || self.composite.is_true()
    }

    pub fn get_are_declaration_maps_enabled(&self) -> bool {
        self.declaration_map == TS_TRUE && self.get_emit_declarations()
    }

    pub fn has_json_module_emit_enabled(&self) -> bool {
        match self.get_emit_module_kind() {
            ModuleKind::System | ModuleKind::UMD => return false,
            _ => {}
        }
        true
    }

    // PORT: Go returns `options.RootDirs` (nil-able); clone preserves the
    // Option.
    pub fn get_effective_root_dirs(&self) -> Option<Vec<tspath::RootedDirectoryPath>> {
        self.root_dirs.clone()
    }

    pub fn get_paths_base_path(
        &self,
        current_directory: &tspath::RootedDirectoryPath,
    ) -> tspath::RootedDirectoryPath {
        if self.paths.as_ref().is_none_or(|p| p.is_empty()) {
            return tspath::RootedDirectoryPath::default();
        }
        if !self.paths_base_path.is_empty() {
            return self.paths_base_path.clone();
        }
        current_directory.clone()
    }
}

impl ModuleKind {
    pub fn is_non_node_esm(&self) -> bool {
        *self >= ModuleKind::ES2015 && *self <= ModuleKind::ESNext
    }

    pub fn supports_import_attributes(&self) -> bool {
        ModuleKind::Node18 <= *self && *self <= ModuleKind::NodeNext
            || *self == ModuleKind::Preserve
            || *self == ModuleKind::ESNext
    }

    pub fn supports_deferred_imports(&self) -> bool {
        *self == ModuleKind::ESNext || *self == ModuleKind::Preserve
    }

    pub fn supports_source_phase_imports(&self) -> bool {
        *self == ModuleKind::ESNext
            || *self == ModuleKind::NodeNext
            || *self == ModuleKind::Preserve
    }
}

/// ModuleKindNone | ModuleKindCommonJS | ModuleKindESNext
pub type ResolutionMode = ModuleKind;

pub const RESOLUTION_MODE_NONE: ResolutionMode = ModuleKind::None;
pub const RESOLUTION_MODE_COMMON_JS: ResolutionMode = ModuleKind::CommonJS;
pub const RESOLUTION_MODE_ESM: ResolutionMode = ModuleKind::ESNext;

pub fn get_new_line_kind(s: &str) -> NewLineKind {
    match s {
        "\r\n" => NewLineKind::CRLF,
        "\n" => NewLineKind::LF,
        _ => NewLineKind::None,
    }
}

impl NewLineKind {
    pub fn get_new_line_character(&self) -> &'static str {
        match self {
            NewLineKind::CRLF => "\r\n",
            _ => "\n",
        }
    }
}
