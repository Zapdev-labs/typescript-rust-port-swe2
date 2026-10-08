// Ported from tsc/internal/tsoptions/showconfig.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::LazyLock;

use serde::Serialize;
use tsc_collections::OrderedMap;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::Tristate;
use tsc_tspath::{CaseSensitivity, RootedFilePath, RootedPath};

use crate::commandlineoption::CommandLineOptionRef;
use crate::generated::options::serialize_compiler_options;
use crate::parsedcommandline::ParsedCommandLine;
use crate::tsconfigparsing::{command_line_compiler_options_map, name_map_get};
use crate::value::Value;

/// `computeFn` equivalent — the compute functions below already return
/// `Value`, so no wrapper is needed.

/// `type impliedOption struct` — a compiler option whose effective value can
/// be derived from other options (TypeScript's computedOptions).
struct ImpliedOption {
    /// `name` is the Go struct field name of the CompilerOptions field
    /// (e.g., "Module").
    name: &'static str,
    /// `dependencies` lists the Go struct field names this option depends on.
    dependencies: &'static [&'static str],
    /// `compute` returns the effective value of this option.
    compute: fn(&CompilerOptions) -> Value,
}

/// `var impliedOptions`.
static IMPLIED_OPTIONS: &[ImpliedOption] = &[
    ImpliedOption {
        name: "Module",
        dependencies: &["Target"],
        compute: |o| Value::Int(o.get_emit_module_kind() as i64),
    },
    ImpliedOption {
        name: "ModuleResolution",
        dependencies: &["Module", "Target"],
        compute: |o| Value::Int(o.get_module_resolution_kind() as i64),
    },
    ImpliedOption {
        name: "ModuleDetection",
        dependencies: &["Module", "Target"],
        compute: |o| Value::Int(o.get_emit_module_detection_kind() as i64),
    },
    ImpliedOption {
        name: "IsolatedModules",
        dependencies: &["VerbatimModuleSyntax"],
        compute: |o| Value::Bool(o.get_isolated_modules()),
    },
    ImpliedOption {
        name: "PreserveConstEnums",
        dependencies: &["IsolatedModules", "VerbatimModuleSyntax"],
        compute: |o| Value::Bool(o.should_preserve_const_enums()),
    },
    ImpliedOption {
        name: "Declaration",
        dependencies: &["Composite"],
        compute: |o| Value::Bool(o.get_emit_declarations()),
    },
    ImpliedOption {
        name: "DeclarationMap",
        dependencies: &["Declaration", "Composite"],
        compute: |o| Value::Bool(o.get_are_declaration_maps_enabled()),
    },
    ImpliedOption {
        name: "Incremental",
        dependencies: &["Composite"],
        compute: |o| Value::Bool(o.is_incremental()),
    },
    ImpliedOption {
        name: "UseDefineForClassFields",
        dependencies: &["Target", "Module"],
        compute: |o| Value::Bool(o.get_use_define_for_class_fields()),
    },
    ImpliedOption {
        name: "ResolvePackageJsonExports",
        dependencies: &["ModuleResolution", "Module", "Target"],
        compute: |o| Value::Bool(o.get_resolve_package_json_exports()),
    },
    ImpliedOption {
        name: "ResolvePackageJsonImports",
        dependencies: &[
            "ModuleResolution",
            "ResolvePackageJsonExports",
            "Module",
            "Target",
        ],
        compute: |o| Value::Bool(o.get_resolve_package_json_imports()),
    },
    ImpliedOption {
        name: "ResolveJsonModule",
        dependencies: &["ModuleResolution", "Module", "Target"],
        compute: |o| Value::Bool(o.get_resolve_json_module()),
    },
    ImpliedOption {
        name: "AllowJs",
        dependencies: &["CheckJs"],
        compute: |o| Value::Bool(o.get_allow_js()),
    },
    ImpliedOption {
        name: "AllowImportingTsExtensions",
        dependencies: &["RewriteRelativeImportExtensions"],
        compute: |o| Value::Bool(o.get_allow_importing_ts_extensions()),
    },
];

/// `type TSConfig struct` — the output structure for `--showConfig`.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TsConfig {
    pub compiler_options: OrderedMap<String, Value>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub references: Vec<Value>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub files: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub include: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub exclude: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compile_on_save: Option<bool>,
}

/// `ConvertToTSConfig` — generates a complete tsconfig representation for
/// --showConfig output, matching TypeScript's convertToTSConfig function.
pub fn convert_to_ts_config(
    config_parse_result: &ParsedCommandLine,
    mut config_file_name: RootedFilePath,
) -> TsConfig {
    if config_file_name.as_string().is_empty() {
        config_file_name = config_parse_result
            .base_directory()
            .resolve_file("tsconfig.json");
    }
    let case_sensitivity = config_parse_result.case_sensitivity();

    // Build the list of all resolved files as relative paths from the config
    // file.
    let mut files = Vec::new();
    for f in config_parse_result.file_names() {
        match case_sensitivity.relative_path_from_file(&config_file_name, f) {
            Some(relative_path) => {
                files.push(relative_path.as_module_specifier().as_string().to_string())
            }
            None => files.push(f.as_string().to_string()),
        }
    }

    // Serialize compiler options
    // PORT: Go passes `configParseResult.CompilerOptions()` (nilable); a
    // missing options struct falls back to defaults.
    let compiler_options = config_parse_result
        .compiler_options()
        .cloned()
        .unwrap_or_default();
    let mut option_map =
        serialize_compiler_options(&compiler_options, config_file_name, case_sensitivity);

    for name in [
        "showConfig",
        "configFile",
        "configFilePath",
        "help",
        "init",
        "listFilesOnly",
        "listEmittedFiles",
        "project",
        "build",
        "version",
    ] {
        option_map.delete(name);
    }

    // Add implied compiler options (options that are derived from explicitly
    // set options, such as moduleResolution implied by module, or
    // useDefineForClassFields implied by target). This mirrors TypeScript's
    // convertToTSConfig computedOptions logic.
    add_implied_options(&mut option_map, &compiler_options);

    let mut config = TsConfig {
        compiler_options: option_map,
        references: Vec::new(),
        files: Vec::new(),
        include: Vec::new(),
        exclude: Vec::new(),
        compile_on_save: None,
    };

    // Add references
    let refs = config_parse_result.project_references();
    if !refs.is_empty() {
        let mut references = Vec::new();
        for r in refs {
            let mut ref_ = OrderedMap::<String, Value>::new();
            ref_.set("path".to_string(), Value::Str(r.original_path.clone()));
            if r.circular {
                ref_.set("circular".to_string(), Value::Bool(true));
            }
            references.push(Value::Map(ref_));
        }
        config.references = references;
    }

    // Add files
    if !files.is_empty() {
        config.files = files;
    }

    // Add include/exclude from configFileSpecs
    if let Some(specs) = config_parse_result.get_config_file_specs() {
        let include = filter_same_as_default_include(
            specs
                .validated_include_specs
                .iter()
                .map(|s| s.as_string().to_string())
                .collect(),
        );
        if !include.is_empty() {
            config.include = include;
        }
        config.exclude = specs
            .validated_exclude_specs
            .iter()
            .map(|s| s.as_string().to_string())
            .collect();
    }

    // Add compileOnSave
    if config_parse_result.compile_on_save == Some(true) {
        config.compile_on_save = Some(true);
    }

    config
}

/// `filterSameAsDefaultInclude` — returns `Vec::new` (Go nil) if specs is the
/// default include spec `["**/*"]`.
fn filter_same_as_default_include(specs: Vec<String>) -> Vec<String> {
    if specs.is_empty() {
        return Vec::new();
    }
    if specs.len() == 1 && specs[0] == crate::tsconfigparsing::DEFAULT_INCLUDE_SPEC {
        return Vec::new();
    }
    specs
}

/// `getNameOfCompilerOptionValue` — the string key for a given enum value by
/// searching the option's enum map.
fn get_name_of_compiler_option_value(
    value: &Value,
    enum_map: &OrderedMap<String, Value>,
) -> String {
    for (k, v) in enum_map.entries() {
        if v == value {
            return k.clone();
        }
    }
    String::new()
}

/// `serializeCompilerOptionPath`.
pub(crate) fn serialize_compiler_option_path(
    value: RootedPath,
    config_file_path: RootedFilePath,
    case_sensitivity: CaseSensitivity,
) -> String {
    if let Some(relative_path) =
        case_sensitivity.relative_path_from_file_to_path(&config_file_path, &value)
    {
        return relative_path.as_module_specifier().as_string().to_string();
    }
    value.as_string().to_string()
}

/// `serializeCompilerOptionEnumList`.
pub(crate) fn serialize_compiler_option_enum_list(
    values: &[String],
    enum_map: &OrderedMap<String, Value>,
) -> Vec<String> {
    values
        .iter()
        .map(|value| {
            let name = get_name_of_compiler_option_value(&Value::Str(value.clone()), enum_map);
            if !name.is_empty() {
                name
            } else {
                value.clone()
            }
        })
        .collect()
}

/// `addImpliedOptions` — adds compiler options implied by other
/// explicitly-set options, mirroring TypeScript's convertToTSConfig
/// computedOptions.
fn add_implied_options(option_map: &mut OrderedMap<String, Value>, options: &CompilerOptions) {
    // Build the set of explicitly provided option JSON names (e.g., "module",
    // "target").
    let provided: std::collections::HashSet<String> = option_map.keys().cloned().collect();

    let default_opts = CompilerOptions::default();

    for entry in IMPLIED_OPTIONS {
        // Get the option declaration for this implied option (using
        // case-insensitive lookup).
        let Some(option_decl) = name_map_get(command_line_compiler_options_map(), entry.name)
        else {
            continue;
        };

        // Skip if this option is already explicitly provided.
        if provided.contains(option_decl.name) {
            continue;
        }

        // Check if any direct dependency is in the provided set. This mirrors
        // TypeScript's optionDependsOn check.
        if !any_dependency_provided(entry.dependencies, &provided) {
            continue;
        }

        // Compute the effective value with current options and the default
        // value with empty options.
        let implied = (entry.compute)(options);
        let default_val = (entry.compute)(&default_opts);

        // If the implied value equals the default, this option doesn't add
        // useful information.
        if implied == default_val {
            continue;
        }

        // Serialize the implied value and add it to the option map.
        let serialized = serialize_implied_option_value(option_decl, &implied);
        if serialized.is_null() {
            continue;
        }
        option_map.set(option_decl.name.to_string(), serialized);
    }
}

/// `anyDependencyProvided` — true if any of the given dependency names (using
/// Go field names like "Target") corresponds to an option in the provided
/// set.
fn any_dependency_provided(
    dependencies: &[&'static str],
    provided: &std::collections::HashSet<String>,
) -> bool {
    for dep in dependencies {
        if let Some(dep_decl) = name_map_get(command_line_compiler_options_map(), dep)
            && provided.contains(dep_decl.name)
        {
            return true;
        }
    }
    false
}

/// `serializeImpliedOptionValue` — converts a computed implied option value
/// to its serializable form. For enum options, numeric values become their
/// string names; for boolean options, the bool is returned directly.
fn serialize_implied_option_value(option_decl: CommandLineOptionRef, value: &Value) -> Value {
    if value.is_null() {
        return Value::Null;
    }
    if let Some(enum_map) = option_decl.enum_map() {
        if let Value::Int(n) = value {
            let s = crate::generated::options::serialize_compiler_option_enum(enum_map, *n);
            if !s.is_empty() {
                return Value::Str(s.to_string());
            }
        }
        return Value::Null;
    }
    match value {
        Value::Bool(_) => value.clone(),
        Value::Tristate(t) => {
            if t.is_true() {
                Value::Bool(true)
            } else if *t == Tristate::False {
                Value::Bool(false)
            } else {
                Value::Null
            }
        }
        _ => value.clone(),
    }
}

// keep LazyLock imported for future statics
#[allow(dead_code)]
type _Unused = LazyLock<()>;
