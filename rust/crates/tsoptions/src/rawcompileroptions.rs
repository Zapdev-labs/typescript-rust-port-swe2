// Ported from tsc/internal/tsoptions/rawcompileroptions.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_collections::OrderedMap;
use tsc_core::options_generated::CompilerOptions;
use tsc_tspath::{self as tspath, RootedDirectoryPath};

use crate::commandlineoption::CommandLineOptionKind;
use crate::commandlineoption::CommandLineOptionPathKind;
use crate::parsinghelpers::{parse_compiler_options, parse_string_array};
use crate::tsconfigparsing::{
    command_line_compiler_options_map, get_substituted_path_with_config_dir_template,
    starts_with_config_dir_template,
};
use crate::value::{Value, value_into_go_map};

/// `RawCompilerOptions` is the JSON/API representation of compiler options.
/// Filesystem paths remain strings until `finalize` resolves them against a
/// base directory and constructs a `CompilerOptions` with typed path
/// guarantees.
#[derive(Clone, Default, Debug)]
pub struct RawCompilerOptions {
    pub values: Option<OrderedMap<String, Value>>,
}

impl Serialize for RawCompilerOptions {
    /// `(o) MarshalJSONTo`.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match &self.values {
            None => OrderedMap::<String, Value>::with_size_hint(0).serialize(serializer),
            Some(values) => values.serialize(serializer),
        }
    }
}

impl<'de> Deserialize<'de> for RawCompilerOptions {
    /// `(o) UnmarshalJSONFrom`.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Go: a `null` token leaves `values` nil-but-initialized; a non-object
        // is an error. serde's `Option`/`Value` split covers both.
        // Deserialize directly into OrderedMap<String, Value>: the custom
        // Value::deserialize preserves the JSON document order at every level
        // (serde_json::Value would use a sorted BTreeMap).
        let raw: Option<OrderedMap<String, Value>> = Option::deserialize(deserializer)?;
        let Some(raw) = raw else {
            return Ok(RawCompilerOptions {
                values: Some(OrderedMap::with_size_hint(0)),
            });
        };
        let mut values = OrderedMap::with_size_hint(raw.size());
        for (key, value) in raw.entries() {
            let value = if key == "paths" {
                // `paths` decodes into `*OrderedMap` (still `Value::Map`).
                value.clone()
            } else {
                // Other members decode into `map[string]any` — preserved quirk.
                value_into_go_map(value.clone())
            };
            values.set(key.clone(), value);
        }
        Ok(RawCompilerOptions {
            values: Some(values),
        })
    }
}

impl RawCompilerOptions {
    /// `(o) Finalize`.
    pub fn finalize(
        &self,
        base_path: &RootedDirectoryPath,
    ) -> (CompilerOptions, Vec<DiagnosticRef>) {
        let mut options = CompilerOptions::default();
        let Some(values) = &self.values else {
            return (options, Vec::new());
        };
        let diagnostics = Vec::new();
        for (key, value) in values.entries() {
            let option =
                crate::tsconfigparsing::name_map_get(command_line_compiler_options_map(), key);
            if let Some(option) = option {
                if key != option.name {
                    continue;
                }
            }
            let mut path_kind = CommandLineOptionPathKind::None;
            if let Some(option) = option {
                path_kind = option.path_kind;
                if option.kind == CommandLineOptionKind::List {
                    if let Some(element) = option.elements() {
                        path_kind = element.path_kind;
                    }
                }
            } else if key == "configFilePath" {
                path_kind = CommandLineOptionPathKind::File;
            } else if key != "allowNonTsExtensions" && key != "suppressOutputPathCheck" {
                continue;
            }
            let mut value = value.clone();
            if path_kind.is_rooted() {
                if option.is_some_and(|o| o.kind == CommandLineOptionKind::List) {
                    value = Value::List(
                        parse_string_array(&value)
                            .unwrap_or_default()
                            .iter()
                            .map(|path| {
                                if starts_with_config_dir_template(path) {
                                    Value::Str(get_substituted_path_with_config_dir_template(
                                        path, base_path,
                                    ))
                                } else {
                                    Value::Str(
                                        tspath::get_normalized_absolute_path(path, base_path)
                                            .into_owned(),
                                    )
                                }
                            })
                            .collect(),
                    );
                } else if let Some(path) = value.as_str().filter(|p| !p.is_empty()) {
                    if starts_with_config_dir_template(path) {
                        value = Value::Str(get_substituted_path_with_config_dir_template(
                            path, base_path,
                        ));
                    } else {
                        value = Value::Str(
                            tspath::get_normalized_absolute_path(path, base_path).into_owned(),
                        );
                    }
                }
            }
            parse_compiler_options(key, &value, &mut options);
        }
        (options, diagnostics)
    }
}
