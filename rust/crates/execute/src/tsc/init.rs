// Ported from tsc/internal/execute/tsc/init.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io::Write as _;
use std::sync::Arc;

use tsc_ast::diagnostic::new_compiler_diagnostic;
use tsc_collections::OrderedMap;
use tsc_core::options_generated::{JsxEmit, ModuleDetectionKind, ModuleKind, ScriptTarget};
use tsc_locale::Locale;
use tsc_tsoptions::generated::declarations;
use tsc_tsoptions::value::Value;

use crate::tsc::compile::System;
use crate::tsc::diagnostics::DiagnosticReporter;
use crate::tsc::help::get_header;

/// `WriteConfigFile`.
pub fn write_config_file(
    sys: &Arc<dyn System>,
    locale: &Locale,
    report_diagnostic: &DiagnosticReporter,
    options: &OrderedMap<String, Value>,
) {
    let current_directory = sys.current_directory();
    let file = current_directory.resolve_file("tsconfig.json");
    if sys.fs().file_exists(&file) {
        report_diagnostic(&new_compiler_diagnostic(
            &tsc_diagnostics::A_tsconfig_json_file_is_already_defined_at_Colon_0,
            &[file.as_string()],
        ));
    } else {
        let _ = sys
            .fs()
            .write_file(&file, &generate_tsconfig(options, locale));
        let mut output: Vec<String> = vec!["\n".to_string()];
        output.extend(get_header(sys, "Created a new tsconfig.json"));
        output.push("You can learn more at https://aka.ms/tsconfig".to_string());
        output.push("\n".to_string());
        let _ = write!(sys.writer().guard(), "{}", output.concat());
    }
}

/// `generateTSConfig`.
fn generate_tsconfig(options: &OrderedMap<String, Value>, locale: &Locale) -> String {
    const TAB: &str = "  ";
    let mut result: Vec<String> = Vec::new();

    let mut all_set_options: Vec<String> = Vec::with_capacity(options.size());
    for k in options.keys() {
        if k != "init" && k != "help" && k != "watch" {
            all_set_options.push(k.clone());
        }
    }

    let emit_header = |result: &mut Vec<String>, header: &'static tsc_diagnostics::Message| {
        result.push(format!(
            "{TAB}{TAB}// {}",
            header.localize(locale, &[] as &[String])
        ));
    };

    // `push("{")`
    result.push("{".to_string());
    result.push(format!(
        "{TAB}// {}",
        tsc_diagnostics::Visit_https_Colon_Slash_Slashaka_ms_Slashtsconfig_to_read_more_about_this_file
            .localize(locale, &[] as &[String])
    ));
    result.push(format!("{TAB}\"compilerOptions\": {{"));

    emit_header(&mut result, &tsc_diagnostics::File_Layout);
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "rootDir",
        Value::Str("./src".to_string()),
        Commented::Optional,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "outDir",
        Value::Str("./dist".to_string()),
        Commented::Optional,
    );

    result.push(String::new());

    emit_header(&mut result, &tsc_diagnostics::Environment_Settings);
    emit_header(
        &mut result,
        &tsc_diagnostics::See_also_https_Colon_Slash_Slashaka_ms_Slashtsconfig_Slashmodule,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "module",
        Value::Int(ModuleKind::NodeNext as i64),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "target",
        Value::Int(ScriptTarget::ESNext as i64),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "types",
        Value::List(Vec::new()),
        Commented::Never,
    );
    if let Some(lib) = options.get("lib") {
        emit_option(
            &mut result,
            options,
            &mut all_set_options,
            "lib",
            lib.clone(),
            Commented::Never,
        );
    }
    emit_header(&mut result, &tsc_diagnostics::For_nodejs_Colon);
    result.push(format!("{TAB}{TAB}// \"lib\": [\"esnext\"],"));
    result.push(format!("{TAB}{TAB}// \"types\": [\"node\"],"));
    emit_header(
        &mut result,
        &tsc_diagnostics::X_and_npm_install_D_types_Slashnode,
    );

    result.push(String::new());

    emit_header(&mut result, &tsc_diagnostics::Other_Outputs);
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "sourceMap",
        Value::Bool(true),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "declaration",
        Value::Bool(true),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "declarationMap",
        Value::Bool(true),
        Commented::Never,
    );

    result.push(String::new());

    emit_header(&mut result, &tsc_diagnostics::Stricter_Typechecking_Options);
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "noUncheckedIndexedAccess",
        Value::Bool(true),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "exactOptionalPropertyTypes",
        Value::Bool(true),
        Commented::Never,
    );

    result.push(String::new());

    emit_header(&mut result, &tsc_diagnostics::Style_Options);
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "noImplicitReturns",
        Value::Bool(true),
        Commented::Optional,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "noImplicitOverride",
        Value::Bool(true),
        Commented::Optional,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "noUnusedLocals",
        Value::Bool(true),
        Commented::Optional,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "noUnusedParameters",
        Value::Bool(true),
        Commented::Optional,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "noFallthroughCasesInSwitch",
        Value::Bool(true),
        Commented::Optional,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "noPropertyAccessFromIndexSignature",
        Value::Bool(true),
        Commented::Optional,
    );

    result.push(String::new());

    emit_header(&mut result, &tsc_diagnostics::Recommended_Options);
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "strict",
        Value::Bool(true),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "jsx",
        Value::Int(JsxEmit::ReactJSX as i64),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "verbatimModuleSyntax",
        Value::Bool(true),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "isolatedModules",
        Value::Bool(true),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "noUncheckedSideEffectImports",
        Value::Bool(true),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "moduleDetection",
        Value::Int(ModuleDetectionKind::Force as i64),
        Commented::Never,
    );
    emit_option(
        &mut result,
        options,
        &mut all_set_options,
        "skipLibCheck",
        Value::Bool(true),
        Commented::Never,
    );

    // Write any user-provided options we haven't already
    if !all_set_options.is_empty() {
        result.push(String::new());
        while let Some(setting) = all_set_options.first().cloned() {
            emit_option(
                &mut result,
                options,
                &mut all_set_options,
                &setting,
                options.get_or_zero(&setting),
                Commented::Never,
            );
        }
    }

    result.push(format!("{TAB}}}"));
    result.push("}".to_string());
    result.push(String::new());

    result.join("\n")
}

/// `emitOption` — `commentedNever`/`commentedAlways`/`commentedOptional`
/// become [`Commented`]; the Go `defaultValue any` is `Value`.
fn emit_option(
    result: &mut Vec<String>,
    options: &OrderedMap<String, Value>,
    all_set_options: &mut Vec<String>,
    setting: &str,
    default_value: Value,
    commented: Commented,
) {
    if let Some(index) = all_set_options.iter().position(|s| s == setting) {
        all_set_options.remove(index);
    }

    let comment = match commented {
        Commented::Always => true,
        Commented::Never => false,
        // `commentedOptional`: comment out unless it's on the command line.
        Commented::Optional => !options.has(setting),
    };

    let value = options.get(setting).cloned().unwrap_or(default_value);

    let text = format_value_or_array(setting, &value);
    if comment {
        result.push(format!("    // \"{setting}\": {text},"));
    } else {
        result.push(format!("    \"{setting}\": {text},"));
    }
}

/// `formatValueOrArray`.
fn format_value_or_array(setting_name: &str, value: &Value) -> String {
    let option = declarations::options_declarations()
        .find(|decl| decl.name == setting_name)
        .unwrap_or_else(|| panic!("No option named {setting_name}"));

    if value.is_slice() {
        let enum_map = option
            .elements()
            .and_then(|elem_option| elem_option.enum_map());
        // `Value::Plugins` (`[]core.PluginImport`) has no per-element
        // `Value`, so its elements are marshaled directly — Go's reflection
        // produces the same `[{...}, ...]` output.
        let elems: Vec<String> = match value {
            Value::Plugins(items) => items
                .iter()
                .map(|p| {
                    String::from_utf8(
                        tsc_json::marshal_indent(p, "", "").expect("plugin import should marshal"),
                    )
                    .expect("json is utf8")
                })
                .collect(),
            _ => slice_elements(value)
                .iter()
                .map(|elem| format_single_value(elem, enum_map))
                .collect(),
        };
        format!("[{}]", elems.join(", "))
    } else {
        format_single_value(value, option.enum_map())
    }
}

/// `reflect.ValueOf(value).Kind() == reflect.Slice` — the slice-typed
/// `Value` arms as an element list.
fn slice_elements(value: &Value) -> Vec<Value> {
    match value {
        Value::List(items) => items.clone(),
        Value::StringList(items) => items.iter().map(|s| Value::Str(s.clone())).collect(),
        Value::FilePathList(items) => items.iter().map(|p| Value::FilePath(p.clone())).collect(),
        Value::DirPathList(items) => items.iter().map(|p| Value::DirPath(p.clone())).collect(),
        _ => unreachable!("value is not a slice"),
    }
}

/// `formatSingleValue` — enum values are looked up in the option's enum map
/// and replaced by their key name, then marshaled to compact JSON.
fn format_single_value(value: &Value, enum_map: Option<&OrderedMap<String, Value>>) -> String {
    let mut value = value.clone();
    if let Some(enum_map) = enum_map {
        let mut found = false;
        for (k, v) in enum_map.entries() {
            if value == *v {
                value = Value::Str(k.clone());
                found = true;
                break;
            }
        }
        if !found {
            panic!("No matching value of {value:?}");
        }
    }

    match tsc_json::marshal_indent(&value, "", "") {
        Ok(bytes) => String::from_utf8(bytes).expect("json is utf8"),
        Err(err) => panic!("should not happen: {err}"),
    }
}

/// `type commented int` — `commentedNever`/`commentedAlways`/`commentedOptional`.
/// Never comment this out / always comment out / comment unless on the
/// command line.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Commented {
    Never,
    /// `commentedAlways` — no `emitOption` call uses it (as in Go); kept for
    /// enum parity.
    #[allow(dead_code)]
    Always,
    Optional,
}
