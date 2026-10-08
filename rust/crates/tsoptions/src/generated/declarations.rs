// Ported from tsc/internal/tsoptions/declarations_generated.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// This file is generated from the Go source by testgen/gen_declarations.py
// with handwritten glue appended. Do not edit by hand; regenerate instead.

use std::sync::LazyLock;

use tsc_collections::OrderedMap;
use tsc_collections::Set;
use tsc_core::options_generated::{
    JsxEmit, ModuleDetectionKind, ModuleKind, ModuleResolutionKind, NewLineKind, ScriptTarget,
};
use tsc_core::tristate::TS_UNKNOWN;
use tsc_diagnostics as diagnostics;

use crate::commandlineoption::{
    CommandLineOption, CommandLineOptionKind, CommandLineOptionPathKind, CommandLineOptionRef,
    DefaultValueDescription, EXTRA_VALIDATION_LOCALE, ElementOptions,
};
use crate::value::Value;

const DEFAULT_COMMAND_LINE_OPTION: CommandLineOption = CommandLineOption {
    name: "",
    short_name: "",
    kind: CommandLineOptionKind::BOOLEAN,
    path_kind: CommandLineOptionPathKind::None,
    is_file_path: false,
    is_ts_config_only: false,
    is_command_line_only: false,
    description: None,
    default_value_description: DefaultValueDescription::None,
    show_in_simplified_help_view: false,
    category: None,
    extra_validation: None,
    min_value: 0,
    list_preserve_falsy_values: false,
    element_options: None,
};

// var TscBuildOption
static TSC_BUILD_OPTION: CommandLineOption = CommandLineOption {
    name: "build",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "b",
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(
        &diagnostics::Build_one_or_more_projects_and_their_dependencies_if_out_of_date,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};

// var compilerOptionsDeclaration
static COMPILER_OPTIONS_DECLARATION: CommandLineOption = CommandLineOption {
    name: "compilerOptions",
    kind: CommandLineOptionKind::OBJECT,
    element_options: Some(ElementOptions::CompilerOptions),
    ..DEFAULT_COMMAND_LINE_OPTION
};

// var typeAcquisitionDeclaration
static TYPE_ACQUISITION_DECLARATION: CommandLineOption = CommandLineOption {
    name: "typeAcquisition",
    kind: CommandLineOptionKind::OBJECT,
    element_options: Some(ElementOptions::TypeAcquisition),
    ..DEFAULT_COMMAND_LINE_OPTION
};

// var extendsOptionDeclaration
static EXTENDS_OPTION_DECLARATION: CommandLineOption = CommandLineOption {
    name: "extends",
    kind: CommandLineOptionKind::LIST_OR_ELEMENT,
    category: Some(&diagnostics::File_Management),
    element_options: Some(ElementOptions::Extends),
    ..DEFAULT_COMMAND_LINE_OPTION
};

// var compileOnSaveCommandLineOption
static COMPILE_ON_SAVE_COMMAND_LINE_OPTION: CommandLineOption = CommandLineOption {
    name: "compileOnSave",
    kind: CommandLineOptionKind::BOOLEAN,
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};

// var tsconfigRootOptionsMap
static TSCONFIG_ROOT_OPTIONS_MAP: CommandLineOption = CommandLineOption {
    name: "undefined",
    kind: CommandLineOptionKind::OBJECT,
    element_options: Some(ElementOptions::TsconfigRoot),
    ..DEFAULT_COMMAND_LINE_OPTION
};

pub static LIB_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(116);
    map.set("es5".to_string(), Value::Str("lib.es5.d.ts".into()));
    map.set("es6".to_string(), Value::Str("lib.es2015.d.ts".into()));
    map.set("es2015".to_string(), Value::Str("lib.es2015.d.ts".into()));
    map.set("es7".to_string(), Value::Str("lib.es2016.d.ts".into()));
    map.set("es2016".to_string(), Value::Str("lib.es2016.d.ts".into()));
    map.set("es2017".to_string(), Value::Str("lib.es2017.d.ts".into()));
    map.set("es2018".to_string(), Value::Str("lib.es2018.d.ts".into()));
    map.set("es2019".to_string(), Value::Str("lib.es2019.d.ts".into()));
    map.set("es2020".to_string(), Value::Str("lib.es2020.d.ts".into()));
    map.set("es2021".to_string(), Value::Str("lib.es2021.d.ts".into()));
    map.set("es2022".to_string(), Value::Str("lib.es2022.d.ts".into()));
    map.set("es2023".to_string(), Value::Str("lib.es2023.d.ts".into()));
    map.set("es2024".to_string(), Value::Str("lib.es2024.d.ts".into()));
    map.set("es2025".to_string(), Value::Str("lib.es2025.d.ts".into()));
    map.set("es2026".to_string(), Value::Str("lib.es2026.d.ts".into()));
    map.set("esnext".to_string(), Value::Str("lib.esnext.d.ts".into()));
    map.set("dom".to_string(), Value::Str("lib.dom.d.ts".into()));
    map.set(
        "dom.iterable".to_string(),
        Value::Str("lib.dom.iterable.d.ts".into()),
    );
    map.set(
        "dom.asynciterable".to_string(),
        Value::Str("lib.dom.asynciterable.d.ts".into()),
    );
    map.set(
        "webworker".to_string(),
        Value::Str("lib.webworker.d.ts".into()),
    );
    map.set(
        "webworker.importscripts".to_string(),
        Value::Str("lib.webworker.importscripts.d.ts".into()),
    );
    map.set(
        "webworker.iterable".to_string(),
        Value::Str("lib.webworker.iterable.d.ts".into()),
    );
    map.set(
        "webworker.asynciterable".to_string(),
        Value::Str("lib.webworker.asynciterable.d.ts".into()),
    );
    map.set(
        "scripthost".to_string(),
        Value::Str("lib.scripthost.d.ts".into()),
    );
    map.set(
        "es2015.core".to_string(),
        Value::Str("lib.es2015.core.d.ts".into()),
    );
    map.set(
        "es2015.collection".to_string(),
        Value::Str("lib.es2015.collection.d.ts".into()),
    );
    map.set(
        "es2015.generator".to_string(),
        Value::Str("lib.es2015.generator.d.ts".into()),
    );
    map.set(
        "es2015.iterable".to_string(),
        Value::Str("lib.es2015.iterable.d.ts".into()),
    );
    map.set(
        "es2015.promise".to_string(),
        Value::Str("lib.es2015.promise.d.ts".into()),
    );
    map.set(
        "es2015.proxy".to_string(),
        Value::Str("lib.es2015.proxy.d.ts".into()),
    );
    map.set(
        "es2015.reflect".to_string(),
        Value::Str("lib.es2015.reflect.d.ts".into()),
    );
    map.set(
        "es2015.symbol".to_string(),
        Value::Str("lib.es2015.symbol.d.ts".into()),
    );
    map.set(
        "es2015.symbol.wellknown".to_string(),
        Value::Str("lib.es2015.symbol.wellknown.d.ts".into()),
    );
    map.set(
        "es2016.array.include".to_string(),
        Value::Str("lib.es2016.array.include.d.ts".into()),
    );
    map.set(
        "es2016.intl".to_string(),
        Value::Str("lib.es2016.intl.d.ts".into()),
    );
    map.set(
        "es2017.arraybuffer".to_string(),
        Value::Str("lib.es2017.arraybuffer.d.ts".into()),
    );
    map.set(
        "es2017.date".to_string(),
        Value::Str("lib.es2017.date.d.ts".into()),
    );
    map.set(
        "es2017.object".to_string(),
        Value::Str("lib.es2017.object.d.ts".into()),
    );
    map.set(
        "es2017.sharedmemory".to_string(),
        Value::Str("lib.es2017.sharedmemory.d.ts".into()),
    );
    map.set(
        "es2017.string".to_string(),
        Value::Str("lib.es2017.string.d.ts".into()),
    );
    map.set(
        "es2017.intl".to_string(),
        Value::Str("lib.es2017.intl.d.ts".into()),
    );
    map.set(
        "es2017.typedarrays".to_string(),
        Value::Str("lib.es2017.typedarrays.d.ts".into()),
    );
    map.set(
        "es2018.asyncgenerator".to_string(),
        Value::Str("lib.es2018.asyncgenerator.d.ts".into()),
    );
    map.set(
        "es2018.asynciterable".to_string(),
        Value::Str("lib.es2018.asynciterable.d.ts".into()),
    );
    map.set(
        "es2018.intl".to_string(),
        Value::Str("lib.es2018.intl.d.ts".into()),
    );
    map.set(
        "es2018.promise".to_string(),
        Value::Str("lib.es2018.promise.d.ts".into()),
    );
    map.set(
        "es2018.regexp".to_string(),
        Value::Str("lib.es2018.regexp.d.ts".into()),
    );
    map.set(
        "es2019.array".to_string(),
        Value::Str("lib.es2019.array.d.ts".into()),
    );
    map.set(
        "es2019.object".to_string(),
        Value::Str("lib.es2019.object.d.ts".into()),
    );
    map.set(
        "es2019.string".to_string(),
        Value::Str("lib.es2019.string.d.ts".into()),
    );
    map.set(
        "es2019.symbol".to_string(),
        Value::Str("lib.es2019.symbol.d.ts".into()),
    );
    map.set(
        "es2019.intl".to_string(),
        Value::Str("lib.es2019.intl.d.ts".into()),
    );
    map.set(
        "es2020.bigint".to_string(),
        Value::Str("lib.es2020.bigint.d.ts".into()),
    );
    map.set(
        "es2020.date".to_string(),
        Value::Str("lib.es2020.date.d.ts".into()),
    );
    map.set(
        "es2020.promise".to_string(),
        Value::Str("lib.es2020.promise.d.ts".into()),
    );
    map.set(
        "es2020.sharedmemory".to_string(),
        Value::Str("lib.es2020.sharedmemory.d.ts".into()),
    );
    map.set(
        "es2020.string".to_string(),
        Value::Str("lib.es2020.string.d.ts".into()),
    );
    map.set(
        "es2020.symbol.wellknown".to_string(),
        Value::Str("lib.es2020.symbol.wellknown.d.ts".into()),
    );
    map.set(
        "es2020.intl".to_string(),
        Value::Str("lib.es2020.intl.d.ts".into()),
    );
    map.set(
        "es2020.number".to_string(),
        Value::Str("lib.es2020.number.d.ts".into()),
    );
    map.set(
        "es2021.promise".to_string(),
        Value::Str("lib.es2021.promise.d.ts".into()),
    );
    map.set(
        "es2021.string".to_string(),
        Value::Str("lib.es2021.string.d.ts".into()),
    );
    map.set(
        "es2021.weakref".to_string(),
        Value::Str("lib.es2021.weakref.d.ts".into()),
    );
    map.set(
        "es2021.intl".to_string(),
        Value::Str("lib.es2021.intl.d.ts".into()),
    );
    map.set(
        "es2022.array".to_string(),
        Value::Str("lib.es2022.array.d.ts".into()),
    );
    map.set(
        "es2022.error".to_string(),
        Value::Str("lib.es2022.error.d.ts".into()),
    );
    map.set(
        "es2022.intl".to_string(),
        Value::Str("lib.es2022.intl.d.ts".into()),
    );
    map.set(
        "es2022.object".to_string(),
        Value::Str("lib.es2022.object.d.ts".into()),
    );
    map.set(
        "es2022.string".to_string(),
        Value::Str("lib.es2022.string.d.ts".into()),
    );
    map.set(
        "es2022.regexp".to_string(),
        Value::Str("lib.es2022.regexp.d.ts".into()),
    );
    map.set(
        "es2023.array".to_string(),
        Value::Str("lib.es2023.array.d.ts".into()),
    );
    map.set(
        "es2023.collection".to_string(),
        Value::Str("lib.es2023.collection.d.ts".into()),
    );
    map.set(
        "es2023.intl".to_string(),
        Value::Str("lib.es2023.intl.d.ts".into()),
    );
    map.set(
        "es2024.arraybuffer".to_string(),
        Value::Str("lib.es2024.arraybuffer.d.ts".into()),
    );
    map.set(
        "es2024.collection".to_string(),
        Value::Str("lib.es2024.collection.d.ts".into()),
    );
    map.set(
        "es2024.object".to_string(),
        Value::Str("lib.es2024.object.d.ts".into()),
    );
    map.set(
        "es2024.promise".to_string(),
        Value::Str("lib.es2024.promise.d.ts".into()),
    );
    map.set(
        "es2024.regexp".to_string(),
        Value::Str("lib.es2024.regexp.d.ts".into()),
    );
    map.set(
        "es2024.sharedmemory".to_string(),
        Value::Str("lib.es2024.sharedmemory.d.ts".into()),
    );
    map.set(
        "es2024.string".to_string(),
        Value::Str("lib.es2024.string.d.ts".into()),
    );
    map.set(
        "es2025.collection".to_string(),
        Value::Str("lib.es2025.collection.d.ts".into()),
    );
    map.set(
        "es2025.float16".to_string(),
        Value::Str("lib.es2025.float16.d.ts".into()),
    );
    map.set(
        "es2025.intl".to_string(),
        Value::Str("lib.es2025.intl.d.ts".into()),
    );
    map.set(
        "es2025.iterator".to_string(),
        Value::Str("lib.es2025.iterator.d.ts".into()),
    );
    map.set(
        "es2025.promise".to_string(),
        Value::Str("lib.es2025.promise.d.ts".into()),
    );
    map.set(
        "es2025.regexp".to_string(),
        Value::Str("lib.es2025.regexp.d.ts".into()),
    );
    map.set(
        "es2026.array".to_string(),
        Value::Str("lib.es2026.array.d.ts".into()),
    );
    map.set(
        "es2026.collection".to_string(),
        Value::Str("lib.es2026.collection.d.ts".into()),
    );
    map.set(
        "es2026.error".to_string(),
        Value::Str("lib.es2026.error.d.ts".into()),
    );
    map.set(
        "es2026.iterator".to_string(),
        Value::Str("lib.es2026.iterator.d.ts".into()),
    );
    map.set(
        "es2026.json".to_string(),
        Value::Str("lib.es2026.json.d.ts".into()),
    );
    map.set(
        "es2026.math".to_string(),
        Value::Str("lib.es2026.math.d.ts".into()),
    );
    map.set(
        "es2026.typedarrays".to_string(),
        Value::Str("lib.es2026.typedarrays.d.ts".into()),
    );
    map.set(
        "esnext.asynciterable".to_string(),
        Value::Str("lib.es2018.asynciterable.d.ts".into()),
    );
    map.set(
        "esnext.symbol".to_string(),
        Value::Str("lib.es2019.symbol.d.ts".into()),
    );
    map.set(
        "esnext.bigint".to_string(),
        Value::Str("lib.es2020.bigint.d.ts".into()),
    );
    map.set(
        "esnext.weakref".to_string(),
        Value::Str("lib.es2021.weakref.d.ts".into()),
    );
    map.set(
        "esnext.object".to_string(),
        Value::Str("lib.es2024.object.d.ts".into()),
    );
    map.set(
        "esnext.regexp".to_string(),
        Value::Str("lib.es2024.regexp.d.ts".into()),
    );
    map.set(
        "esnext.string".to_string(),
        Value::Str("lib.es2024.string.d.ts".into()),
    );
    map.set(
        "esnext.float16".to_string(),
        Value::Str("lib.es2025.float16.d.ts".into()),
    );
    map.set(
        "esnext.array".to_string(),
        Value::Str("lib.es2026.array.d.ts".into()),
    );
    map.set(
        "esnext.collection".to_string(),
        Value::Str("lib.es2026.collection.d.ts".into()),
    );
    map.set(
        "esnext.error".to_string(),
        Value::Str("lib.es2026.error.d.ts".into()),
    );
    map.set(
        "esnext.iterator".to_string(),
        Value::Str("lib.es2026.iterator.d.ts".into()),
    );
    map.set(
        "esnext.typedarrays".to_string(),
        Value::Str("lib.es2026.typedarrays.d.ts".into()),
    );
    map.set(
        "esnext.promise".to_string(),
        Value::Str("lib.esnext.promise.d.ts".into()),
    );
    map.set(
        "esnext.date".to_string(),
        Value::Str("lib.esnext.date.d.ts".into()),
    );
    map.set(
        "esnext.decorators".to_string(),
        Value::Str("lib.esnext.decorators.d.ts".into()),
    );
    map.set(
        "esnext.disposable".to_string(),
        Value::Str("lib.esnext.disposable.d.ts".into()),
    );
    map.set(
        "esnext.intl".to_string(),
        Value::Str("lib.esnext.intl.d.ts".into()),
    );
    map.set(
        "esnext.modulesource".to_string(),
        Value::Str("lib.esnext.modulesource.d.ts".into()),
    );
    map.set(
        "esnext.sharedmemory".to_string(),
        Value::Str("lib.esnext.sharedmemory.d.ts".into()),
    );
    map.set(
        "esnext.temporal".to_string(),
        Value::Str("lib.esnext.temporal.d.ts".into()),
    );
    map.set(
        "decorators".to_string(),
        Value::Str("lib.decorators.d.ts".into()),
    );
    map.set(
        "decorators.legacy".to_string(),
        Value::Str("lib.decorators.legacy.d.ts".into()),
    );
    map
});

pub static MODULE_RESOLUTION_OPTION_MAP: LazyLock<OrderedMap<String, Value>> =
    LazyLock::new(|| {
        let mut map = OrderedMap::with_size_hint(6);
        map.set(
            "node16".to_string(),
            Value::Int(ModuleResolutionKind::Node16 as i64),
        );
        map.set(
            "nodenext".to_string(),
            Value::Int(ModuleResolutionKind::NodeNext as i64),
        );
        map.set(
            "bundler".to_string(),
            Value::Int(ModuleResolutionKind::Bundler as i64),
        );
        map.set(
            "classic".to_string(),
            Value::Int(ModuleResolutionKind::Classic as i64),
        );
        map.set(
            "node".to_string(),
            Value::Int(ModuleResolutionKind::Node10 as i64),
        );
        map.set(
            "node10".to_string(),
            Value::Int(ModuleResolutionKind::Node10 as i64),
        );
        map
    });

pub static MODULE_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(14);
    map.set(
        "commonjs".to_string(),
        Value::Int(ModuleKind::CommonJS as i64),
    );
    map.set("amd".to_string(), Value::Int(ModuleKind::AMD as i64));
    map.set("system".to_string(), Value::Int(ModuleKind::System as i64));
    map.set("umd".to_string(), Value::Int(ModuleKind::UMD as i64));
    map.set("es6".to_string(), Value::Int(ModuleKind::ES2015 as i64));
    map.set("es2015".to_string(), Value::Int(ModuleKind::ES2015 as i64));
    map.set("es2020".to_string(), Value::Int(ModuleKind::ES2020 as i64));
    map.set("es2022".to_string(), Value::Int(ModuleKind::ES2022 as i64));
    map.set("esnext".to_string(), Value::Int(ModuleKind::ESNext as i64));
    map.set("node16".to_string(), Value::Int(ModuleKind::Node16 as i64));
    map.set("node18".to_string(), Value::Int(ModuleKind::Node18 as i64));
    map.set("node20".to_string(), Value::Int(ModuleKind::Node20 as i64));
    map.set(
        "nodenext".to_string(),
        Value::Int(ModuleKind::NodeNext as i64),
    );
    map.set(
        "preserve".to_string(),
        Value::Int(ModuleKind::Preserve as i64),
    );
    map
});

pub static TARGET_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(15);
    map.set("es5".to_string(), Value::Int(ScriptTarget::ES5 as i64));
    map.set("es6".to_string(), Value::Int(ScriptTarget::ES2015 as i64));
    map.set(
        "es2015".to_string(),
        Value::Int(ScriptTarget::ES2015 as i64),
    );
    map.set(
        "es2016".to_string(),
        Value::Int(ScriptTarget::ES2016 as i64),
    );
    map.set(
        "es2017".to_string(),
        Value::Int(ScriptTarget::ES2017 as i64),
    );
    map.set(
        "es2018".to_string(),
        Value::Int(ScriptTarget::ES2018 as i64),
    );
    map.set(
        "es2019".to_string(),
        Value::Int(ScriptTarget::ES2019 as i64),
    );
    map.set(
        "es2020".to_string(),
        Value::Int(ScriptTarget::ES2020 as i64),
    );
    map.set(
        "es2021".to_string(),
        Value::Int(ScriptTarget::ES2021 as i64),
    );
    map.set(
        "es2022".to_string(),
        Value::Int(ScriptTarget::ES2022 as i64),
    );
    map.set(
        "es2023".to_string(),
        Value::Int(ScriptTarget::ES2023 as i64),
    );
    map.set(
        "es2024".to_string(),
        Value::Int(ScriptTarget::ES2024 as i64),
    );
    map.set(
        "es2025".to_string(),
        Value::Int(ScriptTarget::ES2025 as i64),
    );
    map.set(
        "es2026".to_string(),
        Value::Int(ScriptTarget::ES2026 as i64),
    );
    map.set(
        "esnext".to_string(),
        Value::Int(ScriptTarget::ESNext as i64),
    );
    map
});

pub static MODULE_DETECTION_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(3);
    map.set(
        "auto".to_string(),
        Value::Int(ModuleDetectionKind::Auto as i64),
    );
    map.set(
        "legacy".to_string(),
        Value::Int(ModuleDetectionKind::Legacy as i64),
    );
    map.set(
        "force".to_string(),
        Value::Int(ModuleDetectionKind::Force as i64),
    );
    map
});

pub static JSX_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(5);
    map.set("preserve".to_string(), Value::Int(JsxEmit::Preserve as i64));
    map.set(
        "react-native".to_string(),
        Value::Int(JsxEmit::ReactNative as i64),
    );
    map.set(
        "react-jsx".to_string(),
        Value::Int(JsxEmit::ReactJSX as i64),
    );
    map.set(
        "react-jsxdev".to_string(),
        Value::Int(JsxEmit::ReactJSXDev as i64),
    );
    map.set("react".to_string(), Value::Int(JsxEmit::React as i64));
    map
});

pub static NEW_LINE_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(2);
    map.set("crlf".to_string(), Value::Int(NewLineKind::CRLF as i64));
    map.set("lf".to_string(), Value::Int(NewLineKind::LF as i64));
    map
});

static OPTION_1: CommandLineOption = CommandLineOption {
    name: "help",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "h",
    show_in_simplified_help_view: true,
    is_command_line_only: true,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Print_this_message),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_2: CommandLineOption = CommandLineOption {
    name: "help",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "?",
    is_command_line_only: true,
    category: Some(&diagnostics::Command_line_Options),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_3: CommandLineOption = CommandLineOption {
    name: "watch",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "w",
    show_in_simplified_help_view: true,
    is_command_line_only: true,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Watch_input_files),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_4: CommandLineOption = CommandLineOption {
    name: "preserveWatchOutput",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: false,
    category: Some(&diagnostics::Output_Formatting),
    description: Some(&diagnostics::Disable_wiping_the_console_in_watch_mode),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_5: CommandLineOption = CommandLineOption {
    name: "listFiles",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Compiler_Diagnostics),
    description: Some(&diagnostics::Print_all_of_the_files_read_during_the_compilation),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_6: CommandLineOption = CommandLineOption {
    name: "explainFiles",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Compiler_Diagnostics),
    description: Some(
        &diagnostics::Print_files_read_during_the_compilation_including_why_it_was_included,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_7: CommandLineOption = CommandLineOption {
    name: "listEmittedFiles",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Compiler_Diagnostics),
    description: Some(&diagnostics::Print_the_names_of_emitted_files_after_a_compilation),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_8: CommandLineOption = CommandLineOption {
        name: "pretty",
        kind: CommandLineOptionKind::BOOLEAN,
        show_in_simplified_help_view: true,
        category: Some(&diagnostics::Output_Formatting),
        description: Some(&diagnostics::Enable_color_and_formatting_in_TypeScript_s_output_to_make_compiler_errors_easier_to_read),
        default_value_description: DefaultValueDescription::Bool(true),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_9: CommandLineOption = CommandLineOption {
    name: "traceResolution",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Compiler_Diagnostics),
    description: Some(&diagnostics::Log_paths_used_during_the_moduleResolution_process),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_10: CommandLineOption = CommandLineOption {
    name: "diagnostics",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Compiler_Diagnostics),
    description: Some(&diagnostics::Output_compiler_performance_information_after_building),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_11: CommandLineOption = CommandLineOption {
    name: "extendedDiagnostics",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Compiler_Diagnostics),
    description: Some(
        &diagnostics::Output_more_detailed_compiler_performance_information_after_building,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_12: CommandLineOption = CommandLineOption {
    name: "generateCpuProfile",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::File,
    is_file_path: true,
    category: Some(&diagnostics::Compiler_Diagnostics),
    description: Some(&diagnostics::Emit_a_v8_CPU_profile_of_the_compiler_run_for_debugging),
    default_value_description: DefaultValueDescription::Str("profile.cpuprofile"),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_13: CommandLineOption = CommandLineOption {
    name: "generateTrace",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::Directory,
    is_file_path: true,
    category: Some(&diagnostics::Compiler_Diagnostics),
    description: Some(&diagnostics::Generates_an_event_trace_and_a_list_of_types),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_14: CommandLineOption = CommandLineOption {
    name: "incremental",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "i",
    category: Some(&diagnostics::Projects),
    description: Some(
        &diagnostics::Save_tsbuildinfo_files_to_allow_for_incremental_compilation_of_projects,
    ),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_false_unless_composite_is_set,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_15: CommandLineOption = CommandLineOption {
    name: "declaration",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "d",
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Emit),
    description: Some(
        &diagnostics::Generate_d_ts_files_from_TypeScript_and_JavaScript_files_in_your_project,
    ),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_false_unless_composite_is_set,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_16: CommandLineOption = CommandLineOption {
    name: "declarationMap",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Emit),
    default_value_description: DefaultValueDescription::Bool(false),
    description: Some(&diagnostics::Create_sourcemaps_for_d_ts_files),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_17: CommandLineOption = CommandLineOption {
    name: "emitDeclarationOnly",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Emit),
    description: Some(&diagnostics::Only_output_d_ts_files_and_not_JavaScript_files),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_18: CommandLineOption = CommandLineOption {
    name: "sourceMap",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Emit),
    default_value_description: DefaultValueDescription::Bool(false),
    description: Some(&diagnostics::Create_source_map_files_for_emitted_JavaScript_files),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_19: CommandLineOption = CommandLineOption {
    name: "inlineSourceMap",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Emit),
    description: Some(&diagnostics::Include_sourcemap_files_inside_the_emitted_JavaScript),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_20: CommandLineOption = CommandLineOption {
        name: "noCheck",
        kind: CommandLineOptionKind::BOOLEAN,
        show_in_simplified_help_view: false,
        category: Some(&diagnostics::Compiler_Diagnostics),
        description: Some(&diagnostics::Disable_full_type_checking_only_critical_parse_and_emit_errors_will_be_reported),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_21: CommandLineOption = CommandLineOption {
    name: "deduplicatePackages",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Deduplicate_packages_with_the_same_name_and_version),
    default_value_description: DefaultValueDescription::Bool(true),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_22: CommandLineOption = CommandLineOption {
    name: "noEmit",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Emit),
    description: Some(&diagnostics::Disable_emitting_files_from_a_compilation),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_23: CommandLineOption = CommandLineOption {
        name: "assumeChangesOnlyAffectDirectDependencies",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Watch_and_Build_Modes),
        description: Some(&diagnostics::Have_recompiles_in_projects_that_use_incremental_and_watch_mode_assume_that_changes_within_a_file_will_only_affect_files_directly_depending_on_it),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_24: CommandLineOption = CommandLineOption {
    name: "locale",
    kind: CommandLineOptionKind::STRING,
    category: Some(&diagnostics::Command_line_Options),
    is_command_line_only: true,
    description: Some(
        &diagnostics::Set_the_language_of_the_messaging_from_TypeScript_This_does_not_affect_emit,
    ),
    default_value_description: DefaultValueDescription::Message(&diagnostics::Platform_specific),
    extra_validation: Some(EXTRA_VALIDATION_LOCALE),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_25: CommandLineOption = CommandLineOption {
    name: "quiet",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "q",
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Do_not_print_diagnostics),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_26: CommandLineOption = CommandLineOption {
    name: "singleThreaded",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Run_in_single_threaded_mode),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_27: CommandLineOption = CommandLineOption {
    name: "pprofDir",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::Directory,
    is_file_path: true,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Generate_pprof_CPU_Slashmemory_profiles_to_the_given_directory),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_28: CommandLineOption = CommandLineOption {
    name: "checkers",
    kind: CommandLineOptionKind::NUMBER,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Set_the_number_of_checkers_per_project),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_4_unless_singleThreaded_is_passed,
    ),
    min_value: 1,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_29: CommandLineOption = CommandLineOption {
        name: "runExternalCode",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Command_line_Options),
        is_command_line_only: true,
        description: Some(&diagnostics::Allow_loading_external_content_mapper_plugins_that_execute_code_during_compilation),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_30: CommandLineOption = CommandLineOption {
    name: "all",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Show_all_compiler_options),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_31: CommandLineOption = CommandLineOption {
    name: "version",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "v",
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Print_the_compiler_s_version),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_32: CommandLineOption = CommandLineOption {
    name: "init",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(
        &diagnostics::Initializes_a_TypeScript_project_and_creates_a_tsconfig_json_file,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_33: CommandLineOption = CommandLineOption {
        name: "project",
        kind: CommandLineOptionKind::STRING,
        path_kind: CommandLineOptionPathKind::FileOrDirectory,
        short_name: "p",
        is_file_path: true,
        show_in_simplified_help_view: true,
        category: Some(&diagnostics::Command_line_Options),
        description: Some(&diagnostics::Compile_the_project_given_the_path_to_its_configuration_file_or_to_a_folder_with_a_tsconfig_json),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_34: CommandLineOption = CommandLineOption {
    name: "showConfig",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Command_line_Options),
    is_command_line_only: true,
    description: Some(&diagnostics::Print_the_final_configuration_instead_of_building),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_35: CommandLineOption = CommandLineOption {
        name: "listFilesOnly",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Command_line_Options),
        is_command_line_only: true,
        description: Some(&diagnostics::Print_names_of_files_that_are_part_of_the_compilation_and_then_stop_processing),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_36: CommandLineOption = CommandLineOption {
    name: "ignoreConfig",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Command_line_Options),
    is_command_line_only: true,
    description: Some(
        &diagnostics::Ignore_the_tsconfig_found_and_build_with_commandline_options_and_files,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_37: CommandLineOption = CommandLineOption {
        name: "target",
        kind: CommandLineOptionKind::ENUM,
        short_name: "t",
        show_in_simplified_help_view: true,
        category: Some(&diagnostics::Language_and_Environment),
        description: Some(&diagnostics::Set_the_JavaScript_language_version_for_emitted_JavaScript_and_include_compatible_library_declarations),
        default_value_description: DefaultValueDescription::ScriptTarget(ScriptTarget::LATEST_STANDARD),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_38: CommandLineOption = CommandLineOption {
    name: "module",
    kind: CommandLineOptionKind::ENUM,
    short_name: "m",
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Modules),
    description: Some(&diagnostics::Specify_what_module_code_is_generated),
    default_value_description: DefaultValueDescription::Tristate(TS_UNKNOWN),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_39: CommandLineOption = CommandLineOption {
        name: "lib",
        kind: CommandLineOptionKind::LIST,
        show_in_simplified_help_view: true,
        category: Some(&diagnostics::Language_and_Environment),
        description: Some(&diagnostics::Specify_a_set_of_bundled_library_declaration_files_that_describe_the_target_runtime_environment),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_40: CommandLineOption = CommandLineOption {
        name: "allowJs",
        kind: CommandLineOptionKind::BOOLEAN,
        show_in_simplified_help_view: true,
        category: Some(&diagnostics::JavaScript_Support),
        description: Some(&diagnostics::Allow_JavaScript_files_to_be_a_part_of_your_program_Use_the_checkJs_option_to_get_errors_from_these_files),
        default_value_description: DefaultValueDescription::Message(&diagnostics::X_false_unless_checkJs_is_set),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_41: CommandLineOption = CommandLineOption {
    name: "checkJs",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::JavaScript_Support),
    description: Some(&diagnostics::Enable_error_reporting_in_type_checked_JavaScript_files),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_42: CommandLineOption = CommandLineOption {
    name: "jsx",
    kind: CommandLineOptionKind::ENUM,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Language_and_Environment),
    description: Some(&diagnostics::Specify_what_JSX_code_is_generated),
    default_value_description: DefaultValueDescription::Tristate(TS_UNKNOWN),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_43: CommandLineOption = CommandLineOption {
        name: "outFile",
        kind: CommandLineOptionKind::STRING,
        path_kind: CommandLineOptionPathKind::File,
        is_file_path: true,
        show_in_simplified_help_view: true,
        category: Some(&diagnostics::Emit),
        description: Some(&diagnostics::Specify_a_file_that_bundles_all_outputs_into_one_JavaScript_file_If_declaration_is_true_also_designates_a_file_that_bundles_all_d_ts_output),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_44: CommandLineOption = CommandLineOption {
    name: "outDir",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::Directory,
    is_file_path: true,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Emit),
    description: Some(&diagnostics::Specify_an_output_folder_for_all_emitted_files),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_45: CommandLineOption = CommandLineOption {
    name: "rootDir",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::Directory,
    is_file_path: true,
    category: Some(&diagnostics::Modules),
    description: Some(&diagnostics::Specify_the_root_folder_within_your_source_files),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::Computed_from_the_list_of_input_files,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_46: CommandLineOption = CommandLineOption {
        name: "composite",
        kind: CommandLineOptionKind::BOOLEAN,
        is_ts_config_only: true,
        category: Some(&diagnostics::Projects),
        default_value_description: DefaultValueDescription::Bool(false),
        description: Some(&diagnostics::Enable_constraints_that_allow_a_TypeScript_project_to_be_used_with_project_references),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_47: CommandLineOption = CommandLineOption {
    name: "tsBuildInfoFile",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::File,
    is_file_path: true,
    category: Some(&diagnostics::Projects),
    default_value_description: DefaultValueDescription::Str(".tsbuildinfo"),
    description: Some(&diagnostics::Specify_the_path_to_tsbuildinfo_incremental_compilation_file),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_48: CommandLineOption = CommandLineOption {
    name: "removeComments",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Emit),
    default_value_description: DefaultValueDescription::Bool(false),
    description: Some(&diagnostics::Disable_emitting_comments),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_49: CommandLineOption = CommandLineOption {
        name: "importHelpers",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Emit),
        description: Some(&diagnostics::Allow_importing_helper_functions_from_tslib_once_per_project_instead_of_including_them_per_file),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_50: CommandLineOption = CommandLineOption {
    name: "downlevelIteration",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Emit),
    description: Some(
        &diagnostics::Emit_more_compliant_but_verbose_and_less_performant_JavaScript_for_iteration,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_51: CommandLineOption = CommandLineOption {
        name: "isolatedModules",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Interop_Constraints),
        description: Some(&diagnostics::Ensure_that_each_file_can_be_safely_transpiled_without_relying_on_other_imports),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_52: CommandLineOption = CommandLineOption {
        name: "verbatimModuleSyntax",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Interop_Constraints),
        description: Some(&diagnostics::Do_not_transform_or_elide_any_imports_or_exports_not_marked_as_type_only_ensuring_they_are_written_in_the_output_file_s_format_based_on_the_module_setting),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_53: CommandLineOption = CommandLineOption {
        name: "isolatedDeclarations",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Interop_Constraints),
        description: Some(&diagnostics::Require_sufficient_annotation_on_exports_so_other_tools_can_trivially_generate_declaration_files),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_54: CommandLineOption = CommandLineOption {
    name: "erasableSyntaxOnly",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Interop_Constraints),
    description: Some(
        &diagnostics::Do_not_allow_runtime_constructs_that_are_not_part_of_ECMAScript,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_55: CommandLineOption = CommandLineOption {
    name: "libReplacement",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Language_and_Environment),
    description: Some(&diagnostics::Enable_lib_replacement),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_56: CommandLineOption = CommandLineOption {
    name: "strict",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Enable_all_strict_type_checking_options),
    default_value_description: DefaultValueDescription::Bool(true),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_57: CommandLineOption = CommandLineOption {
        name: "noImplicitAny",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Type_Checking),
        description: Some(&diagnostics::Enable_error_reporting_for_expressions_and_declarations_with_an_implied_any_type),
        default_value_description: DefaultValueDescription::Message(&diagnostics::X_true_unless_strict_is_false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_58: CommandLineOption = CommandLineOption {
    name: "strictNullChecks",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::When_type_checking_take_into_account_null_and_undefined),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_true_unless_strict_is_false,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_59: CommandLineOption = CommandLineOption {
        name: "strictFunctionTypes",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Type_Checking),
        description: Some(&diagnostics::When_assigning_functions_check_to_ensure_parameters_and_the_return_values_are_subtype_compatible),
        default_value_description: DefaultValueDescription::Message(&diagnostics::X_true_unless_strict_is_false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_60: CommandLineOption = CommandLineOption {
        name: "strictBindCallApply",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Type_Checking),
        description: Some(&diagnostics::Check_that_the_arguments_for_bind_call_and_apply_methods_match_the_original_function),
        default_value_description: DefaultValueDescription::Message(&diagnostics::X_true_unless_strict_is_false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_61: CommandLineOption = CommandLineOption {
    name: "strictPropertyInitialization",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(
        &diagnostics::Check_for_class_properties_that_are_declared_but_not_set_in_the_constructor,
    ),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_true_unless_strict_is_false,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_62: CommandLineOption = CommandLineOption {
        name: "strictBuiltinIteratorReturn",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Type_Checking),
        description: Some(&diagnostics::Built_in_iterators_are_instantiated_with_a_TReturn_type_of_undefined_instead_of_any),
        default_value_description: DefaultValueDescription::Message(&diagnostics::X_true_unless_strict_is_false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_63: CommandLineOption = CommandLineOption {
    name: "noImplicitThis",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Enable_error_reporting_when_this_is_given_the_type_any),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_true_unless_strict_is_false,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_64: CommandLineOption = CommandLineOption {
    name: "useUnknownInCatchVariables",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Default_catch_clause_variables_as_unknown_instead_of_any),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_true_unless_strict_is_false,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_65: CommandLineOption = CommandLineOption {
    name: "alwaysStrict",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Ensure_use_strict_is_always_emitted),
    default_value_description: DefaultValueDescription::Bool(true),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_66: CommandLineOption = CommandLineOption {
    name: "stableTypeOrdering",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(
        &diagnostics::Ensure_types_are_ordered_stably_and_deterministically_across_compilations,
    ),
    default_value_description: DefaultValueDescription::Bool(true),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_67: CommandLineOption = CommandLineOption {
    name: "noUnusedLocals",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Enable_error_reporting_when_local_variables_aren_t_read),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_68: CommandLineOption = CommandLineOption {
    name: "noUnusedParameters",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Raise_an_error_when_a_function_parameter_isn_t_read),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_69: CommandLineOption = CommandLineOption {
    name: "exactOptionalPropertyTypes",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(
        &diagnostics::Interpret_optional_property_types_as_written_rather_than_adding_undefined,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_70: CommandLineOption = CommandLineOption {
        name: "noImplicitReturns",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Type_Checking),
        description: Some(&diagnostics::Enable_error_reporting_for_codepaths_that_do_not_explicitly_return_in_a_function),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_71: CommandLineOption = CommandLineOption {
    name: "noFallthroughCasesInSwitch",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(
        &diagnostics::Enable_error_reporting_for_fallthrough_cases_in_switch_statements,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_72: CommandLineOption = CommandLineOption {
    name: "noUncheckedIndexedAccess",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Add_undefined_to_a_type_when_accessed_using_an_index),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_73: CommandLineOption = CommandLineOption {
        name: "noImplicitOverride",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Type_Checking),
        description: Some(&diagnostics::Ensure_overriding_members_in_derived_classes_are_marked_with_an_override_modifier),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_74: CommandLineOption = CommandLineOption {
    name: "noPropertyAccessFromIndexSignature",
    kind: CommandLineOptionKind::BOOLEAN,
    show_in_simplified_help_view: false,
    category: Some(&diagnostics::Type_Checking),
    description: Some(
        &diagnostics::Enforces_using_indexed_accessors_for_keys_declared_using_an_indexed_type,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_75: CommandLineOption = CommandLineOption {
        name: "moduleResolution",
        kind: CommandLineOptionKind::ENUM,
        category: Some(&diagnostics::Modules),
        description: Some(&diagnostics::Specify_how_TypeScript_looks_up_a_file_from_a_given_module_specifier),
        default_value_description: DefaultValueDescription::Message(&diagnostics::X_nodenext_if_module_is_nodenext_node16_if_module_is_node16_or_node18_otherwise_bundler),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_76: CommandLineOption = CommandLineOption {
    name: "baseUrl",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::Directory,
    is_file_path: true,
    category: Some(&diagnostics::Modules),
    description: Some(
        &diagnostics::Specify_the_base_directory_to_resolve_non_relative_module_names,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_77: CommandLineOption = CommandLineOption {
    name: "paths",
    kind: CommandLineOptionKind::OBJECT,
    is_ts_config_only: true,
    category: Some(&diagnostics::Modules),
    description: Some(
        &diagnostics::Specify_a_set_of_entries_that_re_map_imports_to_additional_lookup_locations,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_78: CommandLineOption = CommandLineOption {
    name: "rootDirs",
    kind: CommandLineOptionKind::LIST,
    is_ts_config_only: true,
    category: Some(&diagnostics::Modules),
    description: Some(
        &diagnostics::Allow_multiple_folders_to_be_treated_as_one_when_resolving_modules,
    ),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::Computed_from_the_list_of_input_files,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_79: CommandLineOption = CommandLineOption {
    name: "typeRoots",
    kind: CommandLineOptionKind::LIST,
    category: Some(&diagnostics::Modules),
    description: Some(
        &diagnostics::Specify_multiple_folders_that_act_like_Slashnode_modules_Slash_types,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_80: CommandLineOption = CommandLineOption {
        name: "types",
        kind: CommandLineOptionKind::LIST,
        show_in_simplified_help_view: true,
        category: Some(&diagnostics::Modules),
        description: Some(&diagnostics::Specify_type_package_names_to_be_included_without_being_referenced_in_a_source_file),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_81: CommandLineOption = CommandLineOption {
    name: "allowSyntheticDefaultImports",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Interop_Constraints),
    description: Some(
        &diagnostics::Allow_import_x_from_y_when_a_module_doesn_t_have_a_default_export,
    ),
    default_value_description: DefaultValueDescription::Bool(true),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_82: CommandLineOption = CommandLineOption {
        name: "esModuleInterop",
        kind: CommandLineOptionKind::BOOLEAN,
        show_in_simplified_help_view: true,
        category: Some(&diagnostics::Interop_Constraints),
        description: Some(&diagnostics::Emit_additional_JavaScript_to_ease_support_for_importing_CommonJS_modules_This_enables_allowSyntheticDefaultImports_for_type_compatibility),
        default_value_description: DefaultValueDescription::Bool(true),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_83: CommandLineOption = CommandLineOption {
        name: "preserveSymlinks",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Interop_Constraints),
        description: Some(&diagnostics::Disable_resolving_symlinks_to_their_realpath_This_correlates_to_the_same_flag_in_node),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_84: CommandLineOption = CommandLineOption {
    name: "allowUmdGlobalAccess",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Modules),
    description: Some(&diagnostics::Allow_accessing_UMD_globals_from_modules),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_85: CommandLineOption = CommandLineOption {
    name: "moduleSuffixes",
    kind: CommandLineOptionKind::LIST,
    list_preserve_falsy_values: true,
    category: Some(&diagnostics::Modules),
    description: Some(&diagnostics::List_of_file_name_suffixes_to_search_when_resolving_a_module),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_86: CommandLineOption = CommandLineOption {
        name: "allowImportingTsExtensions",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Modules),
        description: Some(&diagnostics::Allow_imports_to_include_TypeScript_file_extensions_Requires_moduleResolution_bundler_and_either_noEmit_or_emitDeclarationOnly_to_be_set),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_87: CommandLineOption = CommandLineOption {
        name: "rewriteRelativeImportExtensions",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Modules),
        description: Some(&diagnostics::Rewrite_ts_tsx_mts_and_cts_file_extensions_in_relative_import_paths_to_their_JavaScript_equivalent_in_output_files),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_88: CommandLineOption = CommandLineOption {
    name: "resolvePackageJsonExports",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Modules),
    description: Some(
        &diagnostics::Use_the_package_json_exports_field_when_resolving_package_imports,
    ),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_true_when_moduleResolution_is_node16_nodenext_or_bundler_otherwise_false,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_89: CommandLineOption = CommandLineOption {
    name: "resolvePackageJsonImports",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Modules),
    description: Some(&diagnostics::Use_the_package_json_imports_field_when_resolving_imports),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_true_when_moduleResolution_is_node16_nodenext_or_bundler_otherwise_false,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_90: CommandLineOption = CommandLineOption {
        name: "customConditions",
        kind: CommandLineOptionKind::LIST,
        category: Some(&diagnostics::Modules),
        description: Some(&diagnostics::Conditions_to_set_in_addition_to_the_resolver_specific_defaults_when_resolving_imports),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_91: CommandLineOption = CommandLineOption {
    name: "noUncheckedSideEffectImports",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Modules),
    description: Some(&diagnostics::Check_side_effect_imports),
    default_value_description: DefaultValueDescription::Bool(true),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_92: CommandLineOption = CommandLineOption {
    name: "sourceRoot",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::SourceMapLocation,
    category: Some(&diagnostics::Emit),
    description: Some(
        &diagnostics::Specify_the_root_path_for_debuggers_to_find_the_reference_source_code,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_93: CommandLineOption = CommandLineOption {
        name: "mapRoot",
        kind: CommandLineOptionKind::STRING,
        path_kind: CommandLineOptionPathKind::SourceMapLocation,
        category: Some(&diagnostics::Emit),
        description: Some(&diagnostics::Specify_the_location_where_debugger_should_locate_map_files_instead_of_generated_locations),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_94: CommandLineOption = CommandLineOption {
    name: "inlineSources",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Emit),
    description: Some(
        &diagnostics::Include_source_code_in_the_sourcemaps_inside_the_emitted_JavaScript,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_95: CommandLineOption = CommandLineOption {
    name: "experimentalDecorators",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Language_and_Environment),
    description: Some(&diagnostics::Enable_experimental_support_for_legacy_experimental_decorators),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_96: CommandLineOption = CommandLineOption {
    name: "emitDecoratorMetadata",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Language_and_Environment),
    description: Some(
        &diagnostics::Emit_design_type_metadata_for_decorated_declarations_in_source_files,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_97: CommandLineOption = CommandLineOption {
        name: "jsxFactory",
        kind: CommandLineOptionKind::STRING,
        category: Some(&diagnostics::Language_and_Environment),
        description: Some(&diagnostics::Specify_the_JSX_factory_function_used_when_targeting_React_JSX_emit_e_g_React_createElement_or_h),
        default_value_description: DefaultValueDescription::Str("`React.createElement`"),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_98: CommandLineOption = CommandLineOption {
        name: "jsxFragmentFactory",
        kind: CommandLineOptionKind::STRING,
        category: Some(&diagnostics::Language_and_Environment),
        description: Some(&diagnostics::Specify_the_JSX_Fragment_reference_used_for_fragments_when_targeting_React_JSX_emit_e_g_React_Fragment_or_Fragment),
        default_value_description: DefaultValueDescription::Str("React.Fragment"),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_99: CommandLineOption = CommandLineOption {
        name: "jsxImportSource",
        kind: CommandLineOptionKind::STRING,
        category: Some(&diagnostics::Language_and_Environment),
        description: Some(&diagnostics::Specify_module_specifier_used_to_import_the_JSX_factory_functions_when_using_jsx_Colon_react_jsx_Asterisk),
        default_value_description: DefaultValueDescription::Str("react"),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_100: CommandLineOption = CommandLineOption {
    name: "resolveJsonModule",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Modules),
    description: Some(&diagnostics::Enable_importing_json_files),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_101: CommandLineOption = CommandLineOption {
        name: "allowArbitraryExtensions",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Modules),
        description: Some(&diagnostics::Enable_importing_files_with_any_extension_provided_a_declaration_file_is_present),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_102: CommandLineOption = CommandLineOption {
        name: "reactNamespace",
        kind: CommandLineOptionKind::STRING,
        category: Some(&diagnostics::Language_and_Environment),
        description: Some(&diagnostics::Specify_the_object_invoked_for_createElement_This_only_applies_when_targeting_react_JSX_emit),
        default_value_description: DefaultValueDescription::Str("`React`"),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_103: CommandLineOption = CommandLineOption {
    name: "skipDefaultLibCheck",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Completeness),
    description: Some(
        &diagnostics::Skip_type_checking_d_ts_files_that_are_included_with_TypeScript,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_104: CommandLineOption = CommandLineOption {
    name: "emitBOM",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Emit),
    description: Some(
        &diagnostics::Emit_a_UTF_8_Byte_Order_Mark_BOM_in_the_beginning_of_output_files,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_105: CommandLineOption = CommandLineOption {
    name: "newLine",
    kind: CommandLineOptionKind::ENUM,
    category: Some(&diagnostics::Emit),
    description: Some(&diagnostics::Set_the_newline_character_for_emitting_files),
    default_value_description: DefaultValueDescription::Str("lf"),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_106: CommandLineOption = CommandLineOption {
    name: "noErrorTruncation",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Output_Formatting),
    description: Some(&diagnostics::Disable_truncating_types_in_error_messages),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_107: CommandLineOption = CommandLineOption {
    name: "noLib",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Language_and_Environment),
    description: Some(
        &diagnostics::Disable_including_any_library_files_including_the_default_lib_d_ts,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_108: CommandLineOption = CommandLineOption {
        name: "noResolve",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Modules),
        description: Some(&diagnostics::Disallow_import_s_require_s_or_reference_s_from_expanding_the_number_of_files_TypeScript_should_add_to_a_project),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_109: CommandLineOption = CommandLineOption {
    name: "stripInternal",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Emit),
    description: Some(
        &diagnostics::Disable_emitting_declarations_that_have_internal_in_their_JSDoc_comments,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_110: CommandLineOption = CommandLineOption {
        name: "disableSizeLimit",
        kind: CommandLineOptionKind::BOOLEAN,
        category: Some(&diagnostics::Editor_Support),
        description: Some(&diagnostics::Remove_the_20mb_cap_on_total_source_code_size_for_JavaScript_files_in_the_TypeScript_language_server),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_111: CommandLineOption = CommandLineOption {
        name: "disableSourceOfProjectReferenceRedirect",
        kind: CommandLineOptionKind::BOOLEAN,
        is_ts_config_only: true,
        category: Some(&diagnostics::Projects),
        description: Some(&diagnostics::Disable_preferring_source_files_instead_of_declaration_files_when_referencing_composite_projects),
        default_value_description: DefaultValueDescription::Bool(false),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_112: CommandLineOption = CommandLineOption {
    name: "disableSolutionSearching",
    kind: CommandLineOptionKind::BOOLEAN,
    is_ts_config_only: true,
    category: Some(&diagnostics::Projects),
    description: Some(
        &diagnostics::Opt_a_project_out_of_multi_project_reference_checking_when_editing,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_113: CommandLineOption = CommandLineOption {
    name: "disableReferencedProjectLoad",
    kind: CommandLineOptionKind::BOOLEAN,
    is_ts_config_only: true,
    category: Some(&diagnostics::Projects),
    description: Some(
        &diagnostics::Reduce_the_number_of_projects_loaded_automatically_by_TypeScript,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_114: CommandLineOption = CommandLineOption {
    name: "noEmitHelpers",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Emit),
    description: Some(
        &diagnostics::Disable_generating_custom_helper_functions_like_extends_in_compiled_output,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_115: CommandLineOption = CommandLineOption {
    name: "noEmitOnError",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Emit),
    description: Some(
        &diagnostics::Disable_emitting_files_if_any_type_checking_errors_are_reported,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_116: CommandLineOption = CommandLineOption {
    name: "preserveConstEnums",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Emit),
    description: Some(&diagnostics::Disable_erasing_const_enum_declarations_in_generated_code),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_117: CommandLineOption = CommandLineOption {
    name: "declarationDir",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::Directory,
    is_file_path: true,
    category: Some(&diagnostics::Emit),
    description: Some(&diagnostics::Specify_the_output_directory_for_generated_declaration_files),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_118: CommandLineOption = CommandLineOption {
    name: "skipLibCheck",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Completeness),
    description: Some(&diagnostics::Skip_type_checking_all_d_ts_files),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_119: CommandLineOption = CommandLineOption {
    name: "allowUnusedLabels",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Disable_error_reporting_for_unused_labels),
    default_value_description: DefaultValueDescription::Tristate(TS_UNKNOWN),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_120: CommandLineOption = CommandLineOption {
    name: "allowUnreachableCode",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Type_Checking),
    description: Some(&diagnostics::Disable_error_reporting_for_unreachable_code),
    default_value_description: DefaultValueDescription::Tristate(TS_UNKNOWN),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_121: CommandLineOption = CommandLineOption {
    name: "forceConsistentCasingInFileNames",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Interop_Constraints),
    description: Some(&diagnostics::Ensure_that_casing_is_correct_in_imports),
    default_value_description: DefaultValueDescription::Bool(true),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_122: CommandLineOption = CommandLineOption {
        name: "maxNodeModuleJsDepth",
        kind: CommandLineOptionKind::NUMBER,
        category: Some(&diagnostics::JavaScript_Support),
        description: Some(&diagnostics::Specify_the_maximum_folder_depth_used_for_checking_JavaScript_files_from_node_modules_Only_applicable_with_allowJs),
        default_value_description: DefaultValueDescription::Number(0),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_123: CommandLineOption = CommandLineOption {
    name: "useDefineForClassFields",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Language_and_Environment),
    description: Some(&diagnostics::Emit_ECMAScript_standard_compliant_class_fields),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_true_for_ES2022_and_above_including_ESNext,
    ),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_124: CommandLineOption = CommandLineOption {
    name: "plugins",
    kind: CommandLineOptionKind::LIST,
    is_ts_config_only: true,
    description: Some(&diagnostics::Specify_a_list_of_language_service_plugins_to_include),
    category: Some(&diagnostics::Editor_Support),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_125: CommandLineOption = CommandLineOption {
        name: "moduleDetection",
        kind: CommandLineOptionKind::ENUM,
        description: Some(&diagnostics::Control_what_method_is_used_to_detect_module_format_JS_files),
        category: Some(&diagnostics::Language_and_Environment),
        default_value_description: DefaultValueDescription::Message(&diagnostics::X_auto_Colon_Treat_files_with_imports_exports_import_meta_jsx_with_jsx_Colon_react_jsx_or_esm_format_with_module_Colon_node16_as_modules),
        ..DEFAULT_COMMAND_LINE_OPTION
    };
static OPTION_126: CommandLineOption = CommandLineOption {
    name: "ignoreDeprecations",
    kind: CommandLineOptionKind::STRING,
    default_value_description: DefaultValueDescription::Tristate(TS_UNKNOWN),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_127: CommandLineOption = CommandLineOption {
    name: "enable",
    kind: CommandLineOptionKind::BOOLEAN,
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_128: CommandLineOption = CommandLineOption {
    name: "include",
    kind: CommandLineOptionKind::LIST,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_129: CommandLineOption = CommandLineOption {
    name: "exclude",
    kind: CommandLineOptionKind::LIST,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_130: CommandLineOption = CommandLineOption {
    name: "disableFilenameBasedTypeAcquisition",
    kind: CommandLineOptionKind::BOOLEAN,
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_131: CommandLineOption = CommandLineOption {
    name: "lib",
    kind: CommandLineOptionKind::ENUM,
    default_value_description: DefaultValueDescription::Tristate(TS_UNKNOWN),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_132: CommandLineOption = CommandLineOption {
    name: "rootDirs",
    kind: CommandLineOptionKind::STRING,
    is_file_path: true,
    path_kind: CommandLineOptionPathKind::Directory,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_133: CommandLineOption = CommandLineOption {
    name: "typeRoots",
    kind: CommandLineOptionKind::STRING,
    is_file_path: true,
    path_kind: CommandLineOptionPathKind::Directory,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_134: CommandLineOption = CommandLineOption {
    name: "types",
    kind: CommandLineOptionKind::STRING,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_135: CommandLineOption = CommandLineOption {
    name: "moduleSuffixes",
    kind: CommandLineOptionKind::STRING,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_136: CommandLineOption = CommandLineOption {
    name: "condition",
    kind: CommandLineOptionKind::STRING,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_137: CommandLineOption = CommandLineOption {
    name: "plugin",
    kind: CommandLineOptionKind::OBJECT,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_138: CommandLineOption = CommandLineOption {
    name: "references",
    kind: CommandLineOptionKind::OBJECT,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_139: CommandLineOption = CommandLineOption {
    name: "contentMappers",
    kind: CommandLineOptionKind::OBJECT,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_140: CommandLineOption = CommandLineOption {
    name: "files",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::FileSpec,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_141: CommandLineOption = CommandLineOption {
    name: "include",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::PathPattern,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_142: CommandLineOption = CommandLineOption {
    name: "exclude",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::PathPattern,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_143: CommandLineOption = CommandLineOption {
    name: "extends",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::ConfigLocator,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_144: CommandLineOption = CommandLineOption {
    name: "libFiles",
    kind: CommandLineOptionKind::STRING,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_145: CommandLineOption = CommandLineOption {
    name: "verbose",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "v",
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Enable_verbose_logging),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_146: CommandLineOption = CommandLineOption {
    name: "dry",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "d",
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Show_what_would_be_built_or_deleted_if_specified_with_clean),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_147: CommandLineOption = CommandLineOption {
    name: "force",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "f",
    category: Some(&diagnostics::Command_line_Options),
    description: Some(
        &diagnostics::Build_all_projects_including_those_that_appear_to_be_up_to_date,
    ),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_148: CommandLineOption = CommandLineOption {
    name: "clean",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Delete_the_outputs_of_all_projects),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_149: CommandLineOption = CommandLineOption {
    name: "builders",
    kind: CommandLineOptionKind::NUMBER,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Set_the_number_of_projects_to_build_concurrently),
    default_value_description: DefaultValueDescription::Message(
        &diagnostics::X_4_unless_singleThreaded_is_passed,
    ),
    min_value: 1,
    ..DEFAULT_COMMAND_LINE_OPTION
};
static OPTION_150: CommandLineOption = CommandLineOption {
    name: "stopBuildOnErrors",
    kind: CommandLineOptionKind::BOOLEAN,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Skip_building_downstream_projects_on_error_in_upstream_project),
    default_value_description: DefaultValueDescription::Bool(false),
    ..DEFAULT_COMMAND_LINE_OPTION
};

pub static COMMON_OPTIONS_WITH_BUILD: &[&CommandLineOption] = &[
    &OPTION_1, &OPTION_2, &OPTION_3, &OPTION_4, &OPTION_5, &OPTION_6, &OPTION_7, &OPTION_8,
    &OPTION_9, &OPTION_10, &OPTION_11, &OPTION_12, &OPTION_13, &OPTION_14, &OPTION_15, &OPTION_16,
    &OPTION_17, &OPTION_18, &OPTION_19, &OPTION_20, &OPTION_21, &OPTION_22, &OPTION_23, &OPTION_24,
    &OPTION_25, &OPTION_26, &OPTION_27, &OPTION_28, &OPTION_29,
];

pub static OPTIONS_DECLARATIONS: &[&CommandLineOption] = &[
    &OPTION_30,
    &OPTION_31,
    &OPTION_32,
    &OPTION_33,
    &OPTION_34,
    &OPTION_35,
    &OPTION_36,
    &OPTION_37,
    &OPTION_38,
    &OPTION_39,
    &OPTION_40,
    &OPTION_41,
    &OPTION_42,
    &OPTION_43,
    &OPTION_44,
    &OPTION_45,
    &OPTION_46,
    &OPTION_47,
    &OPTION_48,
    &OPTION_49,
    &OPTION_50,
    &OPTION_51,
    &OPTION_52,
    &OPTION_53,
    &OPTION_54,
    &OPTION_55,
    &OPTION_56,
    &OPTION_57,
    &OPTION_58,
    &OPTION_59,
    &OPTION_60,
    &OPTION_61,
    &OPTION_62,
    &OPTION_63,
    &OPTION_64,
    &OPTION_65,
    &OPTION_66,
    &OPTION_67,
    &OPTION_68,
    &OPTION_69,
    &OPTION_70,
    &OPTION_71,
    &OPTION_72,
    &OPTION_73,
    &OPTION_74,
    &OPTION_75,
    &OPTION_76,
    &OPTION_77,
    &OPTION_78,
    &OPTION_79,
    &OPTION_80,
    &OPTION_81,
    &OPTION_82,
    &OPTION_83,
    &OPTION_84,
    &OPTION_85,
    &OPTION_86,
    &OPTION_87,
    &OPTION_88,
    &OPTION_89,
    &OPTION_90,
    &OPTION_91,
    &OPTION_92,
    &OPTION_93,
    &OPTION_94,
    &OPTION_95,
    &OPTION_96,
    &OPTION_97,
    &OPTION_98,
    &OPTION_99,
    &OPTION_100,
    &OPTION_101,
    &OPTION_102,
    &OPTION_103,
    &OPTION_104,
    &OPTION_105,
    &OPTION_106,
    &OPTION_107,
    &OPTION_108,
    &OPTION_109,
    &OPTION_110,
    &OPTION_111,
    &OPTION_112,
    &OPTION_113,
    &OPTION_114,
    &OPTION_115,
    &OPTION_116,
    &OPTION_117,
    &OPTION_118,
    &OPTION_119,
    &OPTION_120,
    &OPTION_121,
    &OPTION_122,
    &OPTION_123,
    &OPTION_124,
    &OPTION_125,
    &OPTION_126,
];

pub static TYPE_ACQUISITION_DECLS: &[&CommandLineOption] =
    &[&OPTION_127, &OPTION_128, &OPTION_129, &OPTION_130];

static COMMAND_LINE_OPTION_ELEMENTS: &[(&str, &CommandLineOption)] = &[
    ("lib", &OPTION_131),
    ("rootDirs", &OPTION_132),
    ("typeRoots", &OPTION_133),
    ("types", &OPTION_134),
    ("moduleSuffixes", &OPTION_135),
    ("customConditions", &OPTION_136),
    ("plugins", &OPTION_137),
    ("references", &OPTION_138),
    ("contentMappers", &OPTION_139),
    ("files", &OPTION_140),
    ("include", &OPTION_141),
    ("exclude", &OPTION_142),
    ("extends", &OPTION_143),
    ("libFiles", &OPTION_144),
];

pub static OPTIONS_FOR_BUILD: &[&CommandLineOption] = &[
    &TSC_BUILD_OPTION,
    &OPTION_145,
    &OPTION_146,
    &OPTION_147,
    &OPTION_148,
    &OPTION_149,
    &OPTION_150,
];

// --- handwritten glue -----------------------------------------------------

/// `var OptionsDeclarations = slices.Concat(commonOptionsWithBuild, optionsForCompiler)`.
pub fn options_declarations() -> impl Iterator<Item = CommandLineOptionRef> + 'static {
    COMMON_OPTIONS_WITH_BUILD
        .iter()
        .copied()
        .chain(OPTIONS_DECLARATIONS.iter().copied())
}

/// `var BuildOpts = slices.Concat(commonOptionsWithBuild, OptionsForBuild)`.
pub fn build_opts() -> impl Iterator<Item = CommandLineOptionRef> + 'static {
    COMMON_OPTIONS_WITH_BUILD
        .iter()
        .copied()
        .chain(OPTIONS_FOR_BUILD.iter().copied())
}

/// `TscBuildOption`.
pub fn tsc_build_option() -> CommandLineOptionRef {
    &TSC_BUILD_OPTION
}

/// `compilerOptionsDeclaration`.
pub fn compiler_options_declaration() -> CommandLineOptionRef {
    &COMPILER_OPTIONS_DECLARATION
}

/// `typeAcquisitionDeclaration`.
pub fn type_acquisition_declaration() -> CommandLineOptionRef {
    &TYPE_ACQUISITION_DECLARATION
}

/// `extendsOptionDeclaration`.
pub fn extends_option_declaration() -> CommandLineOptionRef {
    &EXTENDS_OPTION_DECLARATION
}

/// `compileOnSaveCommandLineOption`.
pub fn compile_on_save_command_line_option() -> CommandLineOptionRef {
    &COMPILE_ON_SAVE_COMMAND_LINE_OPTION
}

/// `tsconfigRootOptionsMap`.
pub fn tsconfig_root_options_map() -> CommandLineOptionRef {
    &TSCONFIG_ROOT_OPTIONS_MAP
}

/// Element option of `ElementOptions::Extends`: the anonymous
/// `{Name: "extends", Kind: string, PathKind: configLocator}` member.
static EXTENDS_ELEMENT: CommandLineOption = CommandLineOption {
    name: "extends",
    kind: CommandLineOptionKind::STRING,
    path_kind: CommandLineOptionPathKind::ConfigLocator,
    ..DEFAULT_COMMAND_LINE_OPTION
};

static REFERENCES_ELEMENT: CommandLineOption = CommandLineOption {
    name: "references",
    kind: CommandLineOptionKind::LIST,
    ..DEFAULT_COMMAND_LINE_OPTION
};

static CONTENT_MAPPERS_ELEMENT: CommandLineOption = CommandLineOption {
    name: "contentMappers",
    kind: CommandLineOptionKind::LIST,
    ..DEFAULT_COMMAND_LINE_OPTION
};

static FILES_ELEMENT: CommandLineOption = CommandLineOption {
    name: "files",
    kind: CommandLineOptionKind::LIST,
    ..DEFAULT_COMMAND_LINE_OPTION
};

static INCLUDE_ELEMENT: CommandLineOption = CommandLineOption {
    name: "include",
    kind: CommandLineOptionKind::LIST,
    ..DEFAULT_COMMAND_LINE_OPTION
};

static EXCLUDE_ELEMENT: CommandLineOption = CommandLineOption {
    name: "exclude",
    kind: CommandLineOptionKind::LIST,
    ..DEFAULT_COMMAND_LINE_OPTION
};

/// `var commandLineOptionEnumMap = map[string]*OrderedMap[string, any]{...}`.
pub fn command_line_option_enum_map(name: &str) -> Option<&'static OrderedMap<String, Value>> {
    match name {
        "lib" => Some(&LIB_MAP),
        "moduleResolution" => Some(&MODULE_RESOLUTION_OPTION_MAP),
        "module" => Some(&MODULE_OPTION_MAP),
        "target" => Some(&TARGET_OPTION_MAP),
        "moduleDetection" => Some(&MODULE_DETECTION_OPTION_MAP),
        "jsx" => Some(&JSX_OPTION_MAP),
        "newLine" => Some(&NEW_LINE_OPTION_MAP),
        _ => None,
    }
}

static MODULE_RESOLUTION_DEPRECATED: LazyLock<Set<String>> = LazyLock::new(|| {
    tsc_collections::new_set_from_items(["node", "classic", "node10"].map(str::to_string))
});
static MODULE_DEPRECATED: LazyLock<Set<String>> = LazyLock::new(|| {
    tsc_collections::new_set_from_items(["none", "amd", "system", "umd"].map(str::to_string))
});
static TARGET_DEPRECATED: LazyLock<Set<String>> =
    LazyLock::new(|| tsc_collections::new_set_from_items(["es5"].map(str::to_string)));

/// `var commandLineOptionDeprecated = map[string]*Set[string]{...}`.
pub fn command_line_option_deprecated(name: &str) -> Option<&'static Set<String>> {
    match name {
        "moduleResolution" => Some(&MODULE_RESOLUTION_DEPRECATED),
        "module" => Some(&MODULE_DEPRECATED),
        "target" => Some(&TARGET_DEPRECATED),
        _ => None,
    }
}

/// `var commandLineOptionElements = map[string]*CommandLineOption{...}`.
pub fn command_line_option_elements(name: &str) -> Option<CommandLineOptionRef> {
    COMMAND_LINE_OPTION_ELEMENTS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, o)| *o)
}

/// `var targetToLibMap = map[core.ScriptTarget]string{...}`.
pub fn target_to_lib_map(target: ScriptTarget) -> Option<&'static str> {
    match target {
        ScriptTarget::ESNext => Some("lib.esnext.full.d.ts"),
        ScriptTarget::ES2026 => Some("lib.es2026.full.d.ts"),
        ScriptTarget::ES2025 => Some("lib.es2025.full.d.ts"),
        ScriptTarget::ES2024 => Some("lib.es2024.full.d.ts"),
        ScriptTarget::ES2023 => Some("lib.es2023.full.d.ts"),
        ScriptTarget::ES2022 => Some("lib.es2022.full.d.ts"),
        ScriptTarget::ES2021 => Some("lib.es2021.full.d.ts"),
        ScriptTarget::ES2020 => Some("lib.es2020.full.d.ts"),
        ScriptTarget::ES2019 => Some("lib.es2019.full.d.ts"),
        ScriptTarget::ES2018 => Some("lib.es2018.full.d.ts"),
        ScriptTarget::ES2017 => Some("lib.es2017.full.d.ts"),
        ScriptTarget::ES2016 => Some("lib.es2016.full.d.ts"),
        // Use lib.es6.d.ts for compatibility rather than lib.es2015.full.d.ts.
        ScriptTarget::ES2015 => Some("lib.es6.d.ts"),
        _ => None,
    }
}

/// `(o *CommandLineOption) ElementOptions` — resolves the lazily-built name
/// map selected by the `element_options` tag.
pub fn element_options(
    tag: ElementOptions,
) -> &'static crate::tsconfigparsing::CommandLineOptionNameMap {
    use crate::tsconfigparsing::command_line_options_to_map;
    match tag {
        ElementOptions::CompilerOptions => {
            crate::tsconfigparsing::command_line_compiler_options_map()
        }
        ElementOptions::TypeAcquisition => {
            static M: LazyLock<crate::tsconfigparsing::CommandLineOptionNameMap> =
                LazyLock::new(|| command_line_options_to_map(TYPE_ACQUISITION_DECLS));
            &M
        }
        ElementOptions::Extends => {
            static M: LazyLock<crate::tsconfigparsing::CommandLineOptionNameMap> =
                LazyLock::new(|| command_line_options_to_map(&[&EXTENDS_ELEMENT]));
            &M
        }
        ElementOptions::TsconfigRoot => {
            static M: LazyLock<crate::tsconfigparsing::CommandLineOptionNameMap> =
                LazyLock::new(|| {
                    command_line_options_to_map(&[
                        &COMPILER_OPTIONS_DECLARATION,
                        &TYPE_ACQUISITION_DECLARATION,
                        &EXTENDS_OPTION_DECLARATION,
                        &REFERENCES_ELEMENT,
                        &CONTENT_MAPPERS_ELEMENT,
                        &FILES_ELEMENT,
                        &INCLUDE_ELEMENT,
                        &EXCLUDE_ELEMENT,
                        &COMPILE_ON_SAVE_COMMAND_LINE_OPTION,
                    ])
                });
            &M
        }
    }
}
