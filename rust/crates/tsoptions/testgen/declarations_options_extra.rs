// var TscBuildOption
static TSC_BUILD_OPTION: CommandLineOption = CommandLineOption {
    name: "build",
    kind: CommandLineOptionKind::BOOLEAN,
    short_name: "b",
    show_in_simplified_help_view: true,
    category: Some(&diagnostics::Command_line_Options),
    description: Some(&diagnostics::Build_one_or_more_projects_and_their_dependencies_if_out_of_date),
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
    map.set("dom.iterable".to_string(), Value::Str("lib.dom.iterable.d.ts".into()));
    map.set("dom.asynciterable".to_string(), Value::Str("lib.dom.asynciterable.d.ts".into()));
    map.set("webworker".to_string(), Value::Str("lib.webworker.d.ts".into()));
    map.set("webworker.importscripts".to_string(), Value::Str("lib.webworker.importscripts.d.ts".into()));
    map.set("webworker.iterable".to_string(), Value::Str("lib.webworker.iterable.d.ts".into()));
    map.set("webworker.asynciterable".to_string(), Value::Str("lib.webworker.asynciterable.d.ts".into()));
    map.set("scripthost".to_string(), Value::Str("lib.scripthost.d.ts".into()));
    map.set("es2015.core".to_string(), Value::Str("lib.es2015.core.d.ts".into()));
    map.set("es2015.collection".to_string(), Value::Str("lib.es2015.collection.d.ts".into()));
    map.set("es2015.generator".to_string(), Value::Str("lib.es2015.generator.d.ts".into()));
    map.set("es2015.iterable".to_string(), Value::Str("lib.es2015.iterable.d.ts".into()));
    map.set("es2015.promise".to_string(), Value::Str("lib.es2015.promise.d.ts".into()));
    map.set("es2015.proxy".to_string(), Value::Str("lib.es2015.proxy.d.ts".into()));
    map.set("es2015.reflect".to_string(), Value::Str("lib.es2015.reflect.d.ts".into()));
    map.set("es2015.symbol".to_string(), Value::Str("lib.es2015.symbol.d.ts".into()));
    map.set("es2015.symbol.wellknown".to_string(), Value::Str("lib.es2015.symbol.wellknown.d.ts".into()));
    map.set("es2016.array.include".to_string(), Value::Str("lib.es2016.array.include.d.ts".into()));
    map.set("es2016.intl".to_string(), Value::Str("lib.es2016.intl.d.ts".into()));
    map.set("es2017.arraybuffer".to_string(), Value::Str("lib.es2017.arraybuffer.d.ts".into()));
    map.set("es2017.date".to_string(), Value::Str("lib.es2017.date.d.ts".into()));
    map.set("es2017.object".to_string(), Value::Str("lib.es2017.object.d.ts".into()));
    map.set("es2017.sharedmemory".to_string(), Value::Str("lib.es2017.sharedmemory.d.ts".into()));
    map.set("es2017.string".to_string(), Value::Str("lib.es2017.string.d.ts".into()));
    map.set("es2017.intl".to_string(), Value::Str("lib.es2017.intl.d.ts".into()));
    map.set("es2017.typedarrays".to_string(), Value::Str("lib.es2017.typedarrays.d.ts".into()));
    map.set("es2018.asyncgenerator".to_string(), Value::Str("lib.es2018.asyncgenerator.d.ts".into()));
    map.set("es2018.asynciterable".to_string(), Value::Str("lib.es2018.asynciterable.d.ts".into()));
    map.set("es2018.intl".to_string(), Value::Str("lib.es2018.intl.d.ts".into()));
    map.set("es2018.promise".to_string(), Value::Str("lib.es2018.promise.d.ts".into()));
    map.set("es2018.regexp".to_string(), Value::Str("lib.es2018.regexp.d.ts".into()));
    map.set("es2019.array".to_string(), Value::Str("lib.es2019.array.d.ts".into()));
    map.set("es2019.object".to_string(), Value::Str("lib.es2019.object.d.ts".into()));
    map.set("es2019.string".to_string(), Value::Str("lib.es2019.string.d.ts".into()));
    map.set("es2019.symbol".to_string(), Value::Str("lib.es2019.symbol.d.ts".into()));
    map.set("es2019.intl".to_string(), Value::Str("lib.es2019.intl.d.ts".into()));
    map.set("es2020.bigint".to_string(), Value::Str("lib.es2020.bigint.d.ts".into()));
    map.set("es2020.date".to_string(), Value::Str("lib.es2020.date.d.ts".into()));
    map.set("es2020.promise".to_string(), Value::Str("lib.es2020.promise.d.ts".into()));
    map.set("es2020.sharedmemory".to_string(), Value::Str("lib.es2020.sharedmemory.d.ts".into()));
    map.set("es2020.string".to_string(), Value::Str("lib.es2020.string.d.ts".into()));
    map.set("es2020.symbol.wellknown".to_string(), Value::Str("lib.es2020.symbol.wellknown.d.ts".into()));
    map.set("es2020.intl".to_string(), Value::Str("lib.es2020.intl.d.ts".into()));
    map.set("es2020.number".to_string(), Value::Str("lib.es2020.number.d.ts".into()));
    map.set("es2021.promise".to_string(), Value::Str("lib.es2021.promise.d.ts".into()));
    map.set("es2021.string".to_string(), Value::Str("lib.es2021.string.d.ts".into()));
    map.set("es2021.weakref".to_string(), Value::Str("lib.es2021.weakref.d.ts".into()));
    map.set("es2021.intl".to_string(), Value::Str("lib.es2021.intl.d.ts".into()));
    map.set("es2022.array".to_string(), Value::Str("lib.es2022.array.d.ts".into()));
    map.set("es2022.error".to_string(), Value::Str("lib.es2022.error.d.ts".into()));
    map.set("es2022.intl".to_string(), Value::Str("lib.es2022.intl.d.ts".into()));
    map.set("es2022.object".to_string(), Value::Str("lib.es2022.object.d.ts".into()));
    map.set("es2022.string".to_string(), Value::Str("lib.es2022.string.d.ts".into()));
    map.set("es2022.regexp".to_string(), Value::Str("lib.es2022.regexp.d.ts".into()));
    map.set("es2023.array".to_string(), Value::Str("lib.es2023.array.d.ts".into()));
    map.set("es2023.collection".to_string(), Value::Str("lib.es2023.collection.d.ts".into()));
    map.set("es2023.intl".to_string(), Value::Str("lib.es2023.intl.d.ts".into()));
    map.set("es2024.arraybuffer".to_string(), Value::Str("lib.es2024.arraybuffer.d.ts".into()));
    map.set("es2024.collection".to_string(), Value::Str("lib.es2024.collection.d.ts".into()));
    map.set("es2024.object".to_string(), Value::Str("lib.es2024.object.d.ts".into()));
    map.set("es2024.promise".to_string(), Value::Str("lib.es2024.promise.d.ts".into()));
    map.set("es2024.regexp".to_string(), Value::Str("lib.es2024.regexp.d.ts".into()));
    map.set("es2024.sharedmemory".to_string(), Value::Str("lib.es2024.sharedmemory.d.ts".into()));
    map.set("es2024.string".to_string(), Value::Str("lib.es2024.string.d.ts".into()));
    map.set("es2025.collection".to_string(), Value::Str("lib.es2025.collection.d.ts".into()));
    map.set("es2025.float16".to_string(), Value::Str("lib.es2025.float16.d.ts".into()));
    map.set("es2025.intl".to_string(), Value::Str("lib.es2025.intl.d.ts".into()));
    map.set("es2025.iterator".to_string(), Value::Str("lib.es2025.iterator.d.ts".into()));
    map.set("es2025.promise".to_string(), Value::Str("lib.es2025.promise.d.ts".into()));
    map.set("es2025.regexp".to_string(), Value::Str("lib.es2025.regexp.d.ts".into()));
    map.set("es2026.array".to_string(), Value::Str("lib.es2026.array.d.ts".into()));
    map.set("es2026.collection".to_string(), Value::Str("lib.es2026.collection.d.ts".into()));
    map.set("es2026.error".to_string(), Value::Str("lib.es2026.error.d.ts".into()));
    map.set("es2026.iterator".to_string(), Value::Str("lib.es2026.iterator.d.ts".into()));
    map.set("es2026.json".to_string(), Value::Str("lib.es2026.json.d.ts".into()));
    map.set("es2026.math".to_string(), Value::Str("lib.es2026.math.d.ts".into()));
    map.set("es2026.typedarrays".to_string(), Value::Str("lib.es2026.typedarrays.d.ts".into()));
    map.set("esnext.asynciterable".to_string(), Value::Str("lib.es2018.asynciterable.d.ts".into()));
    map.set("esnext.symbol".to_string(), Value::Str("lib.es2019.symbol.d.ts".into()));
    map.set("esnext.bigint".to_string(), Value::Str("lib.es2020.bigint.d.ts".into()));
    map.set("esnext.weakref".to_string(), Value::Str("lib.es2021.weakref.d.ts".into()));
    map.set("esnext.object".to_string(), Value::Str("lib.es2024.object.d.ts".into()));
    map.set("esnext.regexp".to_string(), Value::Str("lib.es2024.regexp.d.ts".into()));
    map.set("esnext.string".to_string(), Value::Str("lib.es2024.string.d.ts".into()));
    map.set("esnext.float16".to_string(), Value::Str("lib.es2025.float16.d.ts".into()));
    map.set("esnext.array".to_string(), Value::Str("lib.es2026.array.d.ts".into()));
    map.set("esnext.collection".to_string(), Value::Str("lib.es2026.collection.d.ts".into()));
    map.set("esnext.error".to_string(), Value::Str("lib.es2026.error.d.ts".into()));
    map.set("esnext.iterator".to_string(), Value::Str("lib.es2026.iterator.d.ts".into()));
    map.set("esnext.typedarrays".to_string(), Value::Str("lib.es2026.typedarrays.d.ts".into()));
    map.set("esnext.promise".to_string(), Value::Str("lib.esnext.promise.d.ts".into()));
    map.set("esnext.date".to_string(), Value::Str("lib.esnext.date.d.ts".into()));
    map.set("esnext.decorators".to_string(), Value::Str("lib.esnext.decorators.d.ts".into()));
    map.set("esnext.disposable".to_string(), Value::Str("lib.esnext.disposable.d.ts".into()));
    map.set("esnext.intl".to_string(), Value::Str("lib.esnext.intl.d.ts".into()));
    map.set("esnext.modulesource".to_string(), Value::Str("lib.esnext.modulesource.d.ts".into()));
    map.set("esnext.sharedmemory".to_string(), Value::Str("lib.esnext.sharedmemory.d.ts".into()));
    map.set("esnext.temporal".to_string(), Value::Str("lib.esnext.temporal.d.ts".into()));
    map.set("decorators".to_string(), Value::Str("lib.decorators.d.ts".into()));
    map.set("decorators.legacy".to_string(), Value::Str("lib.decorators.legacy.d.ts".into()));
    map
});

pub static MODULE_RESOLUTION_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(6);
    map.set("node16".to_string(), Value::Int(ModuleResolutionKind::Node16 as i64));
    map.set("nodenext".to_string(), Value::Int(ModuleResolutionKind::NodeNext as i64));
    map.set("bundler".to_string(), Value::Int(ModuleResolutionKind::Bundler as i64));
    map.set("classic".to_string(), Value::Int(ModuleResolutionKind::Classic as i64));
    map.set("node".to_string(), Value::Int(ModuleResolutionKind::Node10 as i64));
    map.set("node10".to_string(), Value::Int(ModuleResolutionKind::Node10 as i64));
    map
});

pub static MODULE_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(14);
    map.set("commonjs".to_string(), Value::Int(ModuleKind::CommonJS as i64));
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
    map.set("nodenext".to_string(), Value::Int(ModuleKind::NodeNext as i64));
    map.set("preserve".to_string(), Value::Int(ModuleKind::Preserve as i64));
    map
});

pub static TARGET_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(15);
    map.set("es5".to_string(), Value::Int(ScriptTarget::ES5 as i64));
    map.set("es6".to_string(), Value::Int(ScriptTarget::ES2015 as i64));
    map.set("es2015".to_string(), Value::Int(ScriptTarget::ES2015 as i64));
    map.set("es2016".to_string(), Value::Int(ScriptTarget::ES2016 as i64));
    map.set("es2017".to_string(), Value::Int(ScriptTarget::ES2017 as i64));
    map.set("es2018".to_string(), Value::Int(ScriptTarget::ES2018 as i64));
    map.set("es2019".to_string(), Value::Int(ScriptTarget::ES2019 as i64));
    map.set("es2020".to_string(), Value::Int(ScriptTarget::ES2020 as i64));
    map.set("es2021".to_string(), Value::Int(ScriptTarget::ES2021 as i64));
    map.set("es2022".to_string(), Value::Int(ScriptTarget::ES2022 as i64));
    map.set("es2023".to_string(), Value::Int(ScriptTarget::ES2023 as i64));
    map.set("es2024".to_string(), Value::Int(ScriptTarget::ES2024 as i64));
    map.set("es2025".to_string(), Value::Int(ScriptTarget::ES2025 as i64));
    map.set("es2026".to_string(), Value::Int(ScriptTarget::ES2026 as i64));
    map.set("esnext".to_string(), Value::Int(ScriptTarget::ESNext as i64));
    map
});

pub static MODULE_DETECTION_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(3);
    map.set("auto".to_string(), Value::Int(ModuleDetectionKind::Auto as i64));
    map.set("legacy".to_string(), Value::Int(ModuleDetectionKind::Legacy as i64));
    map.set("force".to_string(), Value::Int(ModuleDetectionKind::Force as i64));
    map
});

pub static JSX_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(5);
    map.set("preserve".to_string(), Value::Int(JsxEmit::Preserve as i64));
    map.set("react-native".to_string(), Value::Int(JsxEmit::ReactNative as i64));
    map.set("react-jsx".to_string(), Value::Int(JsxEmit::ReactJSX as i64));
    map.set("react-jsxdev".to_string(), Value::Int(JsxEmit::ReactJSXDev as i64));
    map.set("react".to_string(), Value::Int(JsxEmit::React as i64));
    map
});

pub static NEW_LINE_OPTION_MAP: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {
    let mut map = OrderedMap::with_size_hint(2);
    map.set("crlf".to_string(), Value::Int(NewLineKind::CRLF as i64));
    map.set("lf".to_string(), Value::Int(NewLineKind::LF as i64));
    map
});
