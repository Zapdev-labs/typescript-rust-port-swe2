// Ported from tsc/internal/testutil/harnessutil/harnessutil.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `testing.TB` conventions (see crate root): `t.Fatalf`/`t.Error` becomes
// `Err(Error)`, `t.Skipf` becomes `Ok(Some(reason))` verdicts the caller
// turns into an early return. `map[string]string` becomes `FxHashMap`;
// `map[*TestFile]` pointer keys become `Arc::as_ptr` identity.
//
// PORT(deferred): `createProgram` does not wrap the program in
// `incremental.NewProgram` when `options.Incremental` is set — the
// `tsc-execute` incremental port is still a skeleton. The `incremental`
// flag is still parsed into `CompilerOptions`, so tests opting in silently
// get a plain program.
// PORT(deferred): `EnumerateFiles` takes a predicate instead of a
// `*regexp.Regexp` (no `regex` dependency in this workspace).

mod recorderfs;
mod sourcemap_recorder;

pub use recorderfs::{OutputRecorderFs, RecordedOutput, new_output_recorder_fs};
pub use sourcemap_recorder::{SourceMapSpanWriter, WriterAggregator, new_source_map_span_writer};

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::rc::Rc;
use std::sync::{Arc, Mutex, OnceLock};

use rustc_hash::FxHashMap;
use tsc_ast::NodeId;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_collections::{OrderedMap, Set};
use tsc_compiler::emit_host::{EmitOptions, EmitResult};
use tsc_compiler::host::{BasicCompilerHost, CompilerHost};
use tsc_compiler::program::{
    Program, ProgramConfig, ProgramFactories, ProgramHosts, ProgramLike, ProgramOptions,
};
use tsc_contentmapper::{Mapper, ParsedSourceFile, Project, ProjectSpec};
use tsc_core::context::Context;
use tsc_core::core::get_script_kind_from_file_name;
use tsc_core::options_generated::{
    CompilerOptions, ModuleKind, ModuleResolutionKind, NewLineKind, ScriptTarget,
};
use tsc_core::scriptkind::ScriptKind;
use tsc_core::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN, Tristate};
use tsc_sourcemap::decode_mappings;
use tsc_tsoptions::commandlineoption::{
    CommandLineOption, CommandLineOptionKind, CommandLineOptionPathKind, CommandLineOptionRef,
    DefaultValueDescription,
};
use tsc_tsoptions::generated::declarations;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::value::Value;
use tsc_tsoptions::{commandlineparser, parsinghelpers};
use tsc_tspath::{self as tspath, CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::{Vfs, vfstest};

use crate::Error;

/// `const testLibFolder` — POSIX-style path to additional test libraries.
pub const TEST_LIB_FOLDER: &str = "/.lib";

/// `const FakeTSVersion`.
pub const FAKE_TS_VERSION: &str = "FakeTSVersion";

/// `type TestFile struct`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestFile {
    pub unit_name: String,
    pub content: String,
}

/// `type TestConfiguration map[string]string`.
pub type TestConfiguration = FxHashMap<String, String>;

/// `type NamedTestConfiguration struct`.
#[derive(Debug)]
pub struct NamedTestConfiguration {
    pub name: String,
    pub config: TestConfiguration,
}

/// `type HarnessOptions struct`.
#[derive(Clone, Default)]
pub struct HarnessOptions {
    pub case_sensitivity: CaseSensitivity,
    pub baseline_file: String,
    pub include_built_file: String,
    pub file_name: String,
    pub lib_files: Vec<String>,
    pub no_implicit_references: bool,
    pub current_directory: RootedDirectoryPath,
    pub symlink: String,
    pub link: String,
    pub no_types_and_symbols: bool,
    pub full_emit_paths: bool,
    pub report_diagnostics: bool,
    pub capture_suggestions: bool,
    pub typescript_version: String,
}

/// `CompileFiles`.
///
// PORT: `t.Fatalf` inside `SetOptionsFromTestConfig` panics (the pinned
// callers run under `catch_unwind`/`recover_and_fail`), so this returns the
// `*CompilationResult` directly.
pub fn compile_files(
    input_files: &[TestFile],
    other_files: &[TestFile],
    test_config: &TestConfiguration,
    tsconfig: Option<&ParsedCommandLine>,
    current_directory: &RootedDirectoryPath,
    symlinks: &FxHashMap<String, String>,
) -> CompilationResult {
    let mut compiler_options = tsconfig
        .and_then(|c| c.parsed_config.as_ref())
        .and_then(|p| p.compiler_options.clone())
        .unwrap_or_default();
    // Set default options for tests
    if compiler_options.new_line == NewLineKind::None {
        compiler_options.new_line = NewLineKind::CRLF;
    }
    if compiler_options.skip_default_lib_check == TS_UNKNOWN {
        compiler_options.skip_default_lib_check = TS_TRUE;
    }
    compiler_options.no_error_truncation = TS_TRUE;
    let mut harness_options = HarnessOptions {
        case_sensitivity: CaseSensitivity::CaseSensitive,
        current_directory: current_directory.clone(),
        ..Default::default()
    };

    // Parse harness and compiler options from the test configuration
    set_options_from_test_config(
        test_config,
        &mut compiler_options,
        &mut harness_options,
        current_directory,
        false, // allowUnknownOptions
    )
    .unwrap_or_else(|e| panic!("{e}"));

    compile_files_ex(
        input_files,
        other_files,
        &harness_options,
        compiler_options,
        current_directory,
        symlinks,
        tsconfig,
    )
}

/// `CompileFilesEx`.
///
// PORT: `compilerOptions` is moved in (Go mutates the caller's
// `*CompilerOptions` through `SetOptionsFromTestConfig`, then clones for the
// pre-emit config). `tsconfig` is `*tsoptions.ParsedCommandLine` — only the
// fields Go reads (`ParsedConfig.ContentMappers`, `ConfigFile`, `Errors`,
// `BaseDirectory`) are snapshotted, since `ParsedCommandLine` is not
// `Clone`.
pub fn compile_files_ex(
    input_files: &[TestFile],
    other_files: &[TestFile],
    harness_options: &HarnessOptions,
    compiler_options: CompilerOptions,
    current_directory: &RootedDirectoryPath,
    symlinks: &FxHashMap<String, String>,
    tsconfig: Option<&ParsedCommandLine>,
) -> CompilationResult {
    compile_files_ex_inner(
        input_files,
        other_files,
        harness_options,
        compiler_options,
        current_directory,
        symlinks,
        TsconfigSnapshot::from(tsconfig).as_ref(),
    )
}

/// The pieces of `*tsoptions.ParsedCommandLine` `CompileFilesEx` reads —
/// snapshotted so `Repeat` can recompile without aliasing the (non-`Clone`)
/// config.
#[derive(Clone, Default)]
struct TsconfigSnapshot {
    content_mappers: Vec<Arc<Mapper>>,
    config_file: Option<Arc<tsc_tsoptions::tsconfigparsing::TsConfigSourceFile>>,
    errors: Vec<DiagnosticRef>,
    base_directory: Option<RootedDirectoryPath>,
}

impl TsconfigSnapshot {
    fn from(tsconfig: Option<&ParsedCommandLine>) -> Option<TsconfigSnapshot> {
        tsconfig.map(|c| TsconfigSnapshot {
            content_mappers: c
                .parsed_config
                .as_ref()
                .map(|p| p.content_mappers.clone())
                .unwrap_or_default(),
            config_file: c.config_file.clone(),
            errors: c.errors.lock().unwrap_or_else(|e| e.into_inner()).clone(),
            base_directory: if c.base_directory().is_empty() {
                None
            } else {
                Some(c.base_directory().clone())
            },
        })
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_files_ex_inner(
    input_files: &[TestFile],
    other_files: &[TestFile],
    harness_options: &HarnessOptions,
    compiler_options: CompilerOptions,
    current_directory: &RootedDirectoryPath,
    symlinks: &FxHashMap<String, String>,
    tsconfig: Option<&TsconfigSnapshot>,
) -> CompilationResult {
    let mut program_file_names: Vec<RootedFilePath> = Vec::new();
    for file in input_files {
        let file_name = tspath::to_rooted_file_path(&file.unit_name, current_directory);
        if !file_name.extension_is(tspath::EXTENSION_JSON)
            && !file_name.extension_is(tspath::EXTENSION_TS_BUILD_INFO)
        {
            program_file_names.push(file_name);
        }
    }

    // !!! Note: lib files are not going to be in `built/local`.
    // In addition, not all files that used to be in `built/local` are going to exist.
    // Files from built\local that are requested by test "@includeBuiltFiles" to be in the context.
    // Treat them as library files, so include them in build, but not in baselines.
    // (The `harnessOptions.IncludeBuiltFile` block is commented out upstream too.)

    // Performance optimization; avoid copying in the /.lib folder if the test doesn't need it.
    let mut include_lib_dir = input_files
        .iter()
        .any(|file| file.content.contains(&format!("{TEST_LIB_FOLDER}/")));

    // Files from testdata\lib that are requested by "@libFiles"
    for lib_file in &harness_options.lib_files {
        if lib_file == "lib.d.ts" && compiler_options.no_lib != TS_TRUE {
            // We used to override lib with a custom lib.d.ts for some reason. Skip this unless it becomes necessary.
            continue;
        }
        program_file_names.push(current_directory.resolve_file(&tspath::combine_paths(
            TEST_LIB_FOLDER,
            &[lib_file.as_str()],
        )));
        include_lib_dir = true;
    }

    let content_mappers: Vec<Arc<Mapper>> = tsconfig
        .map(|t| t.content_mappers.clone())
        .unwrap_or_default();

    // Create fake FS for testing
    let mut testfs: FxHashMap<String, vfstest::TestFile> = FxHashMap::default();
    for file in input_files.iter().chain(other_files.iter()) {
        let file_name =
            tspath::get_normalized_absolute_path(&file.unit_name, current_directory).into_owned();
        testfs.insert(file_name, vfstest::TestFile::from(file.content.as_str()));
    }
    for (src, target) in symlinks {
        let src_file_name =
            tspath::get_normalized_absolute_path(src, current_directory).into_owned();
        let target_file_name =
            tspath::get_normalized_absolute_path(target, current_directory).into_owned();
        testfs.insert(src_file_name, vfstest::symlink(&target_file_name).into());
    }

    if include_lib_dir {
        for (k, v) in test_lib_folder_map().iter() {
            testfs.insert(k.clone(), v.clone());
        }
    }

    let fs: Arc<dyn Vfs> = vfstest::from_map(testfs, harness_options.case_sensitivity);
    let fs = tsc_bundled::wrap_fs(fs);
    // `fs = NewOutputRecorderFS(fs)` — the host gets the recorder (which is a
    // `Vfs`); `create_compiler_host` takes it directly.
    let recorder = new_output_recorder_fs(fs);

    // Content mappers, when trusted, are served in-process by the test mapper (see contentmappertest).
    // The host is shared by the pre- and post-emit programs and torn down when this compilation finishes.
    let ctx = Context::background();
    let content_mapper_host: Option<Arc<dyn tsc_contentmapper::Host>> =
        if compiler_options.run_external_code.is_true() && !content_mappers.is_empty() {
            Some(tsc_contentmapper::new_host(
                &ctx,
                crate::contentmappertest::new_spawner(),
                tsc_locale::DEFAULT,
            ))
        } else {
            None
        };

    let config_file = tsconfig.and_then(|t| t.config_file.clone());
    let errors: Vec<DiagnosticRef> = tsconfig.map(|t| t.errors.clone()).unwrap_or_default();
    let mut base_directory = current_directory.clone();
    if let Some(base) = tsconfig.and_then(|t| t.base_directory.clone()) {
        base_directory = base;
    }
    let mut config = tsc_tsoptions::parsedcommandline::new_parsed_command_line(
        compiler_options.clone(),
        program_file_names,
        Vec::new(),
        base_directory,
        harness_options.case_sensitivity,
    );
    config.set_content_mappers(content_mappers.clone());
    config.config_file = config_file;
    *config.errors.lock().unwrap() = errors;
    let config = Arc::new(config);

    let content_mapper_project: Option<Arc<dyn Project>> =
        content_mapper_host.as_ref().and_then(|host| {
            host.project(&ProjectSpec {
                config_file_name: config.config_name().clone(),
                mappers: config.content_mappers().to_vec(),
                compiler_options: config.compiler_options().map(|o| Arc::new(o.clone())),
            })
        });
    let host = create_compiler_host(
        recorder,
        tsc_bundled::lib_path(),
        current_directory,
        content_mapper_project,
    );
    let mut result = compile_files_with_host(&host, &config, harness_options);
    result.symlinks = symlinks.clone();
    result.trace = host.tracer_string();

    // `Repeat`.
    let input_files = input_files.to_vec();
    let other_files = other_files.to_vec();
    let harness_options_repeat = harness_options.clone();
    let compiler_options_repeat = compiler_options.clone();
    let current_directory_repeat = current_directory.clone();
    let symlinks_repeat = symlinks.clone();
    let tsconfig_repeat = tsconfig.cloned();
    result.repeat = Some(Box::new(move |test_config: TestConfiguration| {
        let mut new_harness_options = harness_options_repeat.clone();
        let mut new_compiler_options = compiler_options_repeat.clone();
        set_options_from_test_config(
            &test_config,
            &mut new_compiler_options,
            &mut new_harness_options,
            &current_directory_repeat,
            false, // allowUnknownOptions
        )
        .unwrap_or_else(|e| panic!("{e}"));
        compile_files_ex_inner(
            &input_files,
            &other_files,
            &new_harness_options,
            new_compiler_options,
            &current_directory_repeat,
            &symlinks_repeat,
            tsconfig_repeat.as_ref(),
        )
    }));

    // `defer contentMapperHost.Close()` / `contentMapperProject.Close()` —
    // the project is closed when the host is; keep host alive through the
    // compilation above.
    if let Some(host) = &content_mapper_host {
        let _ = host.close();
    }
    result
}

/// `testLibFolderMap` — `sync.OnceValue` becomes `OnceLock`.
///
// PORT: `os.DirFS`+`fs.WalkDir` becomes a recursive `std::fs::read_dir` walk;
// entries are sorted for determinism (map order is unobservable to
// `from_map` anyway).
fn test_lib_folder_map() -> &'static FxHashMap<String, vfstest::TestFile> {
    static CACHE: OnceLock<FxHashMap<String, vfstest::TestFile>> = OnceLock::new();
    CACHE.get_or_init(|| {
        fn walk(dir: &std::path::Path, rel: &str, out: &mut FxHashMap<String, vfstest::TestFile>) {
            let mut entries: Vec<_> = std::fs::read_dir(dir)
                .and_then(|r| r.collect::<Result<Vec<_>, _>>())
                .unwrap_or_else(|err| panic!("Failed to read lib dir: {err}"));
            entries.sort_by_key(|e| e.file_name());
            for entry in entries {
                let file_type = entry.file_type().expect("lib dir entry type");
                let name = entry.file_name().to_string_lossy().into_owned();
                let entry_rel = if rel.is_empty() {
                    name
                } else {
                    format!("{rel}/{name}")
                };
                if file_type.is_dir() {
                    walk(&entry.path(), &entry_rel, out);
                } else {
                    let content = std::fs::read(entry.path())
                        .unwrap_or_else(|err| panic!("Failed to read lib dir: {err}"));
                    out.insert(
                        format!("{TEST_LIB_FOLDER}/{entry_rel}"),
                        vfstest::TestFile::from(content.as_slice()),
                    );
                }
            }
        }
        let mut testfs = FxHashMap::default();
        let lib_dir = std::path::Path::new(tsc_repo::test_data_path())
            .join("tests")
            .join("lib");
        walk(&lib_dir, "", &mut testfs);
        testfs
    })
}

/// `SetOptionsFromTestConfig`.
pub fn set_options_from_test_config(
    test_config: &TestConfiguration,
    compiler_options: &mut CompilerOptions,
    harness_options: &mut HarnessOptions,
    current_directory: &RootedDirectoryPath,
    allow_unknown_options: bool,
) -> Result<(), Error> {
    for (name, value) in test_config {
        if name == "typescriptversion" {
            continue;
        }

        if let Some(command_line_option) = get_command_line_option(name) {
            let parsed_value = get_option_value(command_line_option, value, current_directory)?;
            parsinghelpers::parse_compiler_options(
                command_line_option.name,
                &parsed_value,
                compiler_options,
            );
            continue;
        }
        if let Some(harness_option) = get_harness_option(name) {
            let parsed_value = get_option_value(harness_option, value, current_directory)?;
            parse_harness_option(harness_option.name, &parsed_value, harness_options)?;
            continue;
        }
        if !allow_unknown_options {
            return Err(Error::new(format!("Unknown compiler option '{name}'.")));
        }
    }
    Ok(())
}

const EMPTY_COMMAND_LINE_OPTION: CommandLineOption = CommandLineOption {
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

/// `var compilerOptions` — `OPTIONS_DECLARATIONS` plus harness-only extras.
fn compiler_options_decls() -> impl Iterator<Item = CommandLineOptionRef> + 'static {
    static ALLOW_NON_TS_EXTENSIONS: CommandLineOption = CommandLineOption {
        name: "allowNonTsExtensions",
        ..EMPTY_COMMAND_LINE_OPTION
    };
    static NO_ERROR_TRUNCATION: CommandLineOption = CommandLineOption {
        name: "noErrorTruncation",
        ..EMPTY_COMMAND_LINE_OPTION
    };
    static SUPPRESS_OUTPUT_PATH_CHECK: CommandLineOption = CommandLineOption {
        name: "suppressOutputPathCheck",
        ..EMPTY_COMMAND_LINE_OPTION
    };
    static NO_CHECK: CommandLineOption = CommandLineOption {
        name: "noCheck",
        ..EMPTY_COMMAND_LINE_OPTION
    };
    declarations::options_declarations().chain(
        [
            &ALLOW_NON_TS_EXTENSIONS,
            &NO_ERROR_TRUNCATION,
            &SUPPRESS_OUTPUT_PATH_CHECK,
            &NO_CHECK,
        ]
        .into_iter(),
    )
}

// `var harnessCommandLineOptions`.
static HARNESS_USE_CASE_SENSITIVE_FILE_NAMES: CommandLineOption = CommandLineOption {
    name: "useCaseSensitiveFileNames",
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_BASELINE_FILE: CommandLineOption = CommandLineOption {
    name: "baselineFile",
    kind: CommandLineOptionKind::STRING,
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_INCLUDE_BUILT_FILE: CommandLineOption = CommandLineOption {
    name: "includeBuiltFile",
    kind: CommandLineOptionKind::STRING,
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_FILE_NAME: CommandLineOption = CommandLineOption {
    name: "fileName",
    kind: CommandLineOptionKind::STRING,
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_LIB_FILES: CommandLineOption = CommandLineOption {
    name: "libFiles",
    kind: CommandLineOptionKind::LIST,
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_NO_IMPLICIT_REFERENCES: CommandLineOption = CommandLineOption {
    name: "noImplicitReferences",
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_CURRENT_DIRECTORY: CommandLineOption = CommandLineOption {
    name: "currentDirectory",
    kind: CommandLineOptionKind::STRING,
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_SYMLINK: CommandLineOption = CommandLineOption {
    name: "symlink",
    kind: CommandLineOptionKind::STRING,
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_LINK: CommandLineOption = CommandLineOption {
    name: "link",
    kind: CommandLineOptionKind::STRING,
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_NO_TYPES_AND_SYMBOLS: CommandLineOption = CommandLineOption {
    name: "noTypesAndSymbols",
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_FULL_EMIT_PATHS: CommandLineOption = CommandLineOption {
    name: "fullEmitPaths",
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_REPORT_DIAGNOSTICS: CommandLineOption = CommandLineOption {
    name: "reportDiagnostics",
    ..EMPTY_COMMAND_LINE_OPTION
};
static HARNESS_CAPTURE_SUGGESTIONS: CommandLineOption = CommandLineOption {
    name: "captureSuggestions",
    ..EMPTY_COMMAND_LINE_OPTION
};

static HARNESS_COMMAND_LINE_OPTIONS: &[CommandLineOptionRef] = &[
    &HARNESS_USE_CASE_SENSITIVE_FILE_NAMES,
    &HARNESS_BASELINE_FILE,
    &HARNESS_INCLUDE_BUILT_FILE,
    &HARNESS_FILE_NAME,
    &HARNESS_LIB_FILES,
    &HARNESS_NO_IMPLICIT_REFERENCES,
    &HARNESS_CURRENT_DIRECTORY,
    &HARNESS_SYMLINK,
    &HARNESS_LINK,
    &HARNESS_NO_TYPES_AND_SYMBOLS,
    &HARNESS_FULL_EMIT_PATHS,
    &HARNESS_REPORT_DIAGNOSTICS,
    &HARNESS_CAPTURE_SUGGESTIONS,
];

fn harness_command_line_options() -> &'static [CommandLineOptionRef] {
    HARNESS_COMMAND_LINE_OPTIONS
}

/// `getHarnessOption`.
fn get_harness_option(name: &str) -> Option<CommandLineOptionRef> {
    harness_command_line_options()
        .iter()
        .copied()
        .find(|option| option.name.eq_ignore_ascii_case(name))
}

/// `parseHarnessOption`.
///
// PORT: Go's unchecked `value.(bool)`/`value.(string)`/`value.([]any)`
// assertions become `as_bool`/`as_str`/`as_list` unwraps — a mismatched kind
// panics in both ports.
fn parse_harness_option(
    key: &str,
    value: &Value,
    harness_options: &mut HarnessOptions,
) -> Result<(), Error> {
    fn want_bool(v: &Value) -> bool {
        v.as_bool().expect("harness option value must be a boolean")
    }
    fn want_str(v: &Value) -> &str {
        v.as_str().expect("harness option value must be a string")
    }
    match key {
        "useCaseSensitiveFileNames" => {
            harness_options.case_sensitivity = if want_bool(value) {
                CaseSensitivity::CaseSensitive
            } else {
                CaseSensitivity::CaseInsensitive
            };
        }
        "baselineFile" => harness_options.baseline_file = want_str(value).to_string(),
        "includeBuiltFile" => harness_options.include_built_file = want_str(value).to_string(),
        "fileName" => harness_options.file_name = want_str(value).to_string(),
        "libFiles" => {
            harness_options.lib_files = value
                .as_list()
                .expect("libFiles must be a list")
                .iter()
                .map(|v| want_str(v).to_string())
                .collect();
        }
        "noImplicitReferences" => harness_options.no_implicit_references = want_bool(value),
        "currentDirectory" => {
            harness_options.current_directory = tspath::to_rooted_directory_path(
                want_str(value),
                &harness_options.current_directory,
            );
        }
        "symlink" => harness_options.symlink = want_str(value).to_string(),
        "link" => harness_options.link = want_str(value).to_string(),
        "noTypesAndSymbols" => harness_options.no_types_and_symbols = want_bool(value),
        "fullEmitPaths" => harness_options.full_emit_paths = want_bool(value),
        "reportDiagnostics" => harness_options.report_diagnostics = want_bool(value),
        "captureSuggestions" => harness_options.capture_suggestions = want_bool(value),
        "typescriptVersion" => harness_options.typescript_version = want_str(value).to_string(),
        _ => return Err(Error::new(format!("Unknown harness option '{key}'."))),
    }
    Ok(())
}

/// `getOptionValue`.
fn get_option_value(
    option: CommandLineOptionRef,
    value: &str,
    cwd: &RootedDirectoryPath,
) -> Result<Value, Error> {
    match option.kind {
        CommandLineOptionKind::String => {
            if option.path_kind.is_rooted() {
                return Ok(Value::Str(
                    tspath::get_normalized_absolute_path(value, cwd).into_owned(),
                ));
            }
            Ok(Value::Str(value.to_string()))
        }
        CommandLineOptionKind::Number => value.parse::<i64>().map(Value::Int).map_err(|_| {
            Error::new(format!(
                "Value for option '{}' must be a number, got: {value}",
                option.name
            ))
        }),
        CommandLineOptionKind::Boolean => match value.to_lowercase().as_str() {
            "true" => Ok(Value::Bool(true)),
            "false" => Ok(Value::Bool(false)),
            _ => Err(Error::new(format!(
                "Value for option '{}' must be a boolean, got: {value}",
                option.name
            ))),
        },
        CommandLineOptionKind::Enum => {
            let enum_map = option.enum_map().expect("enum option has enum map");
            match enum_map.get(&value.to_lowercase()) {
                Some(enum_val) => Ok(enum_val.clone()),
                None => Err(Error::new(format!(
                    "Value for option '{}' must be one of {}, got: {value}",
                    option.name,
                    enum_map.keys().cloned().collect::<Vec<_>>().join(","),
                ))),
            }
        }
        CommandLineOptionKind::List | CommandLineOptionKind::ListOrElement => {
            let (list_val, errors) = commandlineparser::parse_list_type_option(option, value);
            if option.elements().is_some_and(|e| e.path_kind.is_rooted()) {
                return Ok(Value::List(
                    list_val
                        .into_iter()
                        .map(|item| {
                            let s = item.as_str().expect("list element must be a string");
                            Value::Str(tspath::get_normalized_absolute_path(s, cwd).into_owned())
                        })
                        .collect(),
                ));
            }
            if !errors.is_empty() {
                return Err(Error::new(format!(
                    "Unknown value '{value}' for compiler option '{}'",
                    option.name
                )));
            }
            Ok(Value::List(list_val))
        }
        CommandLineOptionKind::Object => Err(Error::new(format!(
            "Object type options like '{}' are not supported",
            option.name
        ))),
    }
}

// `var sourceFileCache` — `collections.SyncMap` becomes a thread-local map:
// `ParsedSourceFile`/`Node` aren't `Send`, and the parse cache is only a
// performance optimization, so per-thread storage matches Go's sharing
// semantics wherever it is reachable.
thread_local! {
    static SOURCE_FILE_CACHE: RefCell<FxHashMap<SourceFileCacheKey, ParsedSourceFile>> =
        RefCell::new(FxHashMap::default());
}

// PORT: Go's `SyncMap` is unbounded, but `ParsedSourceFile` retains a whole
// node arena per entry — across a full baseline suite that pins gigabytes of
// ASTs and OOMs the host. Bound the cache; a miss only costs a re-parse.
// Library files (`lib.*.d.ts`) are the hot shared parses, so eviction keeps
// them and drops test-case files first.
const SOURCE_FILE_CACHE_CAP: usize = 256;

fn source_file_cache_evict_if_full(
    cache: &mut FxHashMap<SourceFileCacheKey, ParsedSourceFile>,
) {
    if cache.len() < SOURCE_FILE_CACHE_CAP {
        return;
    }
    cache.retain(|key, _| key.file_name.as_string().contains("/lib."));
    if cache.len() >= SOURCE_FILE_CACHE_CAP {
        cache.clear();
    }
}

/// `type SourceFileCacheKey struct`.
///
// PORT: `ast.SourceFileParseOptions` isn't `Hash`; the key flattens its
// fields.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SourceFileCacheKey {
    pub file_name: RootedFilePath,
    pub path_key: PathKey,
    pub external_module_indicator_jsx: bool,
    pub external_module_indicator_force: bool,
    pub text: String,
    pub script_kind: ScriptKind,
}

/// `GetSourceFileCacheKey`.
pub fn get_source_file_cache_key(
    opts: &SourceFileParseOptions,
    text: &str,
    script_kind: ScriptKind,
) -> SourceFileCacheKey {
    SourceFileCacheKey {
        file_name: opts.file_name.clone(),
        path_key: opts.path_key.clone(),
        external_module_indicator_jsx: opts.external_module_indicator_options.jsx,
        external_module_indicator_force: opts.external_module_indicator_options.force,
        text: text.to_string(),
        script_kind,
    }
}

/// `type TracerForBaselining struct` — the `*strings.Builder` is `builder`.
pub struct TracerForBaselining {
    current_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
    package_json_cache: FxHashMap<PathKey, bool>,
    builder: String,
}

/// `NewTracerForBaselining` — the Go constructor takes the `*strings.Builder`
/// externally; the port owns it (`string()` exposes the contents).
pub fn new_tracer_for_baselining(
    current_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> TracerForBaselining {
    TracerForBaselining {
        current_directory,
        case_sensitivity,
        package_json_cache: FxHashMap::default(),
        builder: String::new(),
    }
}

impl TracerForBaselining {
    /// `Trace` — `msg.Localize(locale.Default, args...)`; the Rust `TraceFn`
    /// delivers args pre-stringified.
    pub fn trace(&mut self, msg: &'static tsc_diagnostics::Message, args: &[String]) {
        let localized = msg.localize(&tsc_locale::DEFAULT, args);
        let sanitized = self.sanitize_trace(&localized, true);
        let _ = writeln!(self.builder, "{sanitized}");
    }

    /// `TraceWithWriter`.
    pub fn trace_with_writer(
        &mut self,
        w: &mut impl std::fmt::Write,
        msg: &str,
        use_package_json_cache: bool,
    ) {
        let sanitized = self.sanitize_trace(msg, use_package_json_cache);
        let _ = writeln!(w, "{sanitized}");
    }

    /// `sanitizeTrace`.
    pub fn sanitize_trace(&mut self, msg: &str, use_package_json_cache: bool) -> String {
        // Version
        let versioned = msg.replacen(
            &format!("'{}'", tsc_core::version::version()),
            &format!("'{FAKE_TS_VERSION}'"),
            1,
        );
        if versioned != msg {
            return versioned;
        }
        // caching of fs in trace to be replaces with non caching version
        if let Some(str_) =
            msg.strip_suffix("' does not exist according to earlier cached lookups.")
        {
            let file = str_.strip_prefix("File '").unwrap_or(str_);
            if use_package_json_cache {
                let file_path = self
                    .case_sensitivity
                    .path_key(&tspath::to_rooted_path(file, &self.current_directory));
                if self.package_json_cache.contains_key(&file_path) {
                    return msg.to_string();
                }
                self.package_json_cache.insert(file_path, false);
            }
            return format!("File '{file}' does not exist.");
        }
        if let Some(str_) = msg.strip_suffix("' exists according to earlier cached lookups.") {
            let file = str_.strip_prefix("File '").unwrap_or(str_);
            if use_package_json_cache {
                let file_path = self
                    .case_sensitivity
                    .path_key(&tspath::to_rooted_path(file, &self.current_directory));
                if self.package_json_cache.contains_key(&file_path) {
                    return msg.to_string();
                }
                self.package_json_cache.insert(file_path, true);
            }
            return format!("Found 'package.json' at '{file}'.");
        }
        if use_package_json_cache {
            if let Some(str_) = msg.strip_suffix("' does not exist.") {
                let file = str_.strip_prefix("File '").unwrap_or(str_);
                let file_path = self
                    .case_sensitivity
                    .path_key(&tspath::to_rooted_path(file, &self.current_directory));
                return match self.package_json_cache.entry(file_path) {
                    std::collections::hash_map::Entry::Vacant(e) => {
                        e.insert(false);
                        msg.to_string()
                    }
                    std::collections::hash_map::Entry::Occupied(_) => {
                        format!("File '{file}' does not exist according to earlier cached lookups.")
                    }
                };
            }
            if let Some(str_) = msg.strip_prefix("Found 'package.json' at '") {
                let file = str_.strip_suffix("'.").unwrap_or(str_);
                let file_path = self
                    .case_sensitivity
                    .path_key(&tspath::to_rooted_path(file, &self.current_directory));
                return match self.package_json_cache.entry(file_path) {
                    std::collections::hash_map::Entry::Vacant(e) => {
                        e.insert(true);
                        msg.to_string()
                    }
                    std::collections::hash_map::Entry::Occupied(_) => {
                        format!("File '{file}' exists according to earlier cached lookups.")
                    }
                };
            }
        }
        msg.to_string()
    }

    /// `String` — the accumulated trace output.
    pub fn string(&self) -> String {
        self.builder.clone()
    }

    /// `Reset`.
    pub fn reset(&mut self) {
        self.package_json_cache = FxHashMap::default();
    }
}

/// `type cachedCompilerHost struct` — embeds `compiler.CompilerHost`.
///
// PORT: Go embeds the interface and overrides `GetSourceFile`; Rust wraps
// [BasicCompilerHost] and delegates every trait member. `tracer` and
// `recorder` live on the concrete type — Go recovers the recorder from
// `host.FS().(*OutputRecorderFS)`, but `Vfs` has no downcast hook.
pub struct CachedCompilerHost {
    inner: BasicCompilerHost,
    tracer: Arc<Mutex<TracerForBaselining>>,
    recorder: Arc<OutputRecorderFs>,
}

impl CachedCompilerHost {
    /// `tracer.String()`.
    pub fn tracer_string(&self) -> String {
        self.tracer.lock().unwrap().string()
    }

    /// The `TracerForBaselining` handle (e.g. for `Reset`/`TraceWithWriter`).
    pub fn tracer(&self) -> Arc<Mutex<TracerForBaselining>> {
        self.tracer.clone()
    }

    /// The `*OutputRecorderFS` decorating `fs()`.
    pub fn recorder(&self) -> &Arc<OutputRecorderFs> {
        &self.recorder
    }
}

impl CompilerHost for CachedCompilerHost {
    fn fs(&self) -> &Arc<dyn Vfs> {
        self.inner.fs()
    }

    fn default_library_path(&self) -> &RootedDirectoryPath {
        self.inner.default_library_path()
    }

    fn trace(&self, msg: &'static tsc_diagnostics::Message, args: &[String]) {
        self.inner.trace(msg, args)
    }

    /// `(h *cachedCompilerHost) GetSourceFile`.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<ParsedSourceFile> {
        let text = self.fs().read_file(&opts.file_name)?;

        let script_kind = get_script_kind_from_file_name(&opts.file_name);
        if script_kind == ScriptKind::Unknown {
            panic!(
                "Unknown script kind for file  {}",
                opts.file_name.as_string()
            );
        }

        let key = get_source_file_cache_key(opts, &text, script_kind);
        SOURCE_FILE_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            if let Some(cached) = cache.get(&key) {
                // Share the cached arena; programs mutate through `ArenaCell`
                // copy-on-write, so the canonical parse stays pristine.
                return Some(ParsedSourceFile {
                    file: cached.file,
                    nodes: cached.nodes.clone(),
                });
            }
            let (file, nodes) = tsc_parser::parse_source_file(opts.clone(), &text, script_kind);
            let parsed = ParsedSourceFile {
                file,
                nodes: std::rc::Rc::new(nodes),
            };
            source_file_cache_evict_if_full(&mut cache);
            cache.insert(key, parsed.clone());
            Some(parsed)
        })
    }

    fn get_content_mapped_source_files(
        &self,
        parse_options: &SourceFileParseOptions,
        mapper: &Arc<Mapper>,
    ) -> Result<tsc_contentmapper::SourceFiles, tsc_contentmapper::Error> {
        self.inner
            .get_content_mapped_source_files(parse_options, mapper)
    }

    fn content_mapper_project(&self) -> Option<&Arc<dyn Project>> {
        self.inner.content_mapper_project()
    }

    fn get_resolved_project_reference(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<ParsedCommandLine>> {
        self.inner.get_resolved_project_reference(file_name, path)
    }
}

/// `createCompilerHost`.
fn create_compiler_host(
    recorder: Arc<OutputRecorderFs>,
    default_library_path: RootedDirectoryPath,
    current_directory: &RootedDirectoryPath,
    content_mapper_project: Option<Arc<dyn Project>>,
) -> Arc<CachedCompilerHost> {
    let fs: Arc<dyn Vfs> = recorder.clone();
    let tracer = Arc::new(Mutex::new(new_tracer_for_baselining(
        current_directory.clone(),
        fs.case_sensitivity(),
    )));
    let tracer_for_fn = tracer.clone();
    let inner = tsc_compiler::host::new_compiler_host(
        fs,
        default_library_path,
        None, // extended_config_cache
        Some(Box::new(
            move |msg: &'static tsc_diagnostics::Message, args: &[String]| {
                tracer_for_fn.lock().unwrap().trace(msg, args);
            },
        )),
        content_mapper_project,
    );
    Arc::new(CachedCompilerHost {
        inner,
        tracer,
        recorder,
    })
}

/// `compileFilesWithHost`.
fn compile_files_with_host(
    host: &Arc<CachedCompilerHost>,
    config: &Arc<ParsedCommandLine>,
    harness_options: &HarnessOptions,
) -> CompilationResult {
    // !!!
    // if (compilerOptions.project || !rootFiles || rootFiles.length === 0) {
    //     ... readProject path is commented out upstream too.

    let ctx = Context::background();
    let dyn_host: Arc<dyn CompilerHost> = host.clone();

    let mut pre_errors: Vec<DiagnosticRef> = Vec::new();
    let mut pre_compiler_options = config.compiler_options().cloned().unwrap_or_default();
    pre_compiler_options.trace_resolution = TS_FALSE;
    let mut pre_config = tsc_tsoptions::parsedcommandline::new_parsed_command_line(
        pre_compiler_options,
        config.file_names().to_vec(),
        config.project_references().to_vec(),
        config.base_directory().clone(),
        config.case_sensitivity(),
    );
    if let Some(parsed) = config.parsed_config.as_ref() {
        pre_config.set_content_mappers(parsed.content_mappers.clone());
    }
    pre_config.config_file = config.config_file.clone();
    *pre_config.errors.lock().unwrap() = config
        .errors
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone();
    let pre_config = Arc::new(pre_config);

    let pre_program = create_program(dyn_host.clone(), &pre_config);
    pre_errors.extend(pre_program.get_config_file_parsing_diagnostics());
    pre_errors.extend(pre_program.get_program_diagnostics());
    pre_errors.extend(pre_program.get_syntactic_diagnostics(ctx.clone(), None));
    pre_errors.extend(pre_program.get_semantic_diagnostics(ctx.clone(), None));
    pre_errors.extend(pre_program.get_global_diagnostics(ctx.clone()));
    if harness_options.capture_suggestions {
        pre_errors.extend(pre_program.get_suggestion_diagnostics(ctx.clone(), None));
    }
    if pre_program.options().get_emit_declarations() {
        pre_errors.extend(pre_program.get_declaration_diagnostics(ctx.clone(), None));
    }
    let pre_errors = tsc_compiler::program::sort_and_deduplicate_diagnostics(pre_errors);
    // `pre_program` is dead after its diagnostics — release the pooled
    // checkers' `Rc<Program>` back-edge so the whole graph can drop here
    // rather than surviving for the rest of the process (`Rc` cycle; Go
    // relies on GC).
    pre_program.release_checker_pool();

    let post_program = create_program(dyn_host.clone(), config);
    let emit_result = post_program.emit(ctx.clone(), &mut EmitOptions::default());
    let mut post_errors: Vec<DiagnosticRef> = Vec::new();
    post_errors.extend(post_program.get_config_file_parsing_diagnostics());
    post_errors.extend(post_program.get_program_diagnostics());
    post_errors.extend(post_program.get_syntactic_diagnostics(ctx.clone(), None));
    post_errors.extend(post_program.get_semantic_diagnostics(ctx.clone(), None));
    post_errors.extend(post_program.get_global_diagnostics(ctx.clone()));
    if post_program.options().get_emit_declarations() {
        post_errors.extend(post_program.get_declaration_diagnostics(ctx.clone(), None));
    }
    if harness_options.capture_suggestions {
        post_errors.extend(post_program.get_suggestion_diagnostics(ctx.clone(), None));
    }
    let mut errors = tsc_compiler::program::sort_and_deduplicate_diagnostics(post_errors);

    if errors.len() != pre_errors.len() {
        // `longer`/`shorter` — Go swaps by length.
        let swap = pre_errors.len() > errors.len();
        let (longer_errors, shorter_errors) = if swap {
            (&pre_errors, &errors)
        } else {
            (&errors, &pre_errors)
        };
        let diag = tsc_ast::diagnostic::new_compiler_diagnostic::<String>(
            tsc_diagnostics::new_adhoc_message(format!(
                "Pre-emit ({}) and post-emit ({}) diagnostic counts do not match! This can indicate that a semantic _error_ was added by the emit resolver - such an error may not be reflected on the command line or in the editor, but may be captured in a baseline here!",
                pre_errors.len(),
                errors.len()
            )),
            &[],
        );
        diag.lock().unwrap().add_related_info(Some(
            tsc_ast::diagnostic::new_compiler_diagnostic::<String>(
                tsc_diagnostics::new_adhoc_message("The excess diagnostics are:".to_string()),
                &[],
            ),
        ));
        for d in longer_errors {
            let matched = shorter_errors
                .iter()
                .any(|d2| tsc_ast::diagnostic::compare_diagnostics(d, d2) == 0);
            if !matched {
                diag.lock().unwrap().add_related_info(Some(d.clone()));
            }
        }
        let mut shorter_errors = shorter_errors.clone();
        shorter_errors.push(diag);
        errors = shorter_errors;
    }

    new_compilation_result(
        dyn_host,
        Some(host.recorder().clone()),
        harness_options.current_directory.clone(),
        config.compiler_options().cloned().unwrap_or_default(),
        post_program,
        Some(emit_result),
        errors,
        harness_options.clone(),
    )
}

/// `type CompilationResult struct`.
///
// PORT: `Repeat` panics instead of `t.Fatalf` inside
// `SetOptionsFromTestConfig`.
pub struct CompilationResult {
    pub diagnostics: Vec<DiagnosticRef>,
    pub result: Option<EmitResult>,
    /// `Program compiler.ProgramLike` — always set for compilations created
    /// through [`compile_files`]/[`compile_files_with_host`].
    pub program: Rc<dyn ProgramLike>,
    pub options: Rc<CompilerOptions>,
    pub harness_options: HarnessOptions,
    pub js: OrderedMap<RootedFilePath, Arc<TestFile>>,
    pub dts: OrderedMap<RootedFilePath, Arc<TestFile>>,
    pub maps: OrderedMap<RootedFilePath, Arc<TestFile>>,
    pub symlinks: FxHashMap<String, String>,
    /// `Repeat func(TestConfiguration) *CompilationResult`.
    pub repeat: Option<Box<dyn Fn(TestConfiguration) -> CompilationResult>>,
    outputs: Vec<Arc<TestFile>>,
    inputs: Vec<Arc<TestFile>>,
    inputs_and_outputs: OrderedMap<RootedFilePath, Rc<CompilationOutput>>,
    pub trace: String,
    /// `Host compiler.CompilerHost`.
    pub host: Arc<dyn CompilerHost>,
    current_directory: RootedDirectoryPath,
}

impl Drop for CompilationResult {
    /// The program's checker pool keeps `Rc<RefCell<Checker>>`s whose
    /// `Checker.program` back-edge keeps the `Rc<Program>` alive — an `Rc`
    /// cycle the Go side resolves through GC. Without releasing it, each
    /// test's entire program graph (checker arenas, symbols, types) is
    /// retained for the rest of the process — the baseline runner's ~600MB
    /// per-test RSS growth.
    fn drop(&mut self) {
        self.program.release_checker_pool();
    }
}

/// `type CompilationOutput struct`.
pub struct CompilationOutput {
    pub inputs: Vec<Arc<TestFile>>,
    pub js: Option<Arc<TestFile>>,
    pub dts: Option<Arc<TestFile>>,
    pub map: Option<Arc<TestFile>>,
}

/// `newCompilationResult`.
#[allow(clippy::too_many_arguments)]
fn new_compilation_result(
    host: Arc<dyn CompilerHost>,
    recorder: Option<Arc<OutputRecorderFs>>,
    current_directory: RootedDirectoryPath,
    // `options` is unused when `program` is present — Go only falls back to it
    // when `program == nil`.
    _options: CompilerOptions,
    program: Rc<dyn ProgramLike>,
    result: Option<EmitResult>,
    diagnostics: Vec<DiagnosticRef>,
    harness_options: HarnessOptions,
) -> CompilationResult {
    let mut c = CompilationResult {
        diagnostics,
        result,
        options: Rc::new(program.options().clone()),
        program,
        harness_options,
        js: OrderedMap::default(),
        dts: OrderedMap::default(),
        maps: OrderedMap::default(),
        symlinks: FxHashMap::default(),
        repeat: None,
        outputs: Vec::new(),
        inputs: Vec::new(),
        inputs_and_outputs: OrderedMap::default(),
        trace: String::new(),
        host,
        current_directory,
    };

    // Go: `fs := host.FS().(*OutputRecorderFS)` — the recorder is the FS
    // passed to the host, carried separately here.
    if let Some(recorder) = recorder {
        let program = c.program.clone();
        // Corsa, unlike Strada, can use multiple threads for emit. As a result, the order of outputs is non-deterministic.
        // To make the order deterministic, we sort the outputs by the order of the inputs.
        let mut js: OrderedMap<RootedFilePath, Arc<TestFile>> = OrderedMap::default();
        let mut dts: OrderedMap<RootedFilePath, Arc<TestFile>> = OrderedMap::default();
        let mut maps: OrderedMap<RootedFilePath, Arc<TestFile>> = OrderedMap::default();
        let mut output_paths: FxHashMap<*const TestFile, RootedFilePath> = FxHashMap::default();
        for output in recorder.recorded_outputs() {
            let document = output.file;
            output_paths.insert(Arc::as_ptr(&document), output.path.clone());
            if output.path.has_js_file_extension() || output.path.has_json_file_extension() {
                js.set(output.path.clone(), document);
            } else if output.path.is_declaration_file() {
                dts.set(output.path.clone(), document);
            } else if output.path.extension_is(".map") {
                maps.set(output.path.clone(), document);
            }
        }

        // using the order from the inputs, populate the outputs
        for source_file in program.get_source_files() {
            let (file_name, text) = {
                let nodes = program.program().arena_of(source_file);
                let sf = nodes[source_file].as_source_file();
                (sf.file_name().clone(), sf.text().to_string())
            };
            // `!fileName.IsDeclarationFile()` — Go checks the *path*, not the
            // node's `IsDeclarationFile` flag (the declaration transform flips
            // that flag on the source file during emit).
            let is_declaration_file = file_name.is_declaration_file();
            let file_name_string = file_name.as_string().to_string();
            let input = Arc::new(TestFile {
                unit_name: file_name_string.clone(),
                content: text,
            });
            c.inputs.push(input.clone());
            if !is_declaration_file {
                let extname =
                    tsc_outputpaths::get_output_extension_for_file_name(&file_name, c.options.jsx);
                let js_path = c.get_output_path(&file_name, extname);
                let dts_path = c.get_output_path(
                    &file_name,
                    &tspath::get_declaration_emit_extension_for_path(&file_name_string),
                );
                let map_path = c.get_output_path(&file_name, &format!("{extname}.map"));
                let outputs = Rc::new(CompilationOutput {
                    inputs: vec![input],
                    js: js.get(&js_path).cloned(),
                    dts: dts.get(&dts_path).cloned(),
                    map: maps.get(&map_path).cloned(),
                });
                c.inputs_and_outputs.set(file_name, outputs.clone());
                if let Some(js_file) = outputs.js.clone() {
                    c.inputs_and_outputs.set(js_path.clone(), outputs.clone());
                    c.js.set(js_path.clone(), js_file.clone());
                    js.delete(&js_path);
                    c.outputs.push(js_file);
                }
                if let Some(dts_file) = outputs.dts.clone() {
                    c.inputs_and_outputs.set(dts_path.clone(), outputs.clone());
                    c.dts.set(dts_path.clone(), dts_file.clone());
                    dts.delete(&dts_path);
                    c.outputs.push(dts_file);
                }
                if let Some(map_file) = outputs.map.clone() {
                    c.inputs_and_outputs.set(map_path.clone(), outputs.clone());
                    c.maps.set(map_path.clone(), map_file.clone());
                    maps.delete(&map_path);
                    c.outputs.push(map_file);
                }
            }
        }

        // add any unhandled outputs, ordered by unit name
        let mut remaining_js: Vec<Arc<TestFile>> = js.values().cloned().collect();
        remaining_js.sort_by(|a, b| compare_test_files(a, b));
        for document in remaining_js {
            let path = output_paths[&Arc::as_ptr(&document)].clone();
            c.js.set(path, document);
        }
        let mut remaining_dts: Vec<Arc<TestFile>> = dts.values().cloned().collect();
        remaining_dts.sort_by(|a, b| compare_test_files(a, b));
        for document in remaining_dts {
            let path = output_paths[&Arc::as_ptr(&document)].clone();
            c.dts.set(path, document);
        }
        let mut remaining_maps: Vec<Arc<TestFile>> = maps.values().cloned().collect();
        remaining_maps.sort_by(|a, b| compare_test_files(a, b));
        for document in remaining_maps {
            let path = output_paths[&Arc::as_ptr(&document)].clone();
            c.maps.set(path, document);
        }
    }

    c
}

/// `compareTestFiles`.
fn compare_test_files(a: &TestFile, b: &TestFile) -> std::cmp::Ordering {
    a.unit_name.cmp(&b.unit_name)
}

impl CompilationResult {
    /// `(c *CompilationResult) getOutputPath`.
    fn get_output_path(&self, file_path: &RootedFilePath, ext: &str) -> RootedFilePath {
        let mut output_path = file_path.clone();
        let is_declaration_ext = ext == ".d.ts"
            || ext == ".d.mts"
            || ext == ".d.cts"
            || (ext.ends_with(".ts") && ext.contains(".d."));
        let out_dir = if is_declaration_ext {
            if self.options.declaration_dir.is_empty() {
                self.options.out_dir.clone()
            } else {
                self.options.declaration_dir.clone()
            }
        } else {
            self.options.out_dir.clone()
        };
        if !out_dir.is_empty() {
            let common = self.program.common_source_directory();
            if !common.is_empty()
                && let Some(relative_path) = self
                    .host
                    .fs()
                    .case_sensitivity()
                    .relative_path_from_directory(&common, file_path)
            {
                let mut output_directory = self.options.out_dir.clone();
                if output_directory.is_empty() {
                    output_directory = out_dir.clone();
                }
                output_path = output_directory.resolve_relative_file(&relative_path);
            }
        }
        if ext == output_path.declaration_emit_extension() {
            return tsc_outputpaths::change_to_declaration_extension(
                &output_path,
                self.program.program(),
            );
        }
        output_path.change_extension(ext)
    }

    /// `FS`.
    pub fn fs(&self) -> Arc<dyn Vfs> {
        self.host.fs().clone()
    }

    /// `GetNumberOfJSFiles`.
    pub fn get_number_of_js_files(&self, include_json: bool) -> usize {
        if include_json {
            return self.js.size();
        }
        self.js
            .values()
            .filter(|file| !tspath::file_extension_is(&file.unit_name, tspath::EXTENSION_JSON))
            .count()
    }

    /// `Inputs`.
    pub fn inputs(&self) -> &[Arc<TestFile>] {
        &self.inputs
    }

    /// `Outputs`.
    pub fn outputs(&self) -> &[Arc<TestFile>] {
        &self.outputs
    }

    /// `CurrentDirectory`.
    pub fn current_directory(&self) -> &RootedDirectoryPath {
        &self.current_directory
    }

    /// `GetInputsAndOutputsForFile`.
    pub fn get_inputs_and_outputs_for_file(&self, path: &str) -> Option<Rc<CompilationOutput>> {
        self.inputs_and_outputs
            .get(&self.current_directory.resolve_file(path))
            .cloned()
    }

    /// `GetInputsForFile`.
    pub fn get_inputs_for_file(&self, path: &str) -> Vec<Arc<TestFile>> {
        self.get_inputs_and_outputs_for_file(path)
            .map(|o| o.inputs.clone())
            .unwrap_or_default()
    }

    /// `GetOutput` — `kind` is `"js" | "dts" | "map"`.
    pub fn get_output(&self, path: &str, kind: &str) -> Option<Arc<TestFile>> {
        self.get_inputs_and_outputs_for_file(path)
            .and_then(|outputs| match kind {
                "js" => outputs.js.clone(),
                "dts" => outputs.dts.clone(),
                "map" => outputs.map.clone(),
                _ => None,
            })
    }

    /// `GetSourceMapRecord`.
    pub fn get_source_map_record(&self) -> String {
        let Some(result) = &self.result else {
            return String::new();
        };
        if result.source_maps.is_empty() {
            return String::new();
        }
        let program = &self.program;

        let mut source_map_recorder = WriterAggregator::default();
        for source_map_data in &result.source_maps {
            let mut prev_source_file: Option<NodeId> = None;
            let current_file = if tspath::is_declaration_file_name(&source_map_data.generated_file)
            {
                self.dts
                    .get(&tspath::to_rooted_file_path(
                        &source_map_data.generated_file,
                        &self.current_directory,
                    ))
                    .cloned()
            } else {
                self.js
                    .get(&tspath::to_rooted_file_path(
                        &source_map_data.generated_file,
                        &self.current_directory,
                    ))
                    .cloned()
            };

            // Go passes `currentFile` (possibly nil) to the writer — its only
            // uses are `content`/`unitName`, so an absent file reads as an
            // empty `TestFile`.
            let current_file = current_file.unwrap_or_else(|| {
                Arc::new(TestFile {
                    unit_name: String::new(),
                    content: String::new(),
                })
            });

            let mut source_map_span_writer = new_source_map_span_writer(
                &mut source_map_recorder,
                &source_map_data.source_map,
                &current_file,
            );
            let mut mapper = decode_mappings(&source_map_data.source_map.mappings);
            while let Some(decoded_source_mapping) = mapper.next() {
                if !decoded_source_mapping.is_source_mapping() {
                    source_map_span_writer.record_source_map_span(decoded_source_mapping);
                    continue;
                }
                let current_source_file = program.get_source_file(&tspath::to_rooted_file_path(
                    &source_map_data.input_source_file_names
                        [decoded_source_mapping.source_index as usize],
                    &self.current_directory,
                ));
                if current_source_file != prev_source_file {
                    if let Some(file) = current_source_file {
                        let original_text = {
                            let nodes = program.program().arena_of(file);
                            nodes[file].as_source_file().original_text().to_string()
                        };
                        source_map_span_writer
                            .record_new_source_file_span(decoded_source_mapping, &original_text);
                    }
                    prev_source_file = current_source_file;
                } else {
                    source_map_span_writer.record_source_map_span(decoded_source_mapping);
                }
            }
            source_map_span_writer.close();
        }
        source_map_recorder.into_string()
    }
}

/// `createProgram`.
fn create_program(
    host: Arc<dyn CompilerHost>,
    config: &Arc<ParsedCommandLine>,
) -> Rc<dyn ProgramLike> {
    let single_threaded = if crate::test_program_is_single_threaded() {
        TS_TRUE
    } else {
        Tristate::default()
    };

    let program: Rc<Program> = tsc_compiler::program::new_program(ProgramOptions {
        config: Rc::new(ProgramConfig {
            config: config.clone(),
            single_threaded,
            ..Default::default()
        }),
        hosts: ProgramHosts {
            host,
            tracing: None,
        },
        factories: ProgramFactories::default(),
    });
    // PORT(deferred): `config.CompilerOptions().Incremental.IsTrue()` would wrap
    // the program via `incremental.ReadBuildInfoProgram` +
    // `incremental.NewProgram`; the `tsc-execute` incremental port is a
    // skeleton, so the plain program is returned instead.
    program
}

/// `EnumerateFiles`.
///
// PORT: `testRegex *regexp.Regexp` is a predicate — no `regex` dep.
pub fn enumerate_files(
    folder: &str,
    test_matcher: Option<fn(&str) -> bool>,
    recursive: bool,
) -> std::io::Result<Vec<String>> {
    let test_data_directory =
        tspath::rooted_directory_path_from_absolute(tsc_repo::test_data_path());
    list_files_worker(
        test_matcher,
        recursive,
        &tspath::to_rooted_directory_path(folder, &test_data_directory),
    )
}

/// `listFilesWorker`.
fn list_files_worker(
    spec: Option<fn(&str) -> bool>,
    recursive: bool,
    folder: &RootedDirectoryPath,
) -> Result<Vec<String>, std::io::Error> {
    let mut paths = Vec::new();
    for entry in std::fs::read_dir(folder.as_string())? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            if !recursive {
                continue;
            }
            let name = entry.file_name();
            let sub_paths = list_files_worker(
                spec,
                recursive,
                &folder.resolve_directory(name.to_string_lossy().as_ref()),
            )?;
            paths.extend(sub_paths);
            continue;
        }
        let name = entry.file_name();
        let path = folder.resolve_file(name.to_string_lossy().as_ref());
        if spec.is_none_or(|s| s(path.as_string())) {
            paths.push(path.as_string().to_string());
        }
    }
    Ok(paths)
}

/// `getFileBasedTestConfigurationDescription`.
fn get_file_based_test_configuration_description(config: &TestConfiguration) -> String {
    let mut output = String::new();
    let sorted: BTreeMap<&String, &String> = config.iter().collect();
    for (i, (key, value)) in sorted.iter().enumerate() {
        if i > 0 {
            output.push(',');
        }
        let _ = write!(output, "{key}={}", value.to_lowercase());
    }
    output
}

/// `GetFileBasedTestConfigurations`.
///
// PORT: `t.Fatalf` inside `SplitOptionValues` panics; the "exceeded the
// maximum number of variations" `t.Fatalf` panics too, so this returns the
// slice directly.
pub fn get_file_based_test_configurations(
    settings: &TestConfiguration,
    vary_by_options: &Set<String>,
) -> Vec<NamedTestConfiguration> {
    // Each element slice has the option name as the first element, and the values as the rest
    let mut option_entries: Vec<Vec<String>> = Vec::new();
    let mut variation_count = 1usize;
    let mut non_varying_options: FxHashMap<String, String> = FxHashMap::default();
    for (option, value) in settings {
        if vary_by_options.has(option) {
            let entries = split_option_values(value, option).unwrap_or_else(|e| panic!("{e}"));
            if entries.len() > 1 {
                variation_count *= entries.len();
                if variation_count > 25 {
                    panic!("Provided test options exceeded the maximum number of variations");
                }
                let mut entry = vec![option.clone()];
                entry.extend(entries);
                option_entries.push(entry);
            } else if entries.len() == 1 {
                non_varying_options.insert(option.clone(), entries[0].clone());
            }
        } else {
            // Variation is not supported for the option
            non_varying_options.insert(option.clone(), value.clone());
        }
    }

    let mut configurations = Vec::new();
    if !option_entries.is_empty() {
        // Merge varying and non-varying options
        let varying_configurations =
            compute_file_based_test_configuration_variations(variation_count, &option_entries);
        for mut varying_config in varying_configurations {
            let description = get_file_based_test_configuration_description(&varying_config);
            varying_config.extend(
                non_varying_options
                    .iter()
                    .map(|(k, v)| (k.clone(), v.clone())),
            );
            configurations.push(NamedTestConfiguration {
                name: description,
                config: varying_config,
            });
        }
    } else if !non_varying_options.is_empty() {
        // Only non-varying options
        configurations.push(NamedTestConfiguration {
            name: String::new(),
            config: non_varying_options,
        });
    }
    configurations
}

/// `splitOptionValues` — splits a string value into unique values for the
/// given option; `*` includes all values, `-`/`!` exclude.
fn split_option_values(value: &str, option: &str) -> Result<Vec<String>, Error> {
    if value.is_empty() {
        return Ok(Vec::new());
    }

    let mut star = false;
    let mut includes: Vec<String> = Vec::new();
    let mut excludes: Vec<String> = Vec::new();
    for s in value.split(',') {
        let s = s.trim();
        if s.is_empty() {
            continue;
        }
        if s == "*" {
            star = true;
        } else if let Some(exclude) = s.strip_prefix('-').or_else(|| s.strip_prefix('!')) {
            excludes.push(exclude.to_string());
        } else {
            includes.push(s.to_string());
        }
    }

    if includes.is_empty() && !star && excludes.is_empty() {
        return Ok(Vec::new());
    }

    // Dedupe the variations by their normalized values.
    // PORT: `map[tsoptions.CompilerOptionsValue]string` — `Value` isn't
    // `Hash` (it contains `Float`); its `Debug` form is the dedup key.
    let mut variations: FxHashMap<String, String> = FxHashMap::default();

    // add (and deduplicate) all included entries
    for include in &includes {
        let value = get_value_of_option_string(option, include)?;
        variations
            .entry(format!("{value:?}"))
            .or_insert_with(|| include.clone());
    }

    let all_values = get_all_values_for_option(option);
    if star && !all_values.is_empty() {
        // add all entries
        for include in &all_values {
            let value = get_value_of_option_string(option, include)?;
            variations
                .entry(format!("{value:?}"))
                .or_insert_with(|| include.clone());
        }
    }

    // remove all excluded entries
    for exclude in &excludes {
        let Some(value) = try_get_value_of_option_string(option, exclude) else {
            // The excluded value is not recognized (e.g., a removed option like "es3").
            // Just skip it since there's nothing to remove.
            continue;
        };
        variations.remove(&format!("{value:?}"));
    }

    if variations.is_empty() {
        panic!("Variations in test option '@{option}' resulted in an empty set.");
    }
    // PORT: `slices.Collect(maps.Values(variations))` is map-order; sorted
    // for determinism.
    let mut values: Vec<String> = variations.into_values().collect();
    values.sort();
    Ok(values)
}

/// `getValueOfOptionString`.
fn get_value_of_option_string(option: &str, value: &str) -> Result<Value, Error> {
    try_get_value_of_option_string(option, value)
        .ok_or_else(|| Error::new(format!("Unknown value '{value}' for option '{option}'")))
}

/// `tryGetValueOfOptionString`.
fn try_get_value_of_option_string(option: &str, value: &str) -> Option<Value> {
    let option_decl = get_command_line_option(option)?;
    match option_decl.kind {
        CommandLineOptionKind::Enum => option_decl
            .enum_map()
            .and_then(|m| m.get(&value.to_lowercase()))
            .cloned(),
        CommandLineOptionKind::Boolean => match value.to_lowercase().as_str() {
            "true" => Some(Value::Bool(true)),
            "false" => Some(Value::Bool(false)),
            _ => None,
        },
        _ => Some(Value::Str(value.to_string())),
    }
}

/// `getCommandLineOption`.
fn get_command_line_option(option: &str) -> Option<CommandLineOptionRef> {
    compiler_options_decls().find(|option_decl| option_decl.name.eq_ignore_ascii_case(option))
}

/// `getAllValuesForOption`.
fn get_all_values_for_option(option: &str) -> Vec<String> {
    let Some(option_decl) = get_command_line_option(option) else {
        return Vec::new();
    };
    match option_decl.kind {
        CommandLineOptionKind::Enum => option_decl
            .enum_map()
            .map(|m| m.keys().cloned().collect())
            .unwrap_or_default(),
        CommandLineOptionKind::Boolean => vec!["true".to_string(), "false".to_string()],
        _ => Vec::new(),
    }
}

/// `computeFileBasedTestConfigurationVariations`.
fn compute_file_based_test_configuration_variations(
    variation_count: usize,
    option_entries: &[Vec<String>],
) -> Vec<TestConfiguration> {
    let mut configurations = Vec::with_capacity(variation_count);
    compute_file_based_test_configuration_variations_worker(
        &mut configurations,
        option_entries,
        0,
        TestConfiguration::default(),
    );
    configurations
}

/// `computeFileBasedTestConfigurationVariationsWorker`.
fn compute_file_based_test_configuration_variations_worker(
    configurations: &mut Vec<TestConfiguration>,
    option_entries: &[Vec<String>],
    index: usize,
    variation_state: TestConfiguration,
) {
    if index >= option_entries.len() {
        configurations.push(variation_state);
        return;
    }

    let option_key = option_entries[index][0].clone();
    for entry in &option_entries[index][1..] {
        // set or overwrite the variation, then compute the next variation
        let mut variation_state = variation_state.clone();
        variation_state.insert(option_key.clone(), entry.clone());
        compute_file_based_test_configuration_variations_worker(
            configurations,
            option_entries,
            index + 1,
            variation_state,
        );
    }
}

/// `GetConfigNameFromFileName`.
pub fn get_config_name_from_file_name(filename: &str) -> String {
    let basename_lower = tspath::get_base_file_name(filename).to_lowercase();
    if basename_lower == "tsconfig.json" || basename_lower == "jsconfig.json" {
        return basename_lower;
    }
    String::new()
}

/// `SkipUnsupportedCompilerOptions` — `t.Skipf` becomes `Some(reason)`;
/// `None` means all options are supported. `t.Fatalf` inside
/// `FailOnUnsupportedCompilerOptions` panics.
pub fn skip_unsupported_compiler_options(options: &CompilerOptions) -> Option<String> {
    fail_on_unsupported_compiler_options(options).unwrap_or_else(|e| panic!("{e}"));
    if matches!(options.module, ModuleKind::UMD | ModuleKind::System) {
        return Some(format!("unsupported module kind {}", options.module));
    }
    if matches!(
        options.module_resolution,
        ModuleResolutionKind::Node10 | ModuleResolutionKind::Classic
    ) {
        return Some(format!(
            "unsupported module resolution kind {}",
            options.module_resolution
        ));
    }
    if options.es_module_interop.is_false() {
        return Some("esModuleInterop=false is unsupported".to_string());
    }
    if options.allow_synthetic_default_imports.is_false() {
        return Some("allowSyntheticDefaultImports=false is unsupported".to_string());
    }
    if !options.base_url.is_empty() {
        return Some(format!(
            "unsupported baseUrl {}",
            options.base_url.as_string()
        ));
    }
    if options.target == ScriptTarget::ES5 {
        return Some(format!("unsupported target {}", options.target));
    }
    if options.always_strict.is_false() {
        return Some("alwaysStrict=false is unsupported".to_string());
    }
    None
}

/// `failOnUnsupportedCompilerOptions`.
fn fail_on_unsupported_compiler_options(options: &CompilerOptions) -> Result<(), Error> {
    if options.module == ModuleKind::AMD {
        return Err(Error::new(format!(
            "unsupported module kind {}",
            options.module
        )));
    }
    if !options.out_file.is_empty() {
        return Err(Error::new(format!(
            "unsupported outFile {}",
            options.out_file.as_string()
        )));
    }
    Ok(())
}
