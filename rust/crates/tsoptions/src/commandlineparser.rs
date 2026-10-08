// Ported from tsc/internal/tsoptions/commandlineparser.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_ast::diagnostic::{DiagnosticRef, new_compiler_diagnostic};
use tsc_collections::{OrderedMap, Set};
use tsc_core::options_generated::CompilerOptions;
use tsc_diagnostics::{self as diagnostics};
use tsc_tspath::{self as tspath, PathKey, RootedDirectoryPath};
use tsc_vfs::Vfs;

use crate::commandlineoption::{CommandLineOptionKind, CommandLineOptionRef};
use crate::diagnostics::{
    ParseCommandLineWorkerDiagnostics, build_options_did_you_mean_diagnostics,
    compiler_options_did_you_mean_diagnostics,
};
use crate::errors::{
    create_diagnostic_for_invalid_enum_type, create_unknown_option_error,
    get_compiler_option_value_type_string,
};
use crate::namemap::{NameMap, build_name_map, compiler_name_map, get_name_map_from_list};
use crate::parsedbuildcommandline::ParsedBuildCommandLine;
use crate::parsedcommandline::{ParsedCommandLine, new_parsed_command_line};
use crate::parsinghelpers::{self, BuildOptionsParser, CompilerOptionsParser};
use crate::tsconfigparsing::{
    convert_json_option_of_enum_type, convert_map_to_options, try_read_file,
    validate_json_option_value,
};
use crate::value::Value;

/// `type commandLineParser struct`.
pub(crate) struct CommandLineParser<'a> {
    worker_diagnostics: &'a ParseCommandLineWorkerDiagnostics,
    options_map: NameMap,
    fs: Option<Arc<dyn Vfs>>,
    current_directory: RootedDirectoryPath,
    options: OrderedMap<String, Value>,
    file_names: Vec<String>,
    errors: Vec<DiagnosticRef>,
    response_file_stack: Set<PathKey>,
}

impl CommandLineParser<'_> {
    /// `(p) AlternateMode`.
    fn alternate_mode(&self) -> Option<&'static crate::diagnostics::AlternateModeDiagnostics> {
        self.worker_diagnostics.did_you_mean.alternate_mode
    }

    /// `(p) OptionsDeclarations`.
    fn options_declarations(&self) -> Vec<CommandLineOptionRef> {
        (self.worker_diagnostics.did_you_mean.option_declarations)().collect()
    }

    /// `(p) UnknownOptionDiagnostic`.
    fn unknown_option_diagnostic(&self) -> &'static diagnostics::Message {
        self.worker_diagnostics
            .did_you_mean
            .unknown_option_diagnostic
    }

    /// `(p) UnknownDidYouMeanDiagnostic`.
    fn unknown_did_you_mean_diagnostic(&self) -> &'static diagnostics::Message {
        self.worker_diagnostics
            .did_you_mean
            .unknown_did_you_mean_diagnostic
    }

    /// `(p) createUnknownOptionError`.
    fn create_unknown_option_error(
        &self,
        unknown_option: &str,
        unknown_option_error_text: &str,
    ) -> DiagnosticRef {
        create_unknown_option_error(
            unknown_option,
            self.unknown_option_diagnostic(),
            unknown_option_error_text,
            None,
            None,
            self.alternate_mode(),
            Some(self.unknown_did_you_mean_diagnostic()),
            Some(&crate::tsconfigparsing::command_line_options_to_map(
                &self.options_declarations(),
            )),
        )
    }

    /// `(p) parseStrings`.
    fn parse_strings(&mut self, args: &[String]) {
        let mut i = 0;
        while i < args.len() {
            let s = args[i].clone();
            i += 1;
            if s.is_empty() {
                continue;
            }
            match s.as_bytes()[0] {
                b'@' => self.parse_response_file(&s[1..]),
                b'-' => {
                    let input_option_name = get_input_option_name(&s);
                    let opt = self.options_map.get_option_declaration_from_name(
                        &input_option_name,
                        true, /*allowShort*/
                    );
                    if let Some(opt) = opt {
                        i = self.parse_option_value(
                            args,
                            i,
                            opt,
                            self.worker_diagnostics.option_type_mismatch_diagnostic,
                        );
                    } else {
                        self.errors
                            .push(self.create_unknown_option_error(&input_option_name, &s));
                    }
                }
                _ => {
                    self.file_names.push(s);
                }
            }
        }
    }

    /// `(p) parseResponseFile`.
    fn parse_response_file(&mut self, file_name: &str) {
        let mut typed_file_name =
            tspath::rooted_file_path_from_path(self.current_directory.as_path());
        if !file_name.is_empty() {
            typed_file_name = tspath::to_rooted_file_path(file_name, &self.current_directory);
        }
        let Some(fs) = self.fs.clone() else {
            return;
        };
        let path = fs.case_sensitivity().path_key(&typed_file_name.as_path());
        if self.response_file_stack.has(&path) {
            return;
        }
        self.response_file_stack.add(path.clone());

        let (file_contents, errors) = try_read_file(
            &typed_file_name,
            |file_name| fs.read_file(file_name),
            std::mem::take(&mut self.errors),
        );
        self.errors = errors;
        // Go: defer p.responseFileStack.Delete(path) — the entry stays on the
        // stack for the whole duration of this call, including the recursive
        // parse_strings below, so cyclic response files terminate.
        let delete_path = |p: &mut Self| p.response_file_stack.delete(&path);

        if file_contents.is_empty() {
            delete_path(self);
            return;
        }

        let mut args: Vec<String> = Vec::new();
        let text: Vec<char> = file_contents.chars().collect();
        let text_length = text.len();
        let mut pos = 0;
        while pos < text_length {
            while pos < text_length && text[pos] <= ' ' {
                pos += 1;
            }
            if pos >= text_length {
                break;
            }
            let start = pos;
            if text[pos] == '"' {
                pos += 1;
                while pos < text_length && text[pos] != '"' {
                    pos += 1;
                }
                if pos < text_length {
                    args.push(text[start + 1..pos].iter().collect());
                    pos += 1;
                } else {
                    self.errors.push(new_compiler_diagnostic(
                        &diagnostics::Unterminated_quoted_string_in_response_file_0,
                        &[Value::Str(file_name.to_string())],
                    ));
                }
            } else {
                while pos < text_length && text[pos] > ' ' {
                    pos += 1;
                }
                args.push(text[start..pos].iter().collect());
            }
        }
        self.parse_strings(&args);
        delete_path(self);
    }

    /// `(p) parseOptionValue` — returns the new `i`.
    fn parse_option_value(
        &mut self,
        args: &[String],
        mut i: usize,
        opt: CommandLineOptionRef,
        diag: &'static diagnostics::Message,
    ) -> usize {
        if opt.is_ts_config_only && i <= args.len() {
            let opt_value = if i < args.len() { args[i].as_str() } else { "" };
            if opt_value == "null" {
                self.options.set(opt.name.to_string(), Value::Null);
                i += 1;
            } else if opt.kind == CommandLineOptionKind::Boolean {
                if opt_value == "false" {
                    self.options.set(opt.name.to_string(), Value::Bool(false));
                    i += 1;
                } else {
                    if opt_value == "true" {
                        i += 1;
                    }
                    self.errors.push(new_compiler_diagnostic(
                        &diagnostics::Option_0_can_only_be_specified_in_tsconfig_json_file_or_set_to_false_or_null_on_command_line,
                        &[Value::Str(opt.name.into())],
                    ));
                }
            } else {
                self.errors.push(new_compiler_diagnostic(
                    &diagnostics::Option_0_can_only_be_specified_in_tsconfig_json_file_or_set_to_null_on_command_line,
                    &[Value::Str(opt.name.into())],
                ));
                if !opt_value.is_empty() && !opt_value.starts_with('-') {
                    i += 1;
                }
            }
        } else {
            // Check to see if no argument was provided (e.g. "--locale" is
            // the last command-line argument).
            if i >= args.len() {
                if opt.kind != CommandLineOptionKind::Boolean {
                    self.errors.push(new_compiler_diagnostic(
                        diag,
                        &[
                            Value::Str(opt.name.into()),
                            Value::Str(get_compiler_option_value_type_string(opt)),
                        ],
                    ));
                    if opt.kind == CommandLineOptionKind::List {
                        self.options
                            .set(opt.name.to_string(), Value::StringList(Vec::new()));
                    } else if opt.kind == CommandLineOptionKind::Enum {
                        self.errors
                            .push(create_diagnostic_for_invalid_enum_type(opt, None, None));
                    }
                } else {
                    self.options.set(opt.name.to_string(), Value::Bool(true));
                }
                return i;
            }
            if args[i] != "null" {
                match opt.kind {
                    CommandLineOptionKind::Number => {
                        // !!! Make sure this parseInt matches JS parseInt
                        match args[i].parse::<i64>() {
                            Ok(num) => {
                                if num >= opt.min_value {
                                    self.options.set(opt.name.to_string(), Value::Int(num));
                                } else {
                                    self.errors.push(new_compiler_diagnostic(
                                        &diagnostics::Option_0_requires_value_to_be_greater_than_1,
                                        &[
                                            Value::Str(opt.name.into()),
                                            Value::Str(opt.min_value.to_string()),
                                        ],
                                    ));
                                }
                            }
                            Err(_) => {
                                self.errors.push(new_compiler_diagnostic(
                                    diag,
                                    &[Value::Str(opt.name.into()), Value::Str("number".into())],
                                ));
                            }
                        }
                        i += 1;
                    }
                    CommandLineOptionKind::Boolean => {
                        // boolean flag has optional value true, false, others
                        let opt_value = &args[i];

                        // check next argument as boolean flag value
                        if opt_value == "false" {
                            self.options.set(opt.name.to_string(), Value::Bool(false));
                        } else {
                            self.options.set(opt.name.to_string(), Value::Bool(true));
                        }
                        // try to consume next argument as value for boolean flag;
                        // do not consume argument if it is not "true" or "false"
                        if opt_value == "false" || opt_value == "true" {
                            i += 1;
                        }
                    }
                    CommandLineOptionKind::String => {
                        let (val, err) = validate_json_option_value(
                            opt,
                            &Value::Str(args[i].clone()),
                            None,
                            None,
                        );
                        if err.is_empty() {
                            self.options.set(opt.name.to_string(), val);
                        } else {
                            self.errors.extend(err);
                        }
                        i += 1;
                    }
                    CommandLineOptionKind::List => {
                        let (result, err) = parse_list_type_option(opt, &args[i]);
                        let result_empty = result.is_empty();
                        self.options.set(opt.name.to_string(), Value::List(result));
                        self.errors.extend(err.clone());
                        if !result_empty || !err.is_empty() {
                            i += 1;
                        }
                    }
                    CommandLineOptionKind::ListOrElement => {
                        // If not a primitive, the possible types are specified
                        // in what is effectively a map of options.
                        panic!("listOrElement not supported here");
                    }
                    _ => {
                        let (val, err) = convert_json_option_of_enum_type(
                            opt,
                            args[i].trim_matches(|c: char| tsc_stringutil::is_white_space_like(c)),
                            None,
                            None,
                        );
                        self.options.set(opt.name.to_string(), val);
                        self.errors.extend(err);
                        i += 1;
                    }
                }
            } else {
                self.options.set(opt.name.to_string(), Value::Null);
                i += 1;
            }
        }
        i
    }
}

/// `getInputOptionName` — removes at most two leading '-' from the input
/// string (`TrimPrefix(TrimPrefix(input, "-"), "-")`).
fn get_input_option_name(input: &str) -> String {
    let input = input.strip_prefix('-').unwrap_or(input);
    input.strip_prefix('-').unwrap_or(input).to_string()
}

/// `ParseCommandLine`.
pub fn parse_command_line(
    command_line: &[String],
    fs: &Arc<dyn Vfs>,
    current_directory: RootedDirectoryPath,
) -> ParsedCommandLine {
    let parser = parse_command_line_worker(
        compiler_options_did_you_mean_diagnostics(),
        command_line,
        Some(fs.clone()),
        current_directory.clone(),
    );
    let mut options = parser.options.clone();
    parsinghelpers::convert_to_options_with_absolute_paths(
        &mut options,
        crate::tsconfigparsing::command_line_compiler_options_map(),
        current_directory.clone(),
    );
    let mut compiler_options_target = CompilerOptions::default();
    convert_map_to_options(
        &options,
        &mut CompilerOptionsParser {
            compiler_options: &mut compiler_options_target,
            unresolved_paths: None,
        },
    );
    let case_sensitivity = fs.case_sensitivity();
    let mut result = new_parsed_command_line(
        compiler_options_target,
        parser
            .file_names
            .iter()
            .map(|file_name| tspath::to_rooted_file_path(file_name, &current_directory))
            .collect(),
        Vec::new(),
        current_directory,
        case_sensitivity,
    );
    result.root_file_names_for_diagnostics = parser.file_names;
    *result.errors.lock().unwrap_or_else(|e| e.into_inner()) = parser.errors;
    result.raw = Some(Value::Map(parser.options));
    result
}

/// `ParseBuildCommandLine`.
pub fn parse_build_command_line(
    command_line: &[String],
    fs: &Arc<dyn Vfs>,
    current_directory: RootedDirectoryPath,
) -> ParsedBuildCommandLine {
    let parser = parse_command_line_worker(
        build_options_did_you_mean_diagnostics(),
        command_line,
        Some(fs.clone()),
        current_directory.clone(),
    );
    let mut compiler_options = CompilerOptions::default();
    for (key, value) in parser.options.entries() {
        let build_option = build_name_map().get(key);
        let same_option = |a: Option<CommandLineOptionRef>, b: Option<CommandLineOptionRef>| matches!((a, b), (Some(x), Some(y)) if std::ptr::eq(x, y));
        if same_option(
            build_option,
            Some(crate::generated::declarations::tsc_build_option()),
        ) || same_option(build_option, compiler_name_map().get(key))
        {
            parsinghelpers::parse_compiler_options(key, value, &mut compiler_options);
        }
    }
    let mut build_options_target = tsc_core::options_generated::BuildOptions::default();
    convert_map_to_options(
        &parser.options,
        &mut BuildOptionsParser {
            build_options: &mut build_options_target,
        },
    );
    let mut result = ParsedBuildCommandLine {
        build_options: Some(build_options_target),
        compiler_options: Some(compiler_options),
        projects: parser.file_names,
        errors: parser.errors,
        raw: Some(Value::Map(parser.options)),
        current_directory,
        ..Default::default()
    };

    if result.projects.is_empty() {
        // tsc -b invoked with no extra arguments; act as if invoked with
        // "tsc -b ."
        result.projects.push(".".to_string());
    }

    // Nonsensical combinations
    if result
        .build_options
        .as_ref()
        .is_some_and(|o| o.clean.is_true())
        && result
            .build_options
            .as_ref()
            .is_some_and(|o| o.force.is_true())
    {
        result.errors.push(new_compiler_diagnostic(
            &diagnostics::Options_0_and_1_cannot_be_combined,
            &[Value::Str("clean".into()), Value::Str("force".into())],
        ));
    }
    if result
        .build_options
        .as_ref()
        .is_some_and(|o| o.clean.is_true())
        && result
            .build_options
            .as_ref()
            .is_some_and(|o| o.verbose.is_true())
    {
        result.errors.push(new_compiler_diagnostic(
            &diagnostics::Options_0_and_1_cannot_be_combined,
            &[Value::Str("clean".into()), Value::Str("verbose".into())],
        ));
    }
    if result
        .build_options
        .as_ref()
        .is_some_and(|o| o.clean.is_true())
        && result
            .compiler_options
            .as_ref()
            .is_some_and(|o| o.watch.is_true())
    {
        result.errors.push(new_compiler_diagnostic(
            &diagnostics::Options_0_and_1_cannot_be_combined,
            &[Value::Str("clean".into()), Value::Str("watch".into())],
        ));
    }
    if result
        .compiler_options
        .as_ref()
        .is_some_and(|o| o.watch.is_true())
        && result
            .build_options
            .as_ref()
            .is_some_and(|o| o.dry.is_true())
    {
        result.errors.push(new_compiler_diagnostic(
            &diagnostics::Options_0_and_1_cannot_be_combined,
            &[Value::Str("watch".into()), Value::Str("dry".into())],
        ));
    }

    result
}

/// `parseCommandLineWorker`.
fn parse_command_line_worker<'a>(
    parse_command_line_with_diagnostics: &'a ParseCommandLineWorkerDiagnostics,
    command_line: &[String],
    fs: Option<Arc<dyn Vfs>>,
    current_directory: RootedDirectoryPath,
) -> CommandLineParser<'a> {
    let mut parser = CommandLineParser {
        worker_diagnostics: parse_command_line_with_diagnostics,
        options_map: get_name_map_from_list((parse_command_line_with_diagnostics
            .did_you_mean
            .option_declarations)()),
        fs,
        current_directory,
        options: OrderedMap::new(),
        file_names: Vec::new(),
        errors: Vec::new(),
        response_file_stack: Set::new(),
    };
    parser.parse_strings(command_line);
    parser
}

/// `ParseListTypeOption`.
pub fn parse_list_type_option(
    opt: CommandLineOptionRef,
    value: &str,
) -> (Vec<Value>, Vec<DiagnosticRef>) {
    let value = value.trim();
    let mut errors = Vec::new();
    if value.starts_with('-') {
        return (Vec::new(), errors);
    }
    if opt.kind == CommandLineOptionKind::ListOrElement && !value.contains(',') {
        let (val, err) =
            validate_json_option_value(opt, &Value::Str(value.to_string()), None, None);
        if !err.is_empty() {
            return (Vec::new(), err);
        }
        return (vec![val], errors);
    }
    if value.is_empty() {
        return (Vec::new(), errors);
    }
    let values: Vec<&str> = value.split(',').collect();
    let elements_opt = opt.elements().expect("list option has elements");
    match elements_opt.kind {
        CommandLineOptionKind::String => {
            let elements: Vec<Value> = values
                .iter()
                .filter_map(|v| {
                    let (val, err) = validate_json_option_value(
                        elements_opt,
                        &Value::Str((*v).to_string()),
                        None,
                        None,
                    );
                    if err.is_empty() && val.as_str().is_some_and(|s| !s.is_empty()) {
                        Some(val)
                    } else {
                        errors.extend(err);
                        None
                    }
                })
                .collect();
            (elements, errors)
        }
        CommandLineOptionKind::Boolean
        | CommandLineOptionKind::Object
        | CommandLineOptionKind::Number => {
            // do nothing: only string and enum/object types currently allowed
            // as list entries
            // 				!!! we don't actually have number list options, so I
            // 				didn't implement number list parsing
            panic!(
                "List of {} is not yet supported.",
                elements_opt.kind.as_str()
            )
        }
        _ => {
            let result: Vec<Value> = values
                .iter()
                .filter_map(|v| {
                    let (val, err) = convert_json_option_of_enum_type(
                        elements_opt,
                        v.trim_matches(|c: char| tsc_stringutil::is_white_space_like(c)),
                        None,
                        None,
                    );
                    if err.is_empty() && val.as_str().is_some_and(|s| !s.is_empty()) {
                        Some(val)
                    } else {
                        errors.extend(err);
                        None
                    }
                })
                .collect();
            (result, errors)
        }
    }
}

/// `ParseCommandLineTestWorker` (export_test.go) — runs the parser and
/// returns its raw results for baseline comparison.
#[cfg(test)]
pub(crate) struct TestCommandLineParser {
    pub file_names: Vec<String>,
    pub options: OrderedMap<String, Value>,
    pub errors: Vec<DiagnosticRef>,
}

/// `ParseCommandLineTestWorker` (export_test.go) — `decls` empty means the
/// default compiler-options diagnostics.
#[cfg(test)]
pub(crate) fn parse_command_line_test_worker(
    decls: Vec<CommandLineOptionRef>,
    command_line: &[String],
    fs: Arc<dyn Vfs>,
    current_directory: RootedDirectoryPath,
) -> TestCommandLineParser {
    let custom;
    let worker_diagnostics = if decls.is_empty() {
        compiler_options_did_you_mean_diagnostics()
    } else {
        custom = crate::diagnostics::parse_command_line_worker_diagnostics_from_decls(decls);
        &custom
    };
    let parser = parse_command_line_worker(
        worker_diagnostics,
        command_line,
        Some(fs),
        current_directory,
    );
    TestCommandLineParser {
        file_names: parser.file_names,
        options: parser.options,
        errors: parser.errors,
    }
}
