// Ported from tsc/internal/testrunner/test_case_parser.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::convert::Infallible;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::TextPos;
use tsc_core::tristate::TS_TRUE;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::tsconfigparsing::{
    new_tsconfig_source_file_from_file_path, parse_json_source_file_config_file_content,
};
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, get_base_file_name};
use tsc_vfs::Vfs;

use crate::compiler_runner::src_folder;

/// `lineDelimiter` — Go splits on the regexp `\r?\n`: `\r\n` and lone `\n`
/// break lines, a lone `\r` does not. Keeping the trailing empty piece
/// matches `Split(code, -1)`.
fn split_lines(code: &str) -> Vec<&str> {
    let mut lines = Vec::new();
    let bytes = code.as_bytes();
    let mut start = 0usize;
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'\n' {
            let mut end = i;
            if end > start && bytes[end - 1] == b'\r' {
                end -= 1;
            }
            lines.push(&code[start..end]);
            start = i + 1;
        }
    }
    lines.push(&code[start..]);
    lines
}

/// `rawCompilerSettings` maps a compiler setting to its value as written in
/// the test file. For example, if a test file contains:
///
/// ```text
/// // @target: esnext, es2015
/// ```
///
/// Then the map will map "target" to "esnext, es2015".
pub type RawCompilerSettings = FxHashMap<String, String>;

/// `testUnit` — all the necessary information to turn a multi file test into
/// useful units for later compilation.
pub struct TestUnit {
    pub content: String,
    pub name: String,
}

/// `testCaseContent`.
#[derive(Default)]
pub struct TestCaseContent {
    pub test_unit_data: Vec<TestUnit>,
    pub ts_config: Option<ParsedCommandLine>,
    pub ts_config_file_unit_data: Option<TestUnit>,
    pub symlinks: FxHashMap<String, String>,
}

/// Go regexp `\s` is `[\t\n\f\r ]` — notably NOT `\v` and NOT unicode
/// `IsSpace`. (Only space/tab/\x0c/\r can appear in a post-split line.)
fn is_regex_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\x0c' | '\r' | '\n')
}

/// Go regexp `\w` is ASCII `[0-9A-Za-z_]`.
fn is_word_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// `optionRegex` — `(?m)^\/{2}\s*@(\w+)\s*:\s*([^\r\n]*)` applied per line,
/// which makes `^` trivial and `[,\r\n]` termination equivalent to "end of
/// the value at the first `\r`".
fn match_option_directive(line: &str) -> Option<(&str, &str)> {
    let rest = line.strip_prefix("//")?;
    let rest = rest.trim_start_matches(is_regex_space);
    let rest = rest.strip_prefix('@')?;
    let name_len = rest.find(|c| !is_word_char(c)).unwrap_or(rest.len());
    if name_len == 0 {
        return None;
    }
    let (name, rest) = rest.split_at(name_len);
    let rest = rest.trim_start_matches(is_regex_space);
    let rest = rest.strip_prefix(':')?;
    let rest = rest.trim_start_matches(is_regex_space);
    // `[^\r\n]*` — the value ends at the first `\r` or `\n`.
    let end = rest.find(['\r', '\n']).unwrap_or(rest.len());
    Some((name, &rest[..end]))
}

/// `linkRegex` — `(?m)^\/{2}\s*@link\s*:\s*([^\r\n]*)\s*->\s*([^\r\n]*)`.
/// The first group is greedy, so it extends to the last `->` on the line.
fn match_link_directive(line: &str) -> Option<(&str, &str)> {
    let rest = line.strip_prefix("//")?;
    let rest = rest.trim_start_matches(is_regex_space);
    let rest = rest.strip_prefix("@link")?;
    let rest = rest.trim_start_matches(is_regex_space);
    let rest = rest.strip_prefix(':')?;
    let rest = rest.trim_start_matches(is_regex_space);
    let end = rest.find(['\r', '\n']).unwrap_or(rest.len());
    let rest = &rest[..end];
    let arrow = rest.rfind("->")?;
    Some((
        rest[..arrow].trim_end_matches(is_regex_space),
        rest[arrow + 2..].trim_start_matches(is_regex_space),
    ))
}

/// `fourslashDirectives` — file-specific directives used by fourslash tests.
const FOURSLASH_DIRECTIVES: [&str; 2] = ["emitthisfile", "noopen"];

/// `makeUnitsFromTest` — given a test file containing `// @FileName`
/// directives, return an array of named units of code to be added to an
/// existing compiler instance.
pub fn make_units_from_test(code: &str, file_name: &str) -> TestCaseContent {
    let parsed = parse_test_files_and_symlinks(code, file_name, |filename, content, _| {
        Ok::<_, Infallible>(TestUnit {
            content: content.to_string(),
            name: filename.to_string(),
        })
    });
    let mut test_units = parsed.units;
    let symlinks = parsed.symlinks;
    let raw_current_directory = parsed.current_dir;
    let global_options = parsed.global_options;

    let mut current_directory = src_folder().clone();
    if !raw_current_directory.is_empty() {
        current_directory =
            tsc_tspath::to_rooted_directory_path(&raw_current_directory, src_folder());
    }

    // unit tests always list files explicitly
    let mut all_files: FxHashMap<String, String> = FxHashMap::default();
    for data in &test_units {
        all_files.insert(
            tsc_tspath::to_rooted_file_path(&data.name, &current_directory)
                .as_string()
                .to_string(),
            data.content.clone(),
        );
    }
    let config_fs = new_vfs_with_symlinks(
        &all_files,
        &symlinks,
        &current_directory,
        CaseSensitivity::CaseSensitive,
    );

    // Content mappers are gated behind --runExternalCode, a command-line-only
    // option. A test opts in with a top-level `// @runExternalCode: true`,
    // which we surface to the config parse as an existing option so the gate
    // passes and the mappers register.
    let existing_options =
        if global_options.get("runexternalcode").map(String::as_str) == Some("true") {
            Some(CompilerOptions {
                run_external_code: TS_TRUE,
                ..Default::default()
            })
        } else {
            None
        };

    // check if project has tsconfig.json in the list of files
    let mut ts_config: Option<ParsedCommandLine> = None;
    let mut ts_config_file_unit_data: Option<TestUnit> = None;
    let config_index = test_units
        .iter()
        .position(|data| !get_config_name_from_file_name(&data.name).is_empty());
    if let Some(i) = config_index {
        {
            let data = &test_units[i];
            let config_file_name = tsc_tspath::to_rooted_file_path(&data.name, &current_directory);
            let path = config_fs
                .case_sensitivity()
                .path_key(&config_file_name.as_path());
            let ts_config_source_file = Arc::new(new_tsconfig_source_file_from_file_path(
                config_file_name.clone(),
                path,
                &data.content,
            ));
            let config_dir = config_file_name.directory();
            ts_config = Some(parse_json_source_file_config_file_content(
                &ts_config_source_file,
                &config_fs,
                config_dir,
                existing_options.as_ref(),
                None, /*existing_options_raw*/
                &[],  /*resolution_stack*/
                None, /*extended_config_cache*/
            ));
        }

        // delete tsconfig file entry from the list
        ts_config_file_unit_data = Some(test_units.remove(i));
    }

    TestCaseContent {
        test_unit_data: test_units,
        ts_config,
        ts_config_file_unit_data,
        symlinks,
    }
}

/// `ParseTestFilesOptions`.
#[derive(Default)]
pub struct ParseTestFilesOptions {
    /// If true, allows test content to appear before the first `@Filename`
    /// directive. In this case, an implicit first file is created using the
    /// `file_name` parameter. This matches the behavior of the TypeScript
    /// fourslash test harness.
    pub allow_implicit_first_file: bool,
}

/// `ParseTestFilesAndSymlinks`' five-value return as a struct.
pub struct ParsedTestFiles<T, E> {
    pub units: Vec<T>,
    pub symlinks: FxHashMap<String, String>,
    pub current_dir: String,
    pub global_options: FxHashMap<String, String>,
    /// Go's `error` return — `None` mirrors nil.
    pub error: Option<E>,
}

/// `ParseTestFilesAndSymlinks` — given a test file containing `// @FileName`
/// and `// @symlink` directives, return an array of named units of code to be
/// added to an existing compiler instance, along with a map of symlinks and
/// the current directory.
pub fn parse_test_files_and_symlinks<T, E>(
    code: &str,
    file_name: &str,
    parse_file: impl FnMut(&str, &str, &FxHashMap<String, String>) -> Result<T, E>,
) -> ParsedTestFiles<T, E> {
    parse_test_files_and_symlinks_with_options(
        code,
        file_name,
        parse_file,
        &ParseTestFilesOptions::default(),
    )
}

/// `ParseTestFilesAndSymlinksWithOptions`.
pub fn parse_test_files_and_symlinks_with_options<T, E>(
    code: &str,
    file_name: &str,
    mut parse_file: impl FnMut(&str, &str, &FxHashMap<String, String>) -> Result<T, E>,
    options: &ParseTestFilesOptions,
) -> ParsedTestFiles<T, E> {
    // List of all the subfiles we've parsed out
    let mut test_units: Vec<T> = Vec::new();

    let lines = split_lines(code);

    // Stuff related to the subfile we're parsing
    let mut current_file_content = String::new();
    let mut current_file_name = String::new();
    let mut seen_content_line = false;
    let mut has_seen_file = false;
    if options.allow_implicit_first_file {
        // For fourslash tests, initialize currentFileName to the fileName
        // parameter so content before the first @Filename directive goes into
        // an implicit first file
        current_file_name = file_name.to_string();
    }
    let mut current_directory = String::new();
    let mut parse_error: Option<E> = None;
    let mut current_file_options: FxHashMap<String, String> = FxHashMap::default();
    let mut symlinks: FxHashMap<String, String> = FxHashMap::default();
    let mut global_options: FxHashMap<String, String> = FxHashMap::default();

    'lines: for line in lines {
        if parse_symlink_from_test(line, &mut symlinks) {
            continue;
        }
        if let Some((raw_name, raw_value)) = match_option_directive(line) {
            // Comment line, check for global/file @options and record them
            let meta_data_name = raw_name.to_lowercase();
            let meta_data_value = raw_value.trim();
            if meta_data_name == "currentdirectory" {
                current_directory = meta_data_value.to_string();
            }
            if meta_data_name != "filename" {
                if meta_data_name == "symlink" && !current_file_name.is_empty() {
                    for link in meta_data_value.split(',') {
                        let link = link.trim();
                        if !link.is_empty() {
                            symlinks.insert(link.to_string(), current_file_name.clone());
                        }
                    }
                } else if FOURSLASH_DIRECTIVES.contains(&meta_data_name.as_str()) {
                    // File-specific option
                    current_file_options
                        .insert(meta_data_name.clone(), meta_data_value.to_string());
                } else {
                    // Global option
                    if let Some(existing_value) = global_options.get(&meta_data_name)
                        && *existing_value != meta_data_value
                    {
                        // !!! This would break existing baseline tests
                        // panic!("Duplicate global option: {meta_data_name}")
                    }
                    global_options.insert(meta_data_name.clone(), meta_data_value.to_string());
                }
                continue;
            }

            // New metadata statement after having collected some code to go
            // with the previous metadata
            if !current_file_name.is_empty() {
                // Store result file - always save for regular tests, but skip
                // empty implicit first file for fourslash
                let should_save_file = !options.allow_implicit_first_file
                    || !current_file_content.is_empty()
                    || has_seen_file;
                if should_save_file {
                    has_seen_file = true;
                    match parse_file(
                        &current_file_name,
                        &current_file_content,
                        &current_file_options,
                    ) {
                        Ok(new_test_file) => test_units.push(new_test_file),
                        Err(e) => {
                            parse_error = Some(e);
                            break 'lines;
                        }
                    }
                }

                // Reset local data
                current_file_content.clear();
                seen_content_line = false;
                current_file_name = meta_data_value.to_string();
                current_file_options = FxHashMap::default();
            } else {
                // First metadata marker in the file
                let has_content_before_first_filename = !current_file_content.is_empty()
                    && tsc_scanner::scanner::skip_trivia(&current_file_content, 0)
                        != current_file_content.len() as TextPos;
                if has_content_before_first_filename && !options.allow_implicit_first_file {
                    panic!(
                        "Non-comment test content appears before the first '// @Filename' directive"
                    );
                }

                // If we have content before the first @Filename and
                // AllowImplicitFirstFile is true, we need to save it as an
                // implicit first file before starting the new file
                if has_content_before_first_filename
                    && options.allow_implicit_first_file
                    && !current_file_name.is_empty()
                {
                    // Store the implicit first file
                    has_seen_file = true;
                    match parse_file(
                        &current_file_name,
                        &current_file_content,
                        &current_file_options,
                    ) {
                        Ok(new_test_file) => test_units.push(new_test_file),
                        Err(e) => {
                            parse_error = Some(e);
                            break 'lines;
                        }
                    }
                }

                // Reset for the new file
                current_file_content.clear();
                seen_content_line = false;
                current_file_name = meta_data_value.to_string();
                current_file_options = FxHashMap::default();
            }
        } else {
            // Subfile content line
            // Append to the current subfile content, inserting a newline if
            // needed. For fourslash tests, use seen_content_line to preserve
            // leading blank lines (matching TS fourslash's //// content
            // markers). For compiler tests, use !is_empty which drops leading
            // blanks (matching TS's harness behavior).
            if options.allow_implicit_first_file {
                if seen_content_line {
                    current_file_content.push('\n');
                }
                seen_content_line = true;
            } else if !current_file_content.is_empty() {
                current_file_content.push('\n');
            }
            current_file_content.push_str(line);
        }
    }

    // normalize the fileName for the single file case
    if test_units.is_empty() && current_file_name.is_empty() {
        current_file_name = get_base_file_name(file_name).into_owned();
    }

    // if there are no parse errors so far, parse the rest of the file
    if parse_error.is_none() {
        // EOF, push whatever remains
        match parse_file(
            &current_file_name,
            &current_file_content,
            &current_file_options,
        ) {
            Ok(new_test_file) => test_units.push(new_test_file),
            Err(e) => parse_error = Some(e),
        }
    }

    ParsedTestFiles {
        units: test_units,
        symlinks,
        current_dir: current_directory,
        global_options,
        error: parse_error,
    }
}

/// `extractCompilerSettings`.
pub fn extract_compiler_settings(content: &str) -> RawCompilerSettings {
    let mut opts = FxHashMap::default();

    for line in split_lines(content) {
        if let Some((name, value)) = match_option_directive(line) {
            let trimmed = value.trim();
            let trimmed = trimmed.strip_suffix(';').unwrap_or(trimmed);
            opts.insert(name.to_lowercase(), trimmed.to_string());
        }
    }

    opts
}

/// `parseSymlinkFromTest`.
fn parse_symlink_from_test(line: &str, symlinks: &mut FxHashMap<String, String>) -> bool {
    let Some((target, link)) = match_link_directive(line) else {
        return false;
    };

    symlinks.insert(link.trim().to_string(), target.trim().to_string());
    true
}

/// `harnessutil.GetConfigNameFromFileName`.
///
/// PORT(deferred): `tsc_testutil::harnessutil` is still being ported; this
/// inline copy of the 5-line basename check keeps `make_units_from_test`
/// compiling. Replace with `tsc_testutil::harnessutil::get_config_name_from_file_name`
/// when it lands.
fn get_config_name_from_file_name(filename: &str) -> String {
    let basename_lower = get_base_file_name(filename).to_lowercase();
    if basename_lower == "tsconfig.json" || basename_lower == "jsconfig.json" {
        return basename_lower;
    }
    String::new()
}

/// `tsoptionstest.NewVFSWithSymlinks` — builds a VFS that contains the given
/// symlinks (link path -> target path).
///
/// PORT(deferred): `tsc_tsoptions::tsoptionstest` (Go `tsoptions/tsoptionstest`)
/// is still being ported; this inline equivalent via `tsc_vfs::vfstest`
/// keeps `make_units_from_test` compiling. Replace with
/// `tsc_tsoptions::tsoptionstest::new_vfs_with_symlinks` when it lands.
fn new_vfs_with_symlinks(
    files: &FxHashMap<String, String>,
    symlinks: &FxHashMap<String, String>,
    current_directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> Arc<dyn Vfs> {
    if symlinks.is_empty() {
        return tsc_vfs::vfstest::from_map(
            files.iter().map(|(k, v)| (k.clone(), v.clone())),
            case_sensitivity,
        );
    }
    let mut entries: FxHashMap<String, tsc_vfs::vfstest::TestFile> = FxHashMap::default();
    for (name, content) in files {
        entries.insert(name.clone(), content.clone().into());
    }
    for (link, target) in symlinks {
        entries.insert(
            tsc_tspath::get_normalized_absolute_path(link, current_directory).into_owned(),
            tsc_vfs::vfstest::symlink(&tsc_tspath::get_normalized_absolute_path(
                target,
                current_directory,
            ))
            .into(),
        );
    }
    tsc_vfs::vfstest::from_map(entries, case_sensitivity)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `TestMakeUnitsFromTest`.
    #[test]
    fn make_units_from_test_splits_files() {
        let code = r#"// @strict: true
// @noEmit: true
// @filename: firstFile.ts
function foo() { return "a"; }
// normal comment
// @filename: secondFile.ts
// some other comment
function bar() { return "b"; }"#;
        let content = make_units_from_test(code, "simpleTest.ts");
        assert!(content.ts_config.is_none());
        assert!(content.ts_config_file_unit_data.is_none());
        assert!(content.symlinks.is_empty());
        assert_eq!(content.test_unit_data.len(), 2);
        assert_eq!(content.test_unit_data[0].name, "firstFile.ts");
        assert_eq!(
            content.test_unit_data[0].content,
            "function foo() { return \"a\"; }\n// normal comment",
        );
        assert_eq!(content.test_unit_data[1].name, "secondFile.ts");
        assert_eq!(
            content.test_unit_data[1].content,
            "// some other comment\nfunction bar() { return \"b\"; }",
        );
    }
}
