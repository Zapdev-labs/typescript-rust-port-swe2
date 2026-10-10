// Ported from tsc/internal/execute/tsc/help.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_collections::OrderedMap;
use tsc_core::tristate::TS_UNKNOWN;
use tsc_core::version::version;
use tsc_locale::Locale;
use tsc_tsoptions::commandlineoption::{
    CommandLineOption, CommandLineOptionKind, CommandLineOptionRef, DefaultValueDescription,
};
use tsc_tsoptions::generated::declarations;
use tsc_tsoptions::value::Value;

use crate::tsc::compile::System;
use crate::tsc::diagnostics::{Colors, create_colors};

/// `PrintVersion`.
pub fn print_version(sys: &Arc<dyn System>, locale: &Locale) {
    let w = sys.writer();
    let _ = writeln!(
        w.guard(),
        "{}",
        tsc_diagnostics::Version_0.localize(locale, &[version()])
    );
}

/// `PrintHelp`.
pub fn print_help(
    sys: &Arc<dyn System>,
    locale: &Locale,
    command_line: &tsc_tsoptions::parsedcommandline::ParsedCommandLine,
) {
    let all = command_line
        .compiler_options()
        .map(|o| o.all.is_true())
        .unwrap_or(false);
    if !all {
        print_easy_help(sys, locale, &get_options_for_help(command_line));
    } else {
        print_all_help(sys, locale, &get_options_for_help(command_line));
    }
}

/// `getOptionsForHelp`.
fn get_options_for_help(
    command_line: &tsc_tsoptions::parsedcommandline::ParsedCommandLine,
) -> Vec<CommandLineOptionRef> {
    // Sort our options by their names, (e.g. "--noImplicitAny" comes before "--watch")
    let mut opts: Vec<CommandLineOptionRef> = declarations::options_declarations().collect();
    opts.push(declarations::tsc_build_option());

    if command_line
        .compiler_options()
        .map(|o| o.all.is_true())
        .unwrap_or(false)
    {
        opts.sort_by(|a, b| a.name.to_lowercase().cmp(&b.name.to_lowercase()));
        opts
    } else {
        opts.into_iter()
            .filter(|opt| opt.show_in_simplified_help_view)
            .collect()
    }
}

/// `getHeader`.
pub(crate) fn get_header(sys: &Arc<dyn System>, message: &str) -> Vec<String> {
    let colors = create_colors(sys.as_ref());
    let mut header: Vec<String> = Vec::with_capacity(3);
    let terminal_width = sys.width_of_terminal();
    const TS_ICON: &str = "     ";
    const TS_ICON_TS: &str = "  TS ";
    let ts_icon_length = TS_ICON.len();

    let ts_icon_first_line = colors.blue_background(TS_ICON);
    let ts_icon_second_line = colors.blue_background(&colors.bright_white(TS_ICON_TS));
    // If we have enough space, print TS icon.
    if terminal_width >= message.len() + ts_icon_length {
        // right align of the icon is 120 at most.
        let right_align = if terminal_width > 120 {
            120
        } else {
            terminal_width
        };
        let left_align = right_align - ts_icon_length;
        header.push(format!("{message:<left_align$}"));
        header.push(ts_icon_first_line);
        header.push("\n".to_string());
        header.push(" ".repeat(left_align));
        header.push(ts_icon_second_line);
        header.push("\n".to_string());
    } else {
        header.push(message.to_string());
        header.push("\n".to_string());
        header.push("\n".to_string());
    }
    header
}

/// `printEasyHelp`.
fn print_easy_help(
    sys: &Arc<dyn System>,
    locale: &Locale,
    simple_options: &[CommandLineOptionRef],
) {
    let colors = create_colors(sys.as_ref());
    let mut output: Vec<String> = Vec::new();
    // `output` is a parameter (not a capture) so the pushes below don't
    // collide with the closure's borrow.
    let example =
        |output: &mut Vec<String>, examples: &[&str], desc: &'static tsc_diagnostics::Message| {
            for example in examples {
                output.push("  ".to_string());
                output.push(colors.blue(example));
                output.push("\n".to_string());
            }
            output.push("  ".to_string());
            output.push(desc.localize(locale, &[] as &[String]));
            output.push("\n".to_string());
            output.push("\n".to_string());
        };

    let msg = tsc_diagnostics::X_tsc_Colon_The_TypeScript_Compiler
        .localize(locale, &[] as &[String])
        + " - "
        + &tsc_diagnostics::Version_0.localize(locale, &[version()]);
    output.extend(get_header(sys, &msg));

    output.push(colors.bold(&tsc_diagnostics::COMMON_COMMANDS.localize(locale, &[] as &[String])));
    output.push("\n".to_string());
    output.push("\n".to_string());

    example(
        &mut output,
        &["tsc"],
        &tsc_diagnostics::Compiles_the_current_project_tsconfig_json_in_the_working_directory,
    );
    example(
        &mut output,
        &["tsc app.ts util.ts"],
        &tsc_diagnostics::Ignoring_tsconfig_json_compiles_the_specified_files_with_default_compiler_options,
    );
    example(
        &mut output,
        &["tsc -b"],
        &tsc_diagnostics::Build_a_composite_project_in_the_working_directory,
    );
    example(
        &mut output,
        &["tsc --init"],
        &tsc_diagnostics::Creates_a_tsconfig_json_with_the_recommended_settings_in_the_working_directory,
    );
    example(
        &mut output,
        &["tsc -p ./path/to/tsconfig.json"],
        &tsc_diagnostics::Compiles_the_TypeScript_project_located_at_the_specified_path,
    );
    example(
        &mut output,
        &["tsc --help --all"],
        &tsc_diagnostics::An_expanded_version_of_this_information_showing_all_possible_compiler_options,
    );
    example(
        &mut output,
        &["tsc --noEmit", "tsc --target esnext"],
        &tsc_diagnostics::Compiles_the_current_project_with_additional_settings,
    );

    let mut cli_commands: Vec<CommandLineOptionRef> = Vec::new();
    let mut config_opts: Vec<CommandLineOptionRef> = Vec::new();
    for &opt in simple_options {
        if opt.is_command_line_only
            || opt
                .category
                .is_some_and(|c| std::ptr::eq(c, &tsc_diagnostics::Command_line_Options))
        {
            cli_commands.push(opt);
        } else {
            config_opts.push(opt);
        }
    }

    output.extend(generate_section_options_output(
        sys,
        locale,
        &tsc_diagnostics::COMMAND_LINE_FLAGS.localize(locale, &[] as &[String]),
        &cli_commands,
        false, // subCategory
        None,  // beforeOptionsDescription
        None,  // afterOptionsDescription
    ));

    let after = tsc_diagnostics::You_can_learn_about_all_of_the_compiler_options_at_0
        .localize(locale, &["https://aka.ms/tsc"]);
    output.extend(generate_section_options_output(
        sys,
        locale,
        &tsc_diagnostics::COMMON_COMPILER_OPTIONS.localize(locale, &[] as &[String]),
        &config_opts,
        false,
        None,
        Some(&after),
    ));

    let w = sys.writer();
    for chunk in &output {
        w.write_text(chunk);
    }
}

/// `printAllHelp`.
fn print_all_help(sys: &Arc<dyn System>, locale: &Locale, options: &[CommandLineOptionRef]) {
    let mut output: Vec<String> = Vec::new();
    let msg = tsc_diagnostics::X_tsc_Colon_The_TypeScript_Compiler
        .localize(locale, &[] as &[String])
        + " - "
        + &tsc_diagnostics::Version_0.localize(locale, &[version()]);
    output.extend(get_header(sys, &msg));

    // ALL COMPILER OPTIONS section
    let after_compiler_options =
        tsc_diagnostics::You_can_learn_about_all_of_the_compiler_options_at_0
            .localize(locale, &["https://aka.ms/tsc"]);
    output.extend(generate_section_options_output(
        sys,
        locale,
        &tsc_diagnostics::ALL_COMPILER_OPTIONS.localize(locale, &[] as &[String]),
        options,
        true,
        None,
        Some(&after_compiler_options),
    ));

    // BUILD OPTIONS section
    let before_build_options = tsc_diagnostics::Using_build_b_will_make_tsc_behave_more_like_a_build_orchestrator_than_a_compiler_This_is_used_to_trigger_building_composite_projects_which_you_can_learn_more_about_at_0
        .localize(locale, &["https://aka.ms/tsc-composite-builds"]);
    let build_options: Vec<CommandLineOptionRef> = declarations::OPTIONS_FOR_BUILD
        .iter()
        .copied()
        .filter(|option| !std::ptr::eq(*option, declarations::tsc_build_option()))
        .collect();
    output.extend(generate_section_options_output(
        sys,
        locale,
        &tsc_diagnostics::BUILD_OPTIONS.localize(locale, &[] as &[String]),
        &build_options,
        false,
        Some(&before_build_options),
        None,
    ));

    let w = sys.writer();
    for chunk in &output {
        w.write_text(chunk);
    }
}

/// `PrintBuildHelp`.
pub fn print_build_help(
    sys: &Arc<dyn System>,
    locale: &Locale,
    build_options: &[CommandLineOptionRef],
) {
    let mut output: Vec<String> = Vec::new();
    let msg = tsc_diagnostics::X_tsc_Colon_The_TypeScript_Compiler
        .localize(locale, &[] as &[String])
        + " - "
        + &tsc_diagnostics::Version_0.localize(locale, &[version()]);
    output.extend(get_header(sys, &msg));
    let before = tsc_diagnostics::Using_build_b_will_make_tsc_behave_more_like_a_build_orchestrator_than_a_compiler_This_is_used_to_trigger_building_composite_projects_which_you_can_learn_more_about_at_0
        .localize(locale, &["https://aka.ms/tsc-composite-builds"]);
    let options: Vec<CommandLineOptionRef> = build_options
        .iter()
        .copied()
        .filter(|option| !std::ptr::eq(*option, declarations::tsc_build_option()))
        .collect();
    output.extend(generate_section_options_output(
        sys,
        locale,
        &tsc_diagnostics::BUILD_OPTIONS.localize(locale, &[] as &[String]),
        &options,
        false,
        Some(&before),
        None,
    ));

    let w = sys.writer();
    for chunk in &output {
        w.write_text(chunk);
    }
}

/// `generateSectionOptionsOutput`.
#[allow(clippy::too_many_arguments)]
fn generate_section_options_output(
    sys: &Arc<dyn System>,
    locale: &Locale,
    section_name: &str,
    options: &[CommandLineOptionRef],
    sub_category: bool,
    before_options_description: Option<&str>,
    after_options_description: Option<&str>,
) -> Vec<String> {
    let mut output: Vec<String> = vec![
        create_colors(sys.as_ref()).bold(section_name),
        "\n".to_string(),
        "\n".to_string(),
    ];

    if let Some(before) = before_options_description {
        output.push(before.to_string());
        output.push("\n".to_string());
        output.push("\n".to_string());
    }
    if !sub_category {
        output.extend(generate_group_option_output(sys, locale, options));
        if let Some(after) = after_options_description {
            output.push(after.to_string());
            output.push("\n".to_string());
            output.push("\n".to_string());
        }
        return output;
    }
    let mut category_map: std::collections::HashMap<String, Vec<CommandLineOptionRef>> =
        std::collections::HashMap::new();
    let mut category_order: Vec<String> = Vec::new();
    for &option in options {
        let Some(category) = option.category else {
            continue;
        };
        let cur_category = category.localize(locale, &[] as &[String]);
        category_map
            .entry(cur_category.clone())
            .or_insert_with(|| {
                category_order.push(cur_category.clone());
                Vec::new()
            })
            .push(option);
    }
    for key in &category_order {
        let value = &category_map[key];
        output.push("### ".to_string());
        output.push(key.clone());
        output.push("\n".to_string());
        output.push("\n".to_string());
        output.extend(generate_group_option_output(sys, locale, value));
    }
    if let Some(after) = after_options_description {
        output.push(after.to_string());
        output.push("\n".to_string());
        output.push("\n".to_string());
    }

    output
}

/// `generateGroupOptionOutput`.
fn generate_group_option_output(
    sys: &Arc<dyn System>,
    locale: &Locale,
    options_list: &[CommandLineOptionRef],
) -> Vec<String> {
    let mut max_length = 0usize;
    for option in options_list {
        let cur_length = get_display_name_text_of_option(option).len();
        max_length = cur_length.max(max_length);
    }

    // left part should be right align, right part should be left align

    // assume 2 space between left margin and left part.
    let right_align_of_left_part = max_length + 2;
    // assume 2 space between left and right part
    let left_align_of_right_part = right_align_of_left_part + 2;

    let mut lines: Vec<String> = Vec::new();
    for option in options_list {
        lines.extend(generate_option_output(
            sys,
            locale,
            option,
            right_align_of_left_part,
            left_align_of_right_part,
        ));
    }

    // make sure always a blank line in the end.
    if lines.len() < 2 || lines[lines.len() - 2] != "\n" {
        lines.push("\n".to_string());
    }

    lines
}

/// `generateOptionOutput`.
fn generate_option_output(
    sys: &Arc<dyn System>,
    locale: &Locale,
    option: CommandLineOptionRef,
    right_align_of_left: usize,
    left_align_of_right: usize,
) -> Vec<String> {
    let mut text: Vec<String> = Vec::new();
    let colors = create_colors(sys.as_ref());

    // name and description
    let name = get_display_name_text_of_option(option);

    // value type and possible value
    let value_candidates = get_value_candidate(locale, option);

    let default_value_description = match option.default_value_description {
        DefaultValueDescription::Message(msg) => msg.localize(locale, &[] as &[String]),
        _ => format_default_value(
            &option.default_value_description,
            if option.kind == CommandLineOptionKind::List
                || option.kind == CommandLineOptionKind::ListOrElement
            {
                option.elements()
            } else {
                Some(option)
            },
        ),
    };

    let terminal_width = sys.width_of_terminal();

    if terminal_width >= 80 {
        let description = option
            .description
            .map(|d| d.localize(locale, &[] as &[String]))
            .unwrap_or_default();
        text.extend(get_pretty_output(
            &colors,
            &name,
            &description,
            right_align_of_left,
            left_align_of_right,
            terminal_width,
            true, // colorLeft
        ));
        text.push("\n".to_string());
        if show_additional_info_output(value_candidates.as_ref(), option) {
            if let Some(candidates) = &value_candidates {
                text.extend(get_pretty_output(
                    &colors,
                    &candidates.value_type,
                    &candidates.possible_values,
                    right_align_of_left,
                    left_align_of_right,
                    terminal_width,
                    false, // colorLeft
                ));
                text.push("\n".to_string());
            }
            if !default_value_description.is_empty() {
                text.extend(get_pretty_output(
                    &colors,
                    &tsc_diagnostics::X_default_Colon.localize(locale, &[] as &[String]),
                    &default_value_description,
                    right_align_of_left,
                    left_align_of_right,
                    terminal_width,
                    false, // colorLeft
                ));
                text.push("\n".to_string());
            }
        }
        text.push("\n".to_string());
    } else {
        text.push(colors.blue(&name));
        text.push("\n".to_string());
        if let Some(description) = option.description {
            text.push(description.localize(locale, &[] as &[String]));
        }
        text.push("\n".to_string());
        if show_additional_info_output(value_candidates.as_ref(), option) {
            if let Some(candidates) = &value_candidates {
                text.push(candidates.value_type.clone());
                text.push(" ".to_string());
                text.push(candidates.possible_values.clone());
            }
            if !default_value_description.is_empty() {
                if value_candidates.is_some() {
                    text.push("\n".to_string());
                }
                text.push(tsc_diagnostics::X_default_Colon.localize(locale, &[] as &[String]));
                text.push(" ".to_string());
                text.push(default_value_description);
            }

            text.push("\n".to_string());
        }
        text.push("\n".to_string());
    }

    text
}

/// `formatDefaultValue`.
fn format_default_value(
    default_value: &DefaultValueDescription,
    option: Option<CommandLineOptionRef>,
) -> String {
    let is_undefined = matches!(default_value, DefaultValueDescription::None)
        || matches!(
            default_value,
            DefaultValueDescription::Tristate(t) if *t == TS_UNKNOWN
        );
    if is_undefined {
        return "undefined".to_string();
    }

    if let Some(option) = option
        && option.kind == CommandLineOptionKind::Enum
    {
        // e.g. ScriptTarget.ES2015 -> "es6/es2015"
        let value = default_value_to_value(default_value);
        let mut names: Vec<String> = Vec::new();
        if let Some(enum_map) = option.enum_map() {
            for (name, v) in enum_map.entries() {
                if Some(v) == value.as_ref() {
                    names.push(name.clone());
                }
            }
        }
        return names.join("/");
    }
    format_default_value_display(default_value)
}

/// `DefaultValueDescription` → the `Value` it would compare equal to in an
/// enum map (`fmt.Sprintf("%v", defaultValue)`'s enum-name lookup).
fn default_value_to_value(default_value: &DefaultValueDescription) -> Option<Value> {
    match default_value {
        DefaultValueDescription::Number(n) => Some(Value::Int(*n)),
        DefaultValueDescription::ScriptTarget(t) => Some(Value::Int(*t as i64)),
        _ => None,
    }
}

/// `fmt.Sprintf("%v", defaultValue)` for the non-enum case.
fn format_default_value_display(default_value: &DefaultValueDescription) -> String {
    match default_value {
        DefaultValueDescription::None => "undefined".to_string(),
        DefaultValueDescription::Bool(b) => b.to_string(),
        DefaultValueDescription::Str(s) => s.to_string(),
        DefaultValueDescription::Number(n) => n.to_string(),
        DefaultValueDescription::Message(m) => {
            m.localize(&tsc_locale::Locale::default(), &[] as &[String])
        }
        DefaultValueDescription::Tristate(t) => t.to_string(),
        DefaultValueDescription::ScriptTarget(t) => t.to_string(),
    }
}

/// `type valueCandidate struct`.
pub(crate) struct ValueCandidate {
    /// "one or more" or "any of"
    pub value_type: String,
    pub possible_values: String,
}

/// `showAdditionalInfoOutput`.
fn show_additional_info_output(
    value_candidates: Option<&ValueCandidate>,
    option: &CommandLineOption,
) -> bool {
    if option
        .category
        .is_some_and(|c| std::ptr::eq(c, &tsc_diagnostics::Command_line_Options))
    {
        return false;
    }
    if let Some(candidates) = value_candidates
        && candidates.possible_values == "string"
        && matches!(
            option.default_value_description,
            DefaultValueDescription::None
                | DefaultValueDescription::Bool(false)
                | DefaultValueDescription::Str("n/a")
        )
    {
        return false;
    }
    true
}

/// `getValueCandidate`.
fn get_value_candidate(locale: &Locale, option: &CommandLineOption) -> Option<ValueCandidate> {
    // option.type might be "string" | "number" | "boolean" | "object" | "list" | Map<string, number | string>
    // string -- any of: string
    // number -- any of: number
    // boolean -- any of: boolean
    // object -- null
    // list -- one or more: , content depends on `option.element.type`, the same as others
    // Map<string, number | string> -- any of: key1, key2, ....
    if option.kind == CommandLineOptionKind::Object {
        return None;
    }

    if option.kind == CommandLineOptionKind::ListOrElement {
        // assert(option.type !== "listOrElement")
        panic!("no value candidate for list or element");
    }

    let value_type = match option.kind {
        CommandLineOptionKind::String
        | CommandLineOptionKind::Number
        | CommandLineOptionKind::Boolean => {
            tsc_diagnostics::X_type_Colon.localize(locale, &[] as &[String])
        }
        CommandLineOptionKind::List => {
            tsc_diagnostics::X_one_or_more_Colon.localize(locale, &[] as &[String])
        }
        _ => tsc_diagnostics::X_one_of_Colon.localize(locale, &[] as &[String]),
    };

    Some(ValueCandidate {
        value_type,
        possible_values: get_possible_values(option),
    })
}

/// `getPossibleValues`.
fn get_possible_values(option: &CommandLineOption) -> String {
    match option.kind {
        CommandLineOptionKind::String
        | CommandLineOptionKind::Number
        | CommandLineOptionKind::Boolean => option.kind.as_str().to_string(),
        CommandLineOptionKind::List | CommandLineOptionKind::ListOrElement => {
            get_possible_values(option.elements().expect("elements"))
        }
        CommandLineOptionKind::Object => String::new(),
        CommandLineOptionKind::Enum => {
            // Map<string, number | string>
            // Group synonyms: es6/es2015
            let enum_map = option.enum_map().expect("enum_map");
            // PORT: `OrderedMap[any, []string]` — `Value` is not `Hash+Eq`,
            // so the grouping key is its `Debug` string (equal values have
            // equal representations).
            let mut inverted: OrderedMap<String, Vec<String>> =
                OrderedMap::with_size_hint(enum_map.size());
            let deprecated_keys = option.deprecated_keys();

            for (name, value) in enum_map.entries() {
                if deprecated_keys.is_none_or(|keys| !keys.has(name)) {
                    let key = format!("{value:?}");
                    match inverted.get_mut(&key) {
                        Some(entry) => entry.push(name.clone()),
                        None => inverted.set(key, vec![name.clone()]),
                    }
                }
            }
            let syns: Vec<String> = inverted
                .values()
                .map(|synonyms| synonyms.join("/"))
                .collect();
            syns.join(", ")
        }
    }
}

/// `getPrettyOutput`.
fn get_pretty_output(
    colors: &Colors,
    left: &str,
    right: &str,
    right_align_of_left: usize,
    left_align_of_right: usize,
    terminal_width: usize,
    color_left: bool,
) -> Vec<String> {
    // !!! How does terminalWidth interact with UTF-8 encoding? Strada just assumed UTF-16.
    let mut res: Vec<String> = Vec::with_capacity(4);
    let mut is_first_line = true;
    let mut remain_right = right;
    let right_character_number = terminal_width - left_align_of_right;
    while !remain_right.is_empty() {
        let cur_left = if is_first_line {
            let mut cur_left = format!("{left:>right_align_of_left$}");
            cur_left = format!("{cur_left:<left_align_of_right$}");
            if color_left {
                cur_left = colors.blue(&cur_left);
            }
            cur_left
        } else {
            " ".repeat(left_align_of_right)
        };

        let idx = right_character_number.min(remain_right.len());
        let cur_right = &remain_right[..idx];
        remain_right = &remain_right[idx..];
        res.push(cur_left);
        res.push(cur_right.to_string());
        res.push("\n".to_string());
        is_first_line = false;
    }
    res
}

/// `getDisplayNameTextOfOption`.
fn get_display_name_text_of_option(option: &CommandLineOption) -> String {
    let suffix = if option.short_name.is_empty() {
        String::new()
    } else {
        format!(", -{}", option.short_name)
    };
    format!("--{}{}", option.name, suffix)
}
