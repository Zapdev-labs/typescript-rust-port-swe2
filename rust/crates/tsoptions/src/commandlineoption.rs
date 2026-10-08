// Ported from tsc/internal/tsoptions/commandlineoption.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_collections::OrderedMap;
use tsc_collections::Set;
use tsc_diagnostics::Message;

use crate::generated::declarations;
use crate::value::Value;

/// `type CommandLineOptionKind string` — the Go constants are string values;
/// an enum with `as_str` reproduces them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CommandLineOptionKind {
    String,
    Number,
    Boolean,
    Object,
    List,
    ListOrElement,
    Enum,
}

impl CommandLineOptionKind {
    pub const STRING: CommandLineOptionKind = CommandLineOptionKind::String;
    pub const NUMBER: CommandLineOptionKind = CommandLineOptionKind::Number;
    pub const BOOLEAN: CommandLineOptionKind = CommandLineOptionKind::Boolean;
    pub const OBJECT: CommandLineOptionKind = CommandLineOptionKind::Object;
    pub const LIST: CommandLineOptionKind = CommandLineOptionKind::List;
    pub const LIST_OR_ELEMENT: CommandLineOptionKind = CommandLineOptionKind::ListOrElement;
    pub const ENUM: CommandLineOptionKind = CommandLineOptionKind::Enum;

    /// `string(o.Kind)` — used in diagnostics and kind switches.
    pub fn as_str(&self) -> &'static str {
        match self {
            CommandLineOptionKind::String => "string",
            CommandLineOptionKind::Number => "number",
            CommandLineOptionKind::Boolean => "boolean",
            CommandLineOptionKind::Object => "object",
            CommandLineOptionKind::List => "list",
            CommandLineOptionKind::ListOrElement => "listOrElement",
            CommandLineOptionKind::Enum => "enum",
        }
    }
}

impl PartialEq<CommandLineOptionKind> for &str {
    fn eq(&self, other: &CommandLineOptionKind) -> bool {
        *self == other.as_str()
    }
}

impl PartialEq<&str> for CommandLineOptionKind {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

/// `type CommandLineOptionPathKind uint8`.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub enum CommandLineOptionPathKind {
    #[default]
    None = 0,
    File,
    Directory,
    FileOrDirectory,
    SourceMapLocation,
    FileSpec,
    PathPattern,
    ResolvedPathPattern,
    ConfigLocator,
}

impl CommandLineOptionPathKind {
    pub fn is_rooted(&self) -> bool {
        matches!(
            self,
            CommandLineOptionPathKind::File
                | CommandLineOptionPathKind::Directory
                | CommandLineOptionPathKind::FileOrDirectory
                | CommandLineOptionPathKind::ResolvedPathPattern
        )
    }

    pub fn is_file_system_path(&self) -> bool {
        matches!(
            self,
            CommandLineOptionPathKind::File
                | CommandLineOptionPathKind::Directory
                | CommandLineOptionPathKind::FileOrDirectory
        )
    }
}

/// `PathValueAsString`.
pub fn path_value_as_string(value: &Value) -> Option<String> {
    match value {
        Value::FilePath(p) => Some(p.as_string().to_string()),
        Value::DirPath(p) => Some(p.as_string().to_string()),
        Value::RootedPath(p) => Some(p.as_string().to_string()),
        Value::SourceMapLocation(p) => Some(p.as_string().to_string()),
        _ => None,
    }
}

/// `PathValuesAsStrings`.
pub fn path_values_as_strings(value: &Value) -> Option<Vec<String>> {
    match value {
        Value::FilePathList(v) => Some(v.iter().map(|p| p.as_string().to_string()).collect()),
        Value::DirPathList(v) => Some(v.iter().map(|p| p.as_string().to_string()).collect()),
        _ => None,
    }
}

/// `DefaultValueDescription any` — the concrete population is `bool`,
/// `string`, `*diagnostics.Message`, `core.Tristate`, and i32 option enums
/// (only ScriptTarget is used).
#[derive(Clone, Copy)]
pub enum DefaultValueDescription {
    None,
    Bool(bool),
    Str(&'static str),
    Number(i64),
    Message(&'static Message),
    Tristate(tsc_core::tristate::Tristate),
    ScriptTarget(tsc_core::options_generated::ScriptTarget),
}

/// `type CommandLineOption struct`.
///
/// PORT: Go's `*CommandLineOption` receivers are `&'static CommandLineOption`
/// — every instance lives in the generated declaration tables, and pointer
/// comparisons (`option == extendsOptionDeclaration`) become `std::ptr::eq`.
/// `ElementOptions` can't be a name map at const-construction time (the maps
/// are built lazily), so it stores a tag resolved via
/// [`crate::generated::declarations::element_options`].
pub struct CommandLineOption {
    pub name: &'static str,
    pub short_name: &'static str,
    pub kind: CommandLineOptionKind,

    // used in parsing
    pub path_kind: CommandLineOptionPathKind,
    pub is_file_path: bool,
    pub is_ts_config_only: bool,
    pub is_command_line_only: bool,

    // used in output
    pub description: Option<&'static Message>,
    pub default_value_description: DefaultValueDescription,
    pub show_in_simplified_help_view: bool,

    // used in output in serializing and generate tsconfig
    pub category: Option<&'static Message>,

    // What kind of extra validation `validateJsonOptionValue` should do
    pub extra_validation: Option<ExtraValidation>,

    // checks that option with number type has value >= minValue
    pub min_value: i64,

    // used for CommandLineOptionTypeList
    pub list_preserve_falsy_values: bool,
    // used for compilerOptionsDeclaration
    pub element_options: Option<ElementOptions>,
}

/// Which lazily-built `CommandLineOptionNameMap` `ElementOptions` resolves to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ElementOptions {
    /// `CommandLineCompilerOptionsMap` (compilerOptionsDeclaration).
    CompilerOptions,
    /// `commandLineOptionsToMap(typeAcquisitionDecls)`.
    TypeAcquisition,
    /// `commandLineOptionsToMap([]*CommandLineOption{extendsElement})`.
    Extends,
    /// `commandLineOptionsToMap(<tsconfig root members>)`.
    TsconfigRoot,
}

pub type CommandLineOptionRef = &'static CommandLineOption;

/// `type extraValidation string`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExtraValidation {
    Locale,
}

pub const EXTRA_VALIDATION_LOCALE: ExtraValidation = ExtraValidation::Locale;

impl CommandLineOption {
    /// `(o *CommandLineOption) DeprecatedKeys`.
    pub fn deprecated_keys(&self) -> Option<&'static Set<String>> {
        if self.kind != CommandLineOptionKind::Enum {
            return None;
        }
        declarations::command_line_option_deprecated(self.name)
    }

    /// `(o *CommandLineOption) EnumMap`.
    pub fn enum_map(&self) -> Option<&'static OrderedMap<String, Value>> {
        if self.kind != CommandLineOptionKind::Enum {
            return None;
        }
        declarations::command_line_option_enum_map(self.name)
    }

    /// `(o *CommandLineOption) Elements`.
    pub fn elements(&self) -> Option<CommandLineOptionRef> {
        if self.kind != CommandLineOptionKind::List
            && self.kind != CommandLineOptionKind::ListOrElement
        {
            return None;
        }
        declarations::command_line_option_elements(self.name)
    }

    /// `(o *CommandLineOption) ElementOptions` — resolves the lazy name map.
    pub fn element_options_map(
        &self,
    ) -> Option<&'static crate::tsconfigparsing::CommandLineOptionNameMap> {
        self.element_options.map(declarations::element_options)
    }

    /// `(o *CommandLineOption) DisallowNullOrUndefined`.
    pub fn disallow_null_or_undefined(&self) -> bool {
        self.name == "extends"
    }
}

// PORT: `tsc_diagnostics::Message` does not implement `Debug`; the variant
// names are sufficient for debugging.
impl std::fmt::Debug for DefaultValueDescription {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::None => write!(f, "None"),
            Self::Bool(v) => f.debug_tuple("Bool").field(v).finish(),
            Self::Str(v) => f.debug_tuple("Str").field(v).finish(),
            Self::Number(v) => f.debug_tuple("Number").field(v).finish(),
            Self::Message(v) => f.debug_tuple("Message").field(&v.code()).finish(),
            Self::Tristate(v) => f.debug_tuple("Tristate").field(v).finish(),
            Self::ScriptTarget(v) => f.debug_tuple("ScriptTarget").field(v).finish(),
        }
    }
}
