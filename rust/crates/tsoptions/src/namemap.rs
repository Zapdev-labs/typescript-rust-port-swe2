// Ported from tsc/internal/tsoptions/namemap.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;
use std::sync::LazyLock;

use tsc_collections::OrderedMap;

use crate::commandlineoption::{CommandLineOption, CommandLineOptionRef};
use crate::generated::declarations;

/// `var CompilerNameMap = GetNameMapFromList(OptionsDeclarations)`.
pub fn compiler_name_map() -> &'static NameMap {
    static M: LazyLock<NameMap> =
        LazyLock::new(|| get_name_map_from_list(declarations::options_declarations()));
    &M
}

/// `var BuildNameMap = GetNameMapFromList(BuildOpts)`.
pub fn build_name_map() -> &'static NameMap {
    static M: LazyLock<NameMap> =
        LazyLock::new(|| get_name_map_from_list(declarations::build_opts()));
    &M
}

/// `GetNameMapFromList`.
pub fn get_name_map_from_list(opt_decls: impl Iterator<Item = CommandLineOptionRef>) -> NameMap {
    let opt_decls: Vec<CommandLineOptionRef> = opt_decls.collect();
    let mut options_names = OrderedMap::with_size_hint(opt_decls.len());
    let mut short_option_names = HashMap::new();
    for option in opt_decls {
        options_names.set(option.name.to_lowercase(), option);
        if !option.short_name.is_empty() {
            short_option_names.insert(option.short_name.to_string(), option.name.to_string());
        }
    }
    NameMap {
        options_names,
        short_option_names,
    }
}

/// `type NameMap struct`.
pub struct NameMap {
    options_names: OrderedMap<String, CommandLineOptionRef>,
    short_option_names: HashMap<String, String>,
}

impl NameMap {
    /// `(nm *NameMap) Get`.
    pub fn get(&self, name: &str) -> Option<CommandLineOptionRef> {
        self.options_names.get(&name.to_lowercase()).copied()
    }

    /// `(nm *NameMap) GetFromShort`.
    pub fn get_from_short(&self, short_name: &str) -> Option<CommandLineOptionRef> {
        // returns option only if shortName is a valid short option
        let name = self.short_option_names.get(short_name)?;
        self.get(name)
    }

    /// `(nm *NameMap) GetOptionDeclarationFromName`.
    pub fn get_option_declaration_from_name(
        &self,
        option_name: &str,
        allow_short: bool,
    ) -> Option<CommandLineOptionRef> {
        let mut option_name = option_name.to_lowercase();
        // Try to translate short option names to their full equivalents.
        if allow_short {
            if let Some(short) = self.short_option_names.get(&option_name) {
                option_name = short.clone();
            }
        }
        self.get(&option_name)
    }

    /// Exposed for `did you mean` suggestion iteration (Go
    /// `nm.optionsNames` is consulted via `CommandLineOptionNameMap` in the
    /// caller instead).
    #[allow(dead_code)]
    pub(crate) fn options_names(&self) -> &OrderedMap<String, CommandLineOptionRef> {
        &self.options_names
    }
}

// keep CommandLineOption referenced for docs
#[allow(dead_code)]
type _Unused = CommandLineOption;
