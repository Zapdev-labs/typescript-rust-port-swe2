// Ported from tsc/internal/modulespecifiers/ @ ec47d33c23e464a17cdf2475632cba629bee8763

pub mod compare;
pub mod preferences;
pub mod specifiers;
pub mod types;
pub mod util;

#[cfg(test)]
mod specifiers_test;

pub use specifiers::{
    get_each_file_name_of_module, get_module_specifier, get_module_specifiers,
    get_module_specifiers_for_file_with_info, get_module_specifiers_with_info,
    update_module_specifier,
};
pub use types::{
    CheckerShape, ImportModuleSpecifierEndingPreference, ImportModuleSpecifierPreference,
    MatchingMode, ModulePath, ModuleSpecifierEnding, ModuleSpecifierGenerationHost,
    ModuleSpecifierOptions, ModuleSpecifiersResult, RelativePreferenceKind, ResultKind,
    SourceFileForSpecifierGeneration, UserPreferences,
};
pub use util::get_node_modules_package_name;
