// Ported from tsc/internal/tspath/module_specifier.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::ops::Deref;

use crate::extension::remove_file_extension;
use crate::path::{
    combine_paths, path_is_absolute, path_is_relative,
    resolve_path_without_trailing_directory_separator,
};
use crate::relative_path::RelativePath;

// ModuleSpecifier is source text that identifies a module. It is a semantic tag,
// not a filesystem path invariant, and is intentionally outside the typed-path
// conversion lattice described in doc.go.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ModuleSpecifier(String);

pub fn to_module_specifier(specifier: &str) -> ModuleSpecifier {
    ModuleSpecifier::from(specifier)
}

impl ModuleSpecifier {
    pub fn as_string(&self) -> &str {
        &self.0
    }

    pub fn is_absolute(&self) -> bool {
        path_is_absolute(&self.0)
    }

    pub fn is_relative(&self) -> bool {
        path_is_relative(&self.0)
    }

    pub fn contains(&self, substring: &str) -> bool {
        self.0.contains(substring)
    }

    pub fn resolve(&self, parts: &[&str]) -> ModuleSpecifier {
        ModuleSpecifier(resolve_path_without_trailing_directory_separator(&self.0, parts))
    }

    pub fn resolve_relative(&self, path: &RelativePath) -> ModuleSpecifier {
        self.resolve(&[path.as_string()])
    }

    pub fn combine_relative(&self, path: &RelativePath) -> ModuleSpecifier {
        ModuleSpecifier(combine_paths(&self.0, &[path.as_string()]))
    }

    pub fn remove_file_extension(&self) -> ModuleSpecifier {
        ModuleSpecifier::from(remove_file_extension(&self.0))
    }
}

impl From<&str> for ModuleSpecifier {
    fn from(s: &str) -> Self {
        ModuleSpecifier(s.to_string())
    }
}

impl From<String> for ModuleSpecifier {
    fn from(s: String) -> Self {
        ModuleSpecifier(s)
    }
}

impl Deref for ModuleSpecifier {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}
