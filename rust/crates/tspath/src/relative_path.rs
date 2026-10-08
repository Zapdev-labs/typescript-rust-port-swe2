// Ported from tsc/internal/tspath/relative_path.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::ops::Deref;

use crate::extension::change_extension;
use crate::module_specifier::ModuleSpecifier;
use crate::path::{
    CaseSensitivity, ensure_path_is_non_module_name, get_base_file_name_from_normalized,
    get_encoded_root_length, has_trailing_directory_separator, normalize_path,
    remove_trailing_directory_separator,
};
use crate::rooted_path::{
    RootedDirectoryPath, RootedFilePath, RootedPath, relative_path_from_normalized_paths,
    validate_file_extension,
};

// RelativePath is a slash-normalized, lexically normalized path without a
// root. Leading parent components and a trailing directory separator are
// permitted. Its zero value is a valid sentinel.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RelativePath(String);

// ToRelativePath normalizes a path that is known to be relative.
pub fn to_relative_path(path: &str) -> RelativePath {
    if get_encoded_root_length(path) != 0 {
        panic!("relative path must not be rooted");
    }
    RelativePath(normalize_path(path).into_owned())
}

// RelativePathFromNormalized creates a RelativePath from a value already known
// to be relative and normalized.
pub fn relative_path_from_normalized(path: &str) -> RelativePath {
    if get_encoded_root_length(path) != 0 || normalize_path(path).as_ref() != path {
        panic!("relative path must be relative and normalized: {path}");
    }
    RelativePath::from(path)
}

impl RelativePath {
    pub fn as_string(&self) -> &str {
        &self.0
    }

    pub fn as_module_specifier(&self) -> ModuleSpecifier {
        ModuleSpecifier::from(ensure_path_is_non_module_name(&self.0).as_ref())
    }

    pub fn change_extension(&self, extension: &str) -> RelativePath {
        validate_file_extension(extension);
        RelativePath(change_extension(&self.0, extension).into_owned())
    }

    pub fn base_name(&self) -> &str {
        get_base_file_name_from_normalized(&self.0)
    }

    pub fn is_parent_relative(&self) -> bool {
        self.0 == ".." || self.0.starts_with("../")
    }

    pub fn has_trailing_directory_separator(&self) -> bool {
        has_trailing_directory_separator(&self.0)
    }

    pub fn without_trailing_directory_separator(&self) -> RelativePath {
        if !self.has_trailing_directory_separator() {
            return self.clone();
        }
        RelativePath::from(remove_trailing_directory_separator(&self.0))
    }

    pub fn with_trailing_directory_separator(&self) -> RelativePath {
        if self.0.is_empty() || self.has_trailing_directory_separator() {
            return self.clone();
        }
        RelativePath(format!("{}/", self.0))
    }

    pub(crate) fn requires_resolution(&self) -> bool {
        self.is_parent_relative() || has_trailing_directory_separator(&self.0)
    }
}

impl From<&str> for RelativePath {
    fn from(s: &str) -> Self {
        RelativePath(s.to_string())
    }
}

impl From<String> for RelativePath {
    fn from(s: String) -> Self {
        RelativePath(s)
    }
}

impl Deref for RelativePath {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl CaseSensitivity {
    pub fn canonical_relative_path(&self, path: &RelativePath) -> RelativePath {
        RelativePath::from(self.canonicalize(path.as_string()).as_ref())
    }

    // RelativePathFromDirectory returns the normalized path from directory to
    // fileName. It returns false when the paths have different roots.
    pub fn relative_path_from_directory(
        &self,
        directory: &RootedDirectoryPath,
        file_name: &RootedFilePath,
    ) -> Option<RelativePath> {
        self.relative_path_from_path(directory, &file_name.as_path())
    }

    // RelativePathFromPath returns the normalized path from directory to path.
    // It returns false when the paths have different roots.
    pub fn relative_path_from_path(
        &self,
        directory: &RootedDirectoryPath,
        rooted_path: &RootedPath,
    ) -> Option<RelativePath> {
        let path = relative_path_from_normalized_paths(
            directory.as_string(),
            rooted_path.as_string(),
            *self,
        );
        if get_encoded_root_length(&path) != 0 {
            return None;
        }
        Some(RelativePath(path))
    }

    pub fn relative_path_from_file(
        &self,
        from: &RootedFilePath,
        to: &RootedFilePath,
    ) -> Option<RelativePath> {
        self.relative_path_from_file_to_path(from, &to.as_path())
    }

    pub fn relative_path_from_file_to_path(
        &self,
        from: &RootedFilePath,
        to: &RootedPath,
    ) -> Option<RelativePath> {
        self.relative_path_from_path(&from.directory(), to)
    }

    pub fn relative_path_from_relative_directory(
        &self,
        directory: &RelativePath,
        file_name: &RelativePath,
    ) -> RelativePath {
        RelativePath(relative_path_from_normalized_paths(
            directory.as_string(),
            file_name.as_string(),
            *self,
        ))
    }
}
