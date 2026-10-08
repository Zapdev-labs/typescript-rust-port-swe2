// Ported from tsc/internal/tspath @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Ported from tsc/internal/tspath/doc.go:
//
//! Package tspath defines rooted path types and canonical path keys:
//!
//! ```text
//!                        RootedFilePath
//!                       /
//! string --> RootedPath
//!                       \
//!                        RootedDirectoryPath
//!
//! RootedPath + CaseSensitivity --> PathKey
//! ```
//!
//! Rooted paths preserve their normalized path text and casing. RootedFilePath
//! and RootedDirectoryPath express intended use; they do not assert filesystem
//! existence or kind. Use CaseSensitivity.PathKey to derive a PathKey for
//! comparison and lookup. Do not use a PathKey as a rooted path.
//!
//! Use constructors to resolve, normalize, or validate strings. Converting a
//! RootedFilePath or RootedDirectoryPath to RootedPath is lossless. Choosing
//! file or directory intent for a RootedPath is explicit.
//!
//! Use ToRootedPath, ToRootedFilePath, or ToRootedDirectoryPath for a path that
//! may be relative and needs resolution against a current directory. Use a
//! FromNormalized constructor only when the input is already rooted and
//! normalized. Derive a PathKey only when a canonical key is needed for a
//! comparison, set, or map lookup.
//!
//! RootedFilePath.RemoveFileExtension and RemoveExtension return FileNameStem
//! because removing an extension can break path normalization. Append the final
//! suffix before treating a stem as a rooted file path.

mod dynamic;
mod extension;
mod file_spec;
mod ignoredpaths;
mod module_specifier;
mod path;
mod pathkey;
mod relative_path;
mod rooted_path;
mod source_map_location;
mod stringutil_shim;

pub use dynamic::*;
pub use extension::*;
pub use file_spec::*;
pub use ignoredpaths::*;
pub use module_specifier::*;
pub use path::*;
pub use pathkey::*;
pub use relative_path::*;
pub use rooted_path::*;
pub use source_map_location::*;

#[cfg(test)]
mod ignoredpaths_test;
#[cfg(test)]
mod path_test;
#[cfg(test)]
mod starts_with_directory_test;
#[cfg(test)]
mod typed_paths_test;
#[cfg(test)]
mod untitled_test;
