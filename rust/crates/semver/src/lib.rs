// Ported from tsc/internal/semver @ ec47d33c23e464a17cdf2475632cba629bee8763

mod version;
mod version_range;

pub use version::{must_parse, try_parse_version, NumError, ParseError, SemverParseError, Version};
pub use version_range::{try_parse_version_range, VersionRange};

#[cfg(test)]
mod version_range_test;
#[cfg(test)]
mod version_test;
