// Ported from tsc/internal/semver @ ec47d33c23e464a17cdf2475632cba629bee8763

mod version;
mod version_range;

pub use version::{NumError, ParseError, SemverParseError, Version, must_parse, try_parse_version};
pub use version_range::{VersionRange, try_parse_version_range};

#[cfg(test)]
mod version_range_test;
#[cfg(test)]
mod version_test;
