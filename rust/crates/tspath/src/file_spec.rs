// Ported from tsc/internal/tspath/file_spec.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::ops::Deref;

// FileSpec is a file name as written in a configuration file.
// It may be relative and may contain ${configDir}.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct FileSpec(String);

pub fn to_file_spec(value: &str) -> FileSpec {
    FileSpec::from(value)
}

impl FileSpec {
    pub fn as_string(&self) -> &str {
        &self.0
    }
}

impl From<&str> for FileSpec {
    fn from(s: &str) -> Self {
        FileSpec(s.to_string())
    }
}

impl From<String> for FileSpec {
    fn from(s: String) -> Self {
        FileSpec(s)
    }
}

impl Deref for FileSpec {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

// PathPattern is an include or exclude pattern as written in configuration.
// It may be relative, rooted, or contain wildcards and ${configDir}.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct PathPattern(String);

pub fn to_path_pattern(value: &str) -> PathPattern {
    PathPattern::from(value)
}

impl PathPattern {
    pub fn as_string(&self) -> &str {
        &self.0
    }
}

impl From<&str> for PathPattern {
    fn from(s: &str) -> Self {
        PathPattern(s.to_string())
    }
}

impl From<String> for PathPattern {
    fn from(s: String) -> Self {
        PathPattern(s)
    }
}

impl Deref for PathPattern {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}
