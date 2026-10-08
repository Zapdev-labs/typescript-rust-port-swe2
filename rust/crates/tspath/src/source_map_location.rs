// Ported from tsc/internal/tspath/source_map_location.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::ops::Deref;

use crate::path::{get_root_length, normalize_slashes};
use crate::rooted_path::{RootedDirectoryPath, to_rooted_directory_path};

// SourceMapLocation is a slash-normalized source-map location. It may be relative,
// rooted, or URL-like; the zero value means no map root was specified.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SourceMapLocation(String);

pub fn to_source_map_location(path: &str) -> SourceMapLocation {
    SourceMapLocation(normalize_slashes(path).into_owned())
}

impl SourceMapLocation {
    // UnmarshalText mirrors encoding.TextUnmarshaler: assigns the slash-normalized
    // text. It cannot fail, matching the Go implementation.
    pub fn unmarshal_text(&mut self, text: &[u8]) {
        // PORT: Go stores unchecked bytes; callers guarantee UTF-8. Non-UTF-8 is
        // decoded lossily here since Rust &str requires UTF-8.
        *self = to_source_map_location(&String::from_utf8_lossy(text));
    }

    // MarshalText mirrors encoding.TextMarshaler.
    pub fn marshal_text(&self) -> Vec<u8> {
        self.0.as_bytes().to_vec()
    }

    pub fn as_string(&self) -> &str {
        &self.0
    }

    pub fn is_relative(&self) -> bool {
        get_root_length(&self.0) == 0
    }

    pub fn resolve_directory(
        &self,
        relative_base: &RootedDirectoryPath,
        current_directory: &RootedDirectoryPath,
    ) -> RootedDirectoryPath {
        if self.0.is_empty() {
            panic!("cannot resolve an empty source map root");
        }
        if self.is_relative() {
            return relative_base.resolve_directory(&self.0);
        }
        to_rooted_directory_path(&self.0, current_directory)
    }
}

// PORT: serde impls mirror the Go encoding.TextMarshaler/TextUnmarshaler pair —
// the location serializes as a plain JSON string.
impl serde::Serialize for SourceMapLocation {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> serde::Deserialize<'de> for SourceMapLocation {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        Ok(to_source_map_location(&s))
    }
}

impl From<&str> for SourceMapLocation {
    fn from(s: &str) -> Self {
        SourceMapLocation(s.to_string())
    }
}

impl From<String> for SourceMapLocation {
    fn from(s: String) -> Self {
        SourceMapLocation(s)
    }
}

impl Deref for SourceMapLocation {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}
