// Ported from tsc/internal/core/projectreference.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use serde::{Deserialize, Serialize};
use tsc_tspath as tspath;

use crate::options_generated::rooted_path_serde;

fn bool_is_false(v: &bool) -> bool {
    !*v
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct ProjectReference {
    // Path is a normalized path on disk.
    #[serde(rename = "path", with = "rooted_path_serde")]
    pub path: tspath::RootedPath,
    // OriginalPath is the path as it was originally written.
    #[serde(rename = "originalPath", skip_serializing_if = "String::is_empty")]
    pub original_path: String,
    // Circular indicates that this reference is intended to form a circularity.
    #[serde(rename = "circular", skip_serializing_if = "bool_is_false")]
    pub circular: bool,
}

pub fn resolve_project_reference_path(r#ref: &ProjectReference) -> tspath::RootedFilePath {
    resolve_config_file_name_of_project_reference(&r#ref.path)
}

pub fn resolve_config_file_name_of_project_reference(
    path: &tspath::RootedPath,
) -> tspath::RootedFilePath {
    let file_name = tspath::rooted_file_path_from_path(path.clone());
    if file_name.extension_is(tspath::EXTENSION_JSON) {
        return file_name;
    }
    tspath::rooted_directory_path_from_path(path.clone()).resolve_file("tsconfig.json")
}
