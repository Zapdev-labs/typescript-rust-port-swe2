// Ported from tsc/internal/sourcemap/source_mapper.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::rc::Rc;

use rustc_hash::FxHashMap;
use serde::Deserialize;
use tsc_debug as debug;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};

use crate::decoder::{MISSING_SOURCE, decode_mappings};
use crate::generator::{NameIndex, RawSourceMap, SourceIndex};
use crate::lineinfo::EcmaLineInfo;

/// `type Host interface`
///
/// PORT: `GetECMALineInfo` returns `Rc<EcmaLineInfo>` — Go hosts return a
/// pointer to a line info cached on the file snapshot, and `Rc` preserves
/// that shared-ownership shape without forcing the host to clone the text.
pub trait Host {
    /// `CaseSensitivity() tspath.CaseSensitivity`.
    fn case_sensitivity(&self) -> CaseSensitivity;
    /// `GetECMALineInfo(fileName tspath.RootedFilePath) *ECMALineInfo`.
    fn get_ecma_line_info(&self, file_name: &RootedFilePath) -> Option<Rc<EcmaLineInfo>>;
    /// `ReadFile(fileName tspath.RootedFilePath) (string, bool)`.
    fn read_file(&self, file_name: &RootedFilePath) -> Option<String>;
}

/// `type MappedPosition struct` — similar to `Mapping`, but position-based.
///
/// `SourceMappedPosition` is a Go type alias for `MappedPosition`; this one
/// type serves both uses.
#[derive(Clone, Copy, Debug)]
struct MappedPosition {
    generated_position: i32,
    source_position: i32,
    source_index: SourceIndex,
    // PORT: stored for Go parity; nothing in the ported code reads nameIndex.
    #[allow(dead_code)]
    name_index: NameIndex,
}

/// `const missingPosition = -1`
const MISSING_POSITION: i32 = -1;

impl MappedPosition {
    fn is_source_mapped_position(&self) -> bool {
        self.source_index != MISSING_SOURCE && self.source_position != MISSING_POSITION
    }
}

/// `type DocumentPositionMapper struct`
///
/// Maps source positions to generated positions and vice versa.
///
/// PORT: the nil-safe Go methods (`if d == nil { return nil }`) become
/// `Option<DocumentPositionMapper>` handling at the call site.
pub struct DocumentPositionMapper {
    case_sensitivity: CaseSensitivity,
    source_file_absolute_paths: Vec<RootedFilePath>,
    source_mappings_by_path: FxHashMap<PathKey, Vec<MappedPosition>>,
    generated_absolute_file_path: RootedFilePath,

    generated_mappings: Vec<MappedPosition>,
    // PORT: stored for Go parity; the Go field is likewise only populated,
    // never read (lookups go through sourceMappingsByPath).
    #[allow(dead_code)]
    source_mappings: FxHashMap<SourceIndex, Vec<MappedPosition>>,
}

fn create_document_position_mapper(
    host: &dyn Host,
    source_map: &RawSourceMap,
    source_root_field: Option<&str>,
    null_sources: &[bool],
    map_path: RootedFilePath,
) -> Option<DocumentPositionMapper> {
    let map_directory = map_path.directory();
    let mut source_url_prefix = String::new();
    // ECMA-426 prefixes an explicit empty sourceRoot with "/", but TypeScript and
    // established consumers treat it as absent. Preserve that compatibility.
    if let Some(source_root) = source_root_field {
        if !source_root.is_empty() {
            source_url_prefix = source_root.to_string();
            if !source_url_prefix.ends_with('/') {
                source_url_prefix.push('/');
            }
        }
    }
    let generated_absolute_file_path =
        try_resolve_source_map_path(&source_map.file, &map_directory)?;
    let mut unmapped_sources = null_sources.to_vec();
    let mut source_file_absolute_paths: Vec<RootedFilePath> =
        vec![RootedFilePath::default(); source_map.sources.len()];
    for (i, source) in source_map.sources.iter().enumerate() {
        if unmapped_sources[i] {
            continue;
        }
        let source_with_prefix = format!("{source_url_prefix}{source}");
        let resolved = if source_with_prefix.is_empty() {
            map_path.clone()
        } else {
            match try_resolve_source_map_path(&source_with_prefix, &map_directory) {
                Some(resolved) => resolved,
                None => {
                    unmapped_sources[i] = true;
                    continue;
                }
            }
        };
        source_file_absolute_paths[i] = resolved;
    }
    let case_sensitivity = host.case_sensitivity();
    let mut source_to_source_index_map: FxHashMap<PathKey, Vec<SourceIndex>> = FxHashMap::default();
    for (i, source) in source_file_absolute_paths.iter().enumerate() {
        if unmapped_sources[i] {
            continue;
        }
        let key = case_sensitivity.path_key(&source.as_path());
        source_to_source_index_map
            .entry(key)
            .or_default()
            .push(i as SourceIndex);
    }

    let mut decoded_mappings: Vec<MappedPosition> = Vec::new();
    let mut source_mappings: FxHashMap<SourceIndex, Vec<MappedPosition>> = FxHashMap::default();

    // getDecodedMappings()
    let mut decoder = decode_mappings(&source_map.mappings);
    for mapping in decoder.by_ref() {
        // processMapping()
        let mut generated_position = -1;
        if let Some(line_info) = host.get_ecma_line_info(&generated_absolute_file_path) {
            generated_position = tsc_scanner::scanner::compute_position_of_line_and_utf16_character(
                line_info.line_starts(),
                mapping.generated_line,
                mapping.generated_character,
                line_info.text(),
                true, /* allowEdits */
            );
        }

        let mut source_position = -1;
        if mapping.is_source_mapping() {
            let source_index = mapping.source_index;
            if source_index >= 0
                && (source_index as usize) < source_file_absolute_paths.len()
                && !unmapped_sources[source_index as usize]
            {
                if let Some(line_info) =
                    host.get_ecma_line_info(&source_file_absolute_paths[source_index as usize])
                {
                    source_position =
                        tsc_scanner::scanner::compute_position_of_line_and_utf16_character(
                            line_info.line_starts(),
                            mapping.source_line,
                            mapping.source_character,
                            line_info.text(),
                            true, /* allowEdits */
                        );
                }
            }
        }

        decoded_mappings.push(MappedPosition {
            generated_position,
            source_index: mapping.source_index,
            source_position,
            name_index: mapping.name_index,
        });
    }
    if decoder.error().is_some() {
        decoded_mappings.clear();
    }

    // getSourceMappings()
    for mapping in &decoded_mappings {
        if !mapping.is_source_mapped_position() {
            continue;
        }
        source_mappings
            .entry(mapping.source_index)
            .or_default()
            .push(*mapping);
    }
    for list in source_mappings.values_mut() {
        list.sort_by(|a, b| {
            debug::assert_!(
                a.source_index == b.source_index,
                "All source mappings should have the same source index"
            );
            a.source_position.cmp(&b.source_position)
        });
        *list = tsc_core::core::deduplicate_sorted(list, |a, b| {
            a.generated_position == b.generated_position
                && a.source_index == b.source_index
                && a.source_position == b.source_position
        })
        .into_owned();
    }
    let mut source_mappings_by_path: FxHashMap<PathKey, Vec<MappedPosition>> = FxHashMap::default();
    for (path, source_indices) in &source_to_source_index_map {
        let mut mappings: Vec<MappedPosition> = Vec::new();
        for source_index in source_indices {
            if let Some(list) = source_mappings.get(source_index) {
                mappings.extend_from_slice(list);
            }
        }
        mappings.sort_by_key(|m| m.source_position);
        source_mappings_by_path.insert(path.clone(), mappings);
    }

    // getGeneratedMappings()
    // PORT: Go aliases decodedMappings as generatedMappings and sorts it in
    // place; source_mappings holds independent copies in both languages.
    let mut generated_mappings = decoded_mappings;
    generated_mappings.sort_by(|a, b| a.generated_position.cmp(&b.generated_position));
    generated_mappings = tsc_core::core::deduplicate_sorted(&generated_mappings, |a, b| {
        a.generated_position == b.generated_position
            && a.source_index == b.source_index
            && a.source_position == b.source_position
    })
    .into_owned();

    Some(DocumentPositionMapper {
        case_sensitivity,
        source_file_absolute_paths,
        source_mappings_by_path,
        generated_absolute_file_path,
        generated_mappings,
        source_mappings,
    })
}

/// `func tryResolveSourceMapPath(path string, directory tspath.RootedDirectoryPath) (tspath.RootedFilePath, bool)`
fn try_resolve_source_map_path(
    path: &str,
    directory: &RootedDirectoryPath,
) -> Option<RootedFilePath> {
    if path.is_empty() {
        return None;
    }
    if tsc_tspath::path_is_absolute(path) {
        return tsc_tspath::try_rooted_file_path_from_absolute(path);
    }
    tsc_tspath::try_rooted_file_path_from_absolute(&tsc_tspath::combine_paths(
        directory.as_string(),
        &[path],
    ))
}

/// `type DocumentPosition struct`
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DocumentPosition {
    pub file_name: RootedFilePath,
    pub pos: i32,
}

impl DocumentPositionMapper {
    /// `func (d *DocumentPositionMapper) GetSourcePosition(loc *DocumentPosition) *DocumentPosition`
    ///
    /// PORT: `slices.BinarySearchFunc`'s "first index whose element is not
    /// less than the target" is `partition_point`.
    pub fn get_source_position(&self, loc: &DocumentPosition) -> Option<DocumentPosition> {
        if self.generated_mappings.is_empty() {
            return None;
        }

        let target_index = self
            .generated_mappings
            .partition_point(|m| m.generated_position < loc.pos);

        if target_index >= self.generated_mappings.len() {
            return None;
        }

        let mapping = &self.generated_mappings[target_index];
        if !mapping.is_source_mapped_position() {
            return None;
        }

        // Closest position
        Some(DocumentPosition {
            file_name: self.source_file_absolute_paths[mapping.source_index as usize].clone(),
            pos: mapping.source_position,
        })
    }

    /// `func (d *DocumentPositionMapper) GetGeneratedPosition(loc *DocumentPosition) *DocumentPosition`
    pub fn get_generated_position(&self, loc: &DocumentPosition) -> Option<DocumentPosition> {
        let source_mappings = self
            .source_mappings_by_path
            .get(&self.case_sensitivity.path_key(&loc.file_name.as_path()))?;
        if source_mappings.is_empty() {
            return None;
        }
        let target_index = source_mappings.partition_point(|m| m.source_position < loc.pos);

        if target_index >= source_mappings.len() {
            return None;
        }

        let mapping = &source_mappings[target_index];
        // Closest position
        Some(DocumentPosition {
            file_name: self.generated_absolute_file_path.clone(),
            pos: mapping.generated_position,
        })
    }
}

/// `func GetDocumentPositionMapper(host Host, generatedFileName tspath.RootedFilePath) *DocumentPositionMapper`
pub fn get_document_position_mapper(
    host: &dyn Host,
    generated_file_name: RootedFilePath,
) -> Option<DocumentPositionMapper> {
    let mut map_file_name = try_get_source_mapping_url_from_host(host, &generated_file_name);
    if !map_file_name.is_empty() {
        let (base64_object, matched) = try_parse_base64_url(&map_file_name);
        if matched {
            if !base64_object.is_empty() {
                if let Ok(decoded) = crate::base64::decode(&base64_object) {
                    // PORT: Go's `string(decoded)` admits invalid UTF-8; the
                    // JSON facade replaces it with U+FFFD under
                    // AllowInvalidUTF8, so lossy conversion matches.
                    return convert_document_to_source_mapper(
                        host,
                        &String::from_utf8_lossy(&decoded),
                        generated_file_name,
                    );
                }
            }
            // Not a data URL we can parse, skip it
            map_file_name.clear();
        }
    }

    let mut possible_map_locations: Vec<String> = Vec::new();
    if !map_file_name.is_empty() {
        possible_map_locations.push(map_file_name);
    }
    possible_map_locations.push(
        generated_file_name
            .append_suffix(".map")
            .as_string()
            .to_string(),
    );
    for location in &possible_map_locations {
        let Some(map_file_name) =
            try_resolve_source_map_path(location, &generated_file_name.directory())
        else {
            continue;
        };
        if let Some(map_file_contents) = host.read_file(&map_file_name) {
            return convert_document_to_source_mapper(host, &map_file_contents, map_file_name);
        }
    }
    None
}

/// `func convertDocumentToSourceMapper(host Host, contents string, mapFileName tspath.RootedFilePath) *DocumentPositionMapper`
pub(crate) fn convert_document_to_source_mapper(
    host: &dyn Host,
    contents: &str,
    map_file_name: RootedFilePath,
) -> Option<DocumentPositionMapper> {
    let parsed = try_parse_raw_source_map(contents)?;
    if parsed.source_map.sources.is_empty()
        || parsed.source_map.file.is_empty()
        || parsed.source_map.mappings.is_empty()
    {
        // invalid map
        return None;
    }

    // Don't support source maps that contain inlined sources
    if parsed
        .source_map
        .sources_content
        .as_ref()
        .is_some_and(|content| tsc_core::core::some(content, |s| s.is_some()))
    {
        return None;
    }

    create_document_position_mapper(
        host,
        &parsed.source_map,
        parsed.source_root.as_deref(),
        &parsed.null_sources,
        map_file_name,
    )
}

/// `type parsedRawSourceMap struct`
struct ParsedRawSourceMap {
    source_map: RawSourceMap,
    source_root: Option<String>,
    null_sources: Vec<bool>,
}

/// `func tryParseRawSourceMap(contents string) *parsedRawSourceMap`
fn try_parse_raw_source_map(contents: &str) -> Option<ParsedRawSourceMap> {
    /// `type rawSourceMapJSON struct` — the parse-time view of the map.
    ///
    /// PORT: `#[serde(default)]` reproduces Go's missing-field-means-zero
    /// unmarshal; `*string`/`[]*string` become `Option`/`Vec<Option<T>>`; the
    /// extra `Option` around each `Vec` also accepts JSON `null` for fields Go
    /// would leave nil. `sourceRoot`/`sourcesContent` retain their JSON
    /// spellings via `rename`.
    #[derive(Deserialize)]
    struct RawSourceMapJson {
        #[serde(default)]
        version: i32,
        #[serde(default)]
        file: String,
        #[serde(rename = "sourceRoot", default)]
        source_root: Option<String>,
        #[serde(default)]
        sources: Option<Vec<Option<String>>>,
        #[serde(default)]
        names: Option<Vec<String>>,
        #[serde(default)]
        mappings: String,
        #[serde(rename = "sourcesContent", default)]
        sources_content: Option<Vec<Option<String>>>,
    }

    let encoded: RawSourceMapJson = tsc_json::unmarshal(contents.as_bytes(), &[]).ok()?;
    if encoded.version != 3 {
        return None;
    }
    let encoded_sources = encoded.sources.unwrap_or_default();
    let mut sources: Vec<String> = Vec::with_capacity(encoded_sources.len());
    let mut null_sources = vec![false; encoded_sources.len()];
    for (i, source) in encoded_sources.into_iter().enumerate() {
        match source {
            None => {
                null_sources[i] = true;
                sources.push(String::new());
            }
            Some(source) => sources.push(source),
        }
    }
    Some(ParsedRawSourceMap {
        source_map: RawSourceMap {
            version: encoded.version,
            file: encoded.file,
            // Go does not copy `sourceRoot` into the RawSourceMap.
            source_root: String::new(),
            sources,
            names: encoded.names.unwrap_or_default(),
            mappings: encoded.mappings,
            sources_content: encoded.sources_content,
        },
        source_root: encoded.source_root,
        null_sources,
    })
}

/// `func tryGetSourceMappingURL(host Host, fileName tspath.RootedFilePath) string`
fn try_get_source_mapping_url_from_host(host: &dyn Host, file_name: &RootedFilePath) -> String {
    let line_info = host.get_ecma_line_info(file_name);
    crate::try_get_source_mapping_url(line_info.as_deref())
}

/// `func tryParseBase64Url(url string) (parseableUrl string, isBase64Url bool)`
///
/// Equivalent to `/^data:(?:application\/json;(?:charset=[uU][tT][fF]-8;)?base64,([A-Za-z0-9+/=]+)$)?/`
///
/// PORT: Go's `strings.EqualFold(url[:6], "utf-8;")` would panic when fewer
/// than 6 bytes remain and compares via Unicode case folding; `get(..6)`
/// returns None in that case (treated as a non-match, also when the slice is
/// not on a UTF-8 boundary) and `eq_ignore_ascii_case` is used — the two
/// folds differ only for non-ASCII charsets, which cannot equal "utf-8;" anyway.
fn try_parse_base64_url(url: &str) -> (String, bool) {
    let Some(mut url) = url.strip_prefix("data:") else {
        return (String::new(), false);
    };
    let Some(rest) = url.strip_prefix("application/json;") else {
        return (String::new(), true);
    };
    url = rest;
    if let Some(rest) = url.strip_prefix("charset=") {
        match rest.get(..6) {
            Some(prefix) if prefix.eq_ignore_ascii_case("utf-8;") => url = &rest[6..],
            _ => return (String::new(), true),
        }
    }
    let Some(rest) = url.strip_prefix("base64,") else {
        return (String::new(), true);
    };
    url = rest;
    for r in url.chars() {
        if !(tsc_stringutil::is_ascii_letter(r)
            || tsc_stringutil::is_digit(r)
            || r == '+'
            || r == '/'
            || r == '=')
        {
            return (String::new(), true);
        }
    }
    (url.to_string(), true)
}
