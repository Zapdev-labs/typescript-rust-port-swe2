// Ported from tsc/internal/fourslash/fourslash.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `VerifyBaseline*` helpers — find-all-refs, go-to-definition family, code
// lens, hover, signature help, selection ranges, call hierarchy, document
// highlights/symbols, rename, inlay hints, linked editing, and diagnostics
// baselines. See fourslash.rs for PORT conventions and the assumed
// `crate::baselineutil` API (`DocumentSpan`, `BaselineFourslashLocationsOptions`,
// `MarkerAndItem`, `BaselineDetail`, `location_to_span`, `code_fence`,
// `symbol_information_to_data`, `get_accessible_file_paths`, the `*_cmd`
// constants, and the `FourslashTest` baseline methods).

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::rc::Rc;

use serde::Serialize;
use tsc_collections::MultiMap;
use tsc_core::text::TextRange;
use tsc_core::core::{filter, map, map_filtered, must, stringify_json};
use tsc_core::tristate::{TS_TRUE, TS_UNKNOWN};
use tsc_diagnostics::Category;
use tsc_diagnosticwriter::{Diagnostic as DwDiagnostic, FileLike};
use tsc_locale::Locale;
use tsc_lsconv::{self as lsconv, Converters, Script, compute_lsp_line_starts};
use tsc_lsproto::*;
use tsc_lsutil::{self as lsutil, UserPreferences};
use tsc_spanmap::Feature;
use tsc_stringutil::is_white_space_like;
use tsc_testutil::harnessutil::TestFile;
use tsc_testutil::tsbaseline;
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::baselineutil::{
    self, BaselineCommand, BaselineDetail, BaselineFourslashLocationsOptions, DocumentSpan,
    MarkerAndItem,
};
use crate::fourslash::{
    FourslashTest, ScriptInfo, compare_positions, compute_line_starts,
    new_test_converters, root_dir, roundtrip_through_json, symbol_kind_to_lowercase,
};
use crate::test_parser::{Marker, MarkerOrRange, RangeMarker};
use crate::verify::{is_suggestion_diagnostic, lookup_markers_or_get_ranges};
use crate::verify::SORT_TEXT_AUTO_IMPORT_SUGGESTIONS;

/// `type MarkerOrRangeOrName = any` — `string | *Marker | *RangeMarker`.
pub enum MarkerOrRangeOrName {
    Name(String),
    Marker(Rc<Marker>),
    Range(Rc<RangeMarker>),
}

impl From<&str> for MarkerOrRangeOrName {
    fn from(name: &str) -> Self {
        MarkerOrRangeOrName::Name(name.to_string())
    }
}

impl From<String> for MarkerOrRangeOrName {
    fn from(name: String) -> Self {
        MarkerOrRangeOrName::Name(name)
    }
}

impl From<Rc<Marker>> for MarkerOrRangeOrName {
    fn from(m: Rc<Marker>) -> Self {
        MarkerOrRangeOrName::Marker(m)
    }
}

impl From<Rc<RangeMarker>> for MarkerOrRangeOrName {
    fn from(r: Rc<RangeMarker>) -> Self {
        MarkerOrRangeOrName::Range(r)
    }
}

fn marker_or_range_or_name_to_marker_or_range(
    f: &FourslashTest,
    input: MarkerOrRangeOrName,
) -> Rc<dyn MarkerOrRange> {
    match input {
        MarkerOrRangeOrName::Name(name) => {
            match f.test_data.marker_positions.get(&name) {
                Some(m) => m.clone() as Rc<dyn MarkerOrRange>,
                None => panic!("Marker '{name}' not found"),
            }
        }
        MarkerOrRangeOrName::Marker(m) => m as Rc<dyn MarkerOrRange>,
        MarkerOrRangeOrName::Range(r) => r as Rc<dyn MarkerOrRange>,
    }
}

fn marker_or_ranges_from_names(
    f: &FourslashTest,
    inputs: impl IntoIterator<Item = MarkerOrRangeOrName>,
) -> Vec<Rc<dyn MarkerOrRange>> {
    inputs
        .into_iter()
        .map(|i| marker_or_range_or_name_to_marker_or_range(f, i))
        .collect()
}

impl FourslashTest {
    /// `VerifyBaselineFindAllReferences`
    pub fn verify_baseline_find_all_references(&mut self, markers: &[String]) {
        let reference_locations = lookup_markers_or_get_ranges(self, markers);

        for marker_or_range in reference_locations {
            // worker in `baselineEachMarkerOrRange`
            self.go_to_marker_or_range(&marker_or_range);

            let params = ReferenceParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                position: self.current_caret_position,
                context: Some(ReferenceContext {
                    include_declaration: true,
                }),
                ..Default::default()
            };
            let result = self.send_request(&TEXT_DOCUMENT_REFERENCES_INFO, params);
            let baseline = self.get_baseline_for_locations_with_file_contents(
                &result.locations.unwrap_or_default(),
                BaselineFourslashLocationsOptions {
                    marker: Some(marker_or_range.clone()),
                    marker_name: "/*FIND ALL REFS*/".to_string(),
                    ..Default::default()
                },
            );
            self.add_result_to_baseline(baselineutil::FIND_ALL_REFERENCES_CMD, &baseline);
        }
    }

    /// `VerifyBaselineVSFindAllReferences`
    pub fn verify_baseline_vs_find_all_references(&mut self, markers: &[String]) {
        let reference_locations = lookup_markers_or_get_ranges(self, markers);

        for marker_or_range in reference_locations {
            self.go_to_marker_or_range(&marker_or_range);

            let params = ReferenceParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                position: self.current_caret_position,
                context: Some(ReferenceContext {
                    include_declaration: true,
                }),
                ..Default::default()
            };
            let result = self.send_request(&TEXT_DOCUMENT_VS_REFERENCES_INFO, params);
            // Sort cross-project results for deterministic baselines
            if let Some(items) = &result.vs_reference_items {
                let mut items = items.clone();
                items.sort_by(|a, b| {
                    let ap = a.vs_project_name.as_deref().unwrap_or("");
                    let bp = b.vs_project_name.as_deref().unwrap_or("");
                    ap.cmp(bp)
                        .then(a.vs_location.uri.cmp(&b.vs_location.uri))
                        .then(
                            a.vs_location
                                .range
                                .start
                                .line
                                .cmp(&b.vs_location.range.start.line),
                        )
                        .then(
                            a.vs_location
                                .range
                                .start
                                .character
                                .cmp(&b.vs_location.range.start.character),
                        )
                });
                // Re-number IDs sequentially after sort
                let mut id_remap: BTreeMap<i32, i32> = BTreeMap::new();
                for (i, item) in items.iter_mut().enumerate() {
                    id_remap.insert(item.vs_id, i as i32);
                    item.vs_id = i as i32;
                }
                for item in &mut items {
                    if let Some(def_id) = &mut item.vs_definition_id {
                        *def_id = id_remap[def_id];
                    }
                }

                // Include file contents with markers
                let locations: Vec<Location> =
                    items.iter().map(|item| item.vs_location.clone()).collect();
                let file_contents = self.get_baseline_for_locations_with_file_contents(
                    &locations,
                    BaselineFourslashLocationsOptions {
                        marker: Some(marker_or_range.clone()),
                        marker_name: "/*FIND ALL REFS*/".to_string(),
                        ..Default::default()
                    },
                );

                let result_json = VSReferencesResponse {
                    vs_reference_items: Some(items),
                    ..Default::default()
                };
                match stringify_json(&result_json, "", "  ") {
                    Ok(json_str) => self.add_result_to_baseline(
                        baselineutil::VS_FIND_ALL_REFERENCES_CMD,
                        &format!("{file_contents}\n\n{json_str}"),
                    ),
                    Err(err) => {
                        panic!("Failed to stringify VS references result for baseline: {err}")
                    }
                }
            } else {
                let file_contents = self.get_baseline_for_locations_with_file_contents(
                    &[],
                    BaselineFourslashLocationsOptions {
                        marker: Some(marker_or_range.clone()),
                        marker_name: "/*FIND ALL REFS*/".to_string(),
                        ..Default::default()
                    },
                );
                match stringify_json(&result, "", "  ") {
                    Ok(json_str) => self.add_result_to_baseline(
                        baselineutil::VS_FIND_ALL_REFERENCES_CMD,
                        &format!("{file_contents}\n\n{json_str}"),
                    ),
                    Err(err) => {
                        panic!("Failed to stringify VS references result for baseline: {err}")
                    }
                }
            }
        }
    }

    /// `VerifyBaselineCodeLens`
    pub fn verify_baseline_code_lens(&mut self, preferences: Option<&UserPreferences>) {
        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_baseline_code_lens_impl();
            self.configure(original);
            return;
        }
        self.verify_baseline_code_lens_impl();
    }

    fn verify_baseline_code_lens_impl(&mut self) {
        let mut found_at_least_one_code_lens = false;
        for open_file in self.open_files.clone() {
            let params = CodeLensParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&open_file),
                },
                ..Default::default()
            };

            let unresolved_code_lens_list =
                self.send_request(&TEXT_DOCUMENT_CODE_LENS_INFO, params);
            let Some(unresolved) = unresolved_code_lens_list.code_lenses else {
                continue;
            };
            if unresolved.is_empty() {
                continue;
            }
            found_at_least_one_code_lens = true;

            for unresolved_code_lens in unresolved {
                let Some(resolved_code_lens) =
                    self.send_request(&CODE_LENS_RESOLVE_INFO, unresolved_code_lens)
                else {
                    continue;
                };
                assert!(
                    resolved_code_lens.command.is_some(),
                    "Expected resolved code lens to have a command."
                );
                if let Some(command) = &resolved_code_lens.command {
                    if !command.command.is_empty() {
                        assert_eq!(
                            command.command,
                            crate::fourslash::SHOW_CODE_LENS_LOCATIONS_COMMAND_NAME
                        );
                    }
                }

                let mut locations: Vec<Location> = vec![];
                // commandArgs: (DocumentUri, Position, Location[])
                if let Some(command) = &resolved_code_lens.command {
                    if let Some(command_args) = &command.arguments {
                        if let Some(arg) = command_args.get(2) {
                            match roundtrip_through_json::<Vec<Location>>(arg) {
                                Ok(locs) => locations = locs,
                                Err(err) => {
                                    panic!("failed to re-encode code lens locations: {err}")
                                }
                            }
                        }
                    }
                }

                let ranges = {
                    let script = self.get_script_info_or_panic(&open_file);
                    self.test_converters().converters.from_lsp_range(
                        script,
                        resolved_code_lens.range.clone(),
                        Feature::All,
                    )
                };
                if ranges.len() != 1 {
                    continue;
                }
                let code_lens_range = ranges[0].span;
                let baseline = self.get_baseline_for_locations_with_file_contents(
                    &locations,
                    BaselineFourslashLocationsOptions {
                        marker: Some(Rc::new(RangeMarker {
                            file_name: self
                                .get_script_info_or_panic(&open_file)
                                .file_name
                                .clone(),
                            ls_range: resolved_code_lens.range,
                            range: code_lens_range,
                            marker: None,
                        })),
                        marker_name: format!(
                            "/*CODELENS: {}*/",
                            resolved_code_lens
                                .command
                                .as_ref()
                                .map(|c| c.title.as_str())
                                .unwrap_or("")
                        ),
                        ..Default::default()
                    },
                );
                self.add_result_to_baseline(baselineutil::CODE_LENSES_CMD, &baseline);
            }
        }

        if !found_at_least_one_code_lens {
            panic!("Expected at least one code lens in any open file, but got none.");
        }
    }

    /// `verifyBaselineDefinitions`
    fn verify_baseline_definitions(
        &mut self,
        definition_command: BaselineCommand,
        definition_marker: &str,
        get_definitions: impl Fn(&mut FourslashTest) -> LocationOrLocationsOrDefinitionLinksOrNull,
        include_original_selection_range: bool,
        markers: &[String],
    ) {
        let reference_locations = lookup_markers_or_get_ranges(self, markers);

        for marker_or_range in reference_locations {
            // worker in `baselineEachMarkerOrRange`
            self.go_to_marker_or_range(&marker_or_range);

            let result = get_definitions(self);

            let mut result_as_spans: Vec<DocumentSpan> = vec![];
            let mut additional_span: Option<DocumentSpan> = None;
            if let Some(locations) = &result.locations {
                result_as_spans = map(locations, baselineutil::location_to_span);
            } else if let Some(location) = &result.location {
                result_as_spans = vec![baselineutil::location_to_span(location)];
            } else if let Some(definition_links) = &result.definition_links {
                let mut origin_range: Option<Range> = None;
                result_as_spans = map(definition_links, |link| {
                    if let Some(origin) = &origin_range
                        && (link.origin_selection_range.is_none()
                            || *origin != *link.origin_selection_range.as_ref().unwrap())
                    {
                        panic!("multiple different origin ranges in definition links");
                    }
                    origin_range = link.origin_selection_range.clone();
                    let context_span =
                        if link.target_range != link.target_selection_range && !self.is_strada_server
                        {
                            Some(link.target_range.clone())
                        } else {
                            None
                        };
                    DocumentSpan {
                        uri: link.target_uri.clone(),
                        text_span: link.target_selection_range.clone(),
                        context_span,
                    }
                });
                if include_original_selection_range && let Some(origin) = origin_range {
                    additional_span = Some(DocumentSpan {
                        uri: lsconv::file_name_to_document_uri(&self.active_filename),
                        text_span: origin,
                        context_span: None,
                    });
                }
            }

            let baseline = self.get_baseline_for_spans_with_file_contents(
                &result_as_spans,
                BaselineFourslashLocationsOptions {
                    marker: Some(marker_or_range.clone()),
                    marker_name: definition_marker.to_string(),
                    additional_span,
                    preserve_result_order: definition_command
                        == baselineutil::GO_TO_SOURCE_DEFINITION_CMD,
                    ..Default::default()
                },
            );
            self.add_result_to_baseline(definition_command, &baseline);
        }
    }

    /// `VerifyBaselineGoToDefinition`
    pub fn verify_baseline_go_to_definition(
        &mut self,
        include_original_selection_range: bool,
        markers: &[String],
    ) {
        self.verify_baseline_definitions(
            baselineutil::GO_TO_DEFINITION_CMD,
            "/*GOTO DEF*/", /*definitionMarker*/
            |f| {
                let params = DefinitionParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&f.active_filename),
                    },
                    position: f.current_caret_position,
                    ..Default::default()
                };
                f.send_request(&TEXT_DOCUMENT_DEFINITION_INFO, params)
            },
            include_original_selection_range,
            markers,
        );
    }

    /// `VerifyBaselineGoToTypeDefinition`
    pub fn verify_baseline_go_to_type_definition(&mut self, markers: &[String]) {
        self.verify_baseline_definitions(
            baselineutil::GO_TO_TYPE_DEFINITION_CMD,
            "/*GOTO TYPE*/", /*definitionMarker*/
            |f| {
                let params = TypeDefinitionParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&f.active_filename),
                    },
                    position: f.current_caret_position,
                    ..Default::default()
                };
                f.send_request(&TEXT_DOCUMENT_TYPE_DEFINITION_INFO, params)
            },
            false, /*includeOriginalSelectionRange*/
            markers,
        );
    }

    /// `VerifyBaselineGoToSourceDefinition`
    pub fn verify_baseline_go_to_source_definition(&mut self, markers: &[String]) {
        self.verify_baseline_definitions(
            baselineutil::GO_TO_SOURCE_DEFINITION_CMD,
            "/*GOTO SOURCE DEF*/", /*definitionMarker*/
            |f| {
                let params = TextDocumentPositionParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&f.active_filename),
                    },
                    position: f.current_caret_position,
                    ..Default::default()
                };
                let result = f.send_request(&CUSTOM_TEXT_DOCUMENT_SOURCE_DEFINITION_INFO, params);
                result.unwrap_or_default()
            },
            false, /*includeOriginalSelectionRange*/
            markers,
        );
    }

    /// `VerifyBaselineGoToImplementation`
    pub fn verify_baseline_go_to_implementation(&mut self, markers: &[String]) {
        self.verify_baseline_definitions(
            baselineutil::GO_TO_IMPLEMENTATION_CMD,
            "/*GOTO IMPL*/", /*definitionMarker*/
            |f| {
                let params = ImplementationParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&f.active_filename),
                    },
                    position: f.current_caret_position,
                    ..Default::default()
                };
                f.send_request(&TEXT_DOCUMENT_IMPLEMENTATION_INFO, params)
            },
            false, /*includeOriginalSelectionRange*/
            markers,
        );
    }

    /// `VerifyBaselineWorkspaceSymbol`
    pub fn verify_baseline_workspace_symbol(&mut self, query: &str) {
        let result = self.send_request(
            &WORKSPACE_SYMBOL_INFO,
            WorkspaceSymbolParams {
                query: query.to_string(),
                ..Default::default()
            },
        );

        let mut location_to_text: BTreeMap<DocumentSpanKey, SymbolInformation> = BTreeMap::new();
        let mut grouped_ranges: MultiMap<DocumentUri, DocumentSpan> = MultiMap::default();
        for symbol in result.symbol_informations.as_deref().unwrap_or(&[]) {
            let uri = symbol.location.uri.clone();
            let span = baselineutil::location_to_span(&symbol.location);
            grouped_ranges.add(uri, span.clone());
            location_to_text.insert(DocumentSpanKey::from(&span), symbol.clone());
        }

        let baseline = self.get_baseline_for_grouped_spans_with_file_contents(
            &grouped_ranges,
            &BaselineFourslashLocationsOptions {
                get_location_data: Some(Box::new(move |span: &DocumentSpan| {
                    location_to_text
                        .get(&DocumentSpanKey::from(span))
                        .map(|s| baselineutil::symbol_information_to_data(s))
                        .unwrap_or_default()
                })),
                ..Default::default()
            },
        );
        self.add_result_to_baseline(baselineutil::WORKSPACE_SYMBOL_CMD, &baseline);
    }

    /// `VerifyBaselineHover`
    pub fn verify_baseline_hover(&mut self) {
        let markers_and_items: Vec<MarkerAndItem<Option<Hover>>> = map_filtered(
            &self.test_data.markers.clone(),
            |marker| {
                if marker.as_ref().name.is_none() {
                    return None;
                }
                let (file_name, position) = {
                    let m = marker.as_ref();
                    (m.file_name().clone(), m.ls_position)
                };
                let params = HoverParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&file_name),
                    },
                    position,
                    ..Default::default()
                };
                let result = self.send_request(&TEXT_DOCUMENT_HOVER_INFO, params);
                Some(MarkerAndItem {
                    marker: marker.clone(),
                    item: result.hover,
                })
            },
        );

        let get_range = |item: &Option<Hover>| -> Option<Range> {
            item.as_ref().and_then(|h| h.range.clone())
        };
        let get_tooltip_lines = |item: &Option<Hover>, _prev: &Option<Hover>| -> Vec<String> {
            let mut result: Vec<String> = vec![];
            if let Some(item) = item {
                if let Some(markup) = &item.contents.markup_content {
                    result = markup.value.split('\n').map(|s| s.to_string()).collect();
                }
                if let Some(s) = &item.contents.string {
                    result = s.split('\n').map(|s| s.to_string()).collect();
                }
                if let Some(ms) = &item.contents.marked_string_with_language {
                    result = append_lines_for_marked_string_with_language(result, ms);
                }
                if let Some(marked_strings) = &item.contents.marked_strings {
                    for ms in marked_strings {
                        if let Some(msl) = &ms.marked_string_with_language {
                            result = append_lines_for_marked_string_with_language(result, msl);
                        } else if let Some(s) = &ms.string {
                            result.push(s.clone());
                        }
                    }
                }
            }
            result
        };

        let baseline = self.annotate_content_with_tooltips(
            &markers_and_items,
            "quickinfo",
            get_range,
            get_tooltip_lines,
        );
        self.add_result_to_baseline(baselineutil::QUICK_INFO_CMD, &baseline);
        match stringify_json(&markers_and_items, "", "  ") {
            Ok(json_str) => self.write_to_baseline(baselineutil::QUICK_INFO_CMD, &json_str),
            Err(err) => panic!("Failed to stringify markers and items for baseline: {err}"),
        }
    }

    /// `VerifyBaselineVSHover` — like `verify_baseline_hover`, but asserts on
    /// the VS-specific rich hover content (Hover.VSRawContent) emitted for
    /// clients advertising VSSupportsVisualStudioExtensions.
    pub fn verify_baseline_vs_hover(&mut self) {
        let markers_and_items: Vec<MarkerAndItem<Option<Hover>>> = map_filtered(
            &self.test_data.markers.clone(),
            |marker| {
                if marker.as_ref().name.is_none() {
                    return None;
                }
                let (file_name, position) = {
                    let m = marker.as_ref();
                    (m.file_name().clone(), m.ls_position)
                };
                let params = HoverParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&file_name),
                    },
                    position,
                    ..Default::default()
                };
                let result = self.send_request(&TEXT_DOCUMENT_HOVER_INFO, params);
                Some(MarkerAndItem {
                    marker: marker.clone(),
                    item: result.hover,
                })
            },
        );

        let get_range = |item: &Option<Hover>| -> Option<Range> {
            item.as_ref().and_then(|h| h.range.clone())
        };
        let get_tooltip_lines = |item: &Option<Hover>, _prev: &Option<Hover>| -> Vec<String> {
            let Some(item) = item else {
                return vec![];
            };
            let Some(raw) = &item.vs_raw_content else {
                return vec![
                    "(no _vs_rawContent; is VSSupportsVisualStudioExtensions set on the test's ClientCapabilities?)"
                        .to_string(),
                ];
            };
            render_vs_container_element(raw, "")
        };

        let baseline = self.annotate_content_with_tooltips(
            &markers_and_items,
            "vsquickinfo",
            get_range,
            get_tooltip_lines,
        );
        self.add_result_to_baseline(baselineutil::VS_QUICK_INFO_CMD, &baseline);
        match stringify_json(&markers_and_items, "", "  ") {
            Ok(json_str) => self.write_to_baseline(baselineutil::VS_QUICK_INFO_CMD, &json_str),
            Err(err) => panic!("Failed to stringify markers and items for baseline: {err}"),
        }
    }

    /// `VerifyBaselineHoverWithVerbosity`
    pub fn verify_baseline_hover_with_verbosity(
        &mut self,
        verbosity_levels: &BTreeMap<String, Vec<i32>>,
    ) {
        let mut markers_and_items: Vec<MarkerAndItem<Option<HoverWithVerbosity>>> = vec![];
        for marker in self.markers() {
            if marker.as_ref().name.is_none() {
                continue;
            }
            let (name, file_name, position) = {
                let m = marker.as_ref();
                (m.name.clone().unwrap(), m.file_name().clone(), m.ls_position)
            };
            let levels = verbosity_levels
                .get(&name)
                .cloned()
                .unwrap_or_else(|| vec![0]);
            for (i, level) in levels.iter().enumerate() {
                let verb_level = if *level > 0 { Some(*level) } else { None };
                let params = HoverParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&file_name),
                    },
                    position,
                    verbosity_level: verb_level,
                    ..Default::default()
                };
                let result = self.send_request(&TEXT_DOCUMENT_HOVER_INFO, params);
                let item = HoverWithVerbosity {
                    hover: result.hover,
                    verbosity_level: *level,
                };
                // If the previous level said it can't expand further, verify the hover
                // content is identical, meaning the flag was accurate.
                if i > 0 && *level > levels[i - 1] {
                    if let Some(prev_item) = markers_and_items.last().and_then(|m| m.item.as_ref())
                    {
                        if let Some(prev_hover) = &prev_item.hover {
                            if !prev_hover.can_increase_verbosity {
                                let prev_content = hover_content_string(Some(prev_hover));
                                let cur_content = hover_content_string(item.hover.as_ref());
                                if prev_content != cur_content {
                                    panic!(
                                        "At marker {name:?}: verbosity level {level} response differs from level {}, but level {} had canIncreaseVerbosity=false.\n  level {}: {prev_content}\n  level {level}: {cur_content}",
                                        levels[i - 1],
                                        levels[i - 1],
                                        levels[i - 1],
                                    );
                                }
                            }
                        }
                    }
                }
                markers_and_items.push(MarkerAndItem {
                    marker: marker.clone(),
                    item: Some(item),
                });
            }
        }

        let get_range = |item: &Option<HoverWithVerbosity>| -> Option<Range> {
            item.as_ref()
                .and_then(|i| i.hover.as_ref())
                .and_then(|h| h.range.clone())
        };
        let get_tooltip_lines =
            |item: &Option<HoverWithVerbosity>, _prev: &Option<HoverWithVerbosity>| -> Vec<String> {
                let Some(item) = item else {
                    return vec![];
                };
                let mut result: Vec<String> = vec![];
                if let Some(hover) = &item.hover {
                    if let Some(markup) = &hover.contents.markup_content {
                        result = markup.value.split('\n').map(|s| s.to_string()).collect();
                    }
                    if let Some(s) = &hover.contents.string {
                        result = s.split('\n').map(|s| s.to_string()).collect();
                    }
                    if let Some(ms) = &hover.contents.marked_string_with_language {
                        result = append_lines_for_marked_string_with_language(result, ms);
                    }
                    if let Some(marked_strings) = &hover.contents.marked_strings {
                        for ms in marked_strings {
                            if let Some(msl) = &ms.marked_string_with_language {
                                result = append_lines_for_marked_string_with_language(result, msl);
                            } else if let Some(s) = &ms.string {
                                result.push(s.clone());
                            }
                        }
                    }
                }
                result.push(format!("(verbosity level: {})", item.verbosity_level));
                result
            };

        let baseline = self.annotate_content_with_tooltips(
            &markers_and_items,
            "quickinfo",
            get_range,
            get_tooltip_lines,
        );
        self.add_result_to_baseline(baselineutil::QUICK_INFO_CMD, &baseline);
        match stringify_json(&markers_and_items, "", "  ") {
            Ok(json_str) => self.write_to_baseline(baselineutil::QUICK_INFO_CMD, &json_str),
            Err(err) => panic!("Failed to stringify markers and items for baseline: {err}"),
        }
    }

    /// `VerifyBaselineSignatureHelp`
    pub fn verify_baseline_signature_help(&mut self) {
        let markers_and_items: Vec<MarkerAndItem<Option<SignatureHelp>>> = map_filtered(
            &self.test_data.markers.clone(),
            |marker| {
                if marker.as_ref().name.is_none() {
                    return None;
                }
                let (file_name, position) = {
                    let m = marker.as_ref();
                    (m.file_name().clone(), m.ls_position)
                };
                let params = SignatureHelpParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&file_name),
                    },
                    position,
                    ..Default::default()
                };
                let result = self.send_request(&TEXT_DOCUMENT_SIGNATURE_HELP_INFO, params);
                Some(MarkerAndItem {
                    marker: marker.clone(),
                    item: result.signature_help,
                })
            },
        );

        let get_range = |_item: &Option<SignatureHelp>| -> Option<Range> {
            // SignatureHelp doesn't have a range like hover does
            None
        };

        let get_tooltip_lines =
            |item: &Option<SignatureHelp>, _prev: &Option<SignatureHelp>| -> Vec<String> {
                let Some(item) = item else {
                    return vec!["No signature help available".to_string()];
                };
                if item.signatures.as_deref().unwrap_or(&[]).is_empty() {
                    return vec!["No signature help available".to_string()];
                }

                // Show active signature if specified, otherwise first signature
                let signatures = item.signatures.as_deref().unwrap_or(&[]);
                let mut active_signature = 0usize;
                if let Some(active) = item.active_signature {
                    if (active as usize) < signatures.len() {
                        active_signature = active as usize;
                    }
                }

                let sig = &signatures[active_signature];

                // Build signature display
                let mut signature_line = sig.label.clone();
                let mut active_param_line = String::new();

                // Determine active parameter: per-signature takes precedence over top-level per LSP spec
                // "If provided (or `null`), this is used in place of `SignatureHelp.activeParameter`."
                let active_param_ptr = sig
                    .active_parameter
                    .as_ref()
                    .or(item.active_parameter.as_ref());

                // Show active parameter if specified, and the signature text.
                if let Some(active_param_ptr) = active_param_ptr {
                    if let Some(uinteger) = active_param_ptr.uinteger {
                        if let Some(parameters) = &sig.parameters {
                            let active_param_index = uinteger as usize;
                            if active_param_index < parameters.len() {
                                let active_param = &parameters[active_param_index];

                                // Get the parameter label and bold the
                                // parameter text within the original string.
                                let mut active_param_label = String::new();
                                if let Some(s) = &active_param.label.string {
                                    active_param_label = s.clone();
                                } else if let Some(tuple) = &active_param.label.tuple {
                                    active_param_label = signature_line
                                        [tuple[0] as usize..tuple[1] as usize]
                                        .to_string();
                                } else {
                                    panic!("Unsupported param label kind.");
                                }
                                signature_line = signature_line.replacen(
                                    &active_param_label,
                                    &format!("**{active_param_label}**"),
                                    1,
                                );

                                if let Some(documentation) = &active_param.documentation {
                                    if let Some(markup) = &documentation.markup_content {
                                        active_param_line = markup.value.clone();
                                    } else if let Some(s) = &documentation.string {
                                        active_param_line = s.clone();
                                    }
                                    active_param_line = format!(
                                        "- `{active_param_label}`: {active_param_line}"
                                    );
                                }
                            }
                        }
                    }
                }

                let mut result: Vec<String> = Vec::with_capacity(16);
                result.push(signature_line);
                if !active_param_line.is_empty() {
                    result.push(active_param_line);
                }

                // ORIGINALLY we would "only display signature documentation on the last argument when multiple arguments are marked".
                // !!!
                // Note that this is harder than in Strada, because LSP signature help has no concept of
                // applicable spans.
                if let Some(documentation) = &sig.documentation {
                    if let Some(markup) = &documentation.markup_content {
                        result.extend(markup.value.split('\n').map(|s| s.to_string()));
                    } else if let Some(s) = &documentation.string {
                        result.extend(s.split('\n').map(|s| s.to_string()));
                    } else {
                        panic!("Unsupported documentation format.");
                    }
                }

                result
            };

        let baseline = self.annotate_content_with_tooltips(
            &markers_and_items,
            "signaturehelp",
            get_range,
            get_tooltip_lines,
        );
        self.add_result_to_baseline(baselineutil::SIGNATURE_HELP_CMD, &baseline);
        match stringify_json(&markers_and_items, "", "  ") {
            Ok(json_str) => self.write_to_baseline(baselineutil::SIGNATURE_HELP_CMD, &json_str),
            Err(err) => panic!("Failed to stringify markers and items for baseline: {err}"),
        }
    }

    /// `VerifyBaselineSelectionRanges`
    pub fn verify_baseline_selection_ranges(&mut self) {
        let markers = self.markers();
        let mut result = String::new();
        let new_line = "\n";

        for (i, marker) in markers.iter().enumerate() {
            if i > 0 {
                result.push_str(new_line);
                result.push_str(&"=".repeat(80));
                result.push_str(new_line);
                result.push_str(new_line);
            }

            let (file_name, marker_pos, position) = {
                let m = marker.as_ref();
                (m.file_name().clone(), m.position, m.ls_position)
            };
            let file_content = self
                .get_script_info_or_panic(&file_name)
                .content
                .clone();

            // Add the marker position indicator
            let baseline_content = format!(
                "{}/**/{}{}",
                &file_content[..marker_pos as usize],
                &file_content[marker_pos as usize..],
                new_line
            );
            result.push_str(&baseline_content);

            // Get selection ranges at this marker
            let params = SelectionRangeParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&file_name),
                },
                positions: Some(vec![position]),
                ..Default::default()
            };

            let selection_range_result =
                self.send_request(&TEXT_DOCUMENT_SELECTION_RANGE_INFO, params);

            if selection_range_result
                .selection_ranges
                .as_ref()
                .is_none_or(|r| r.is_empty())
            {
                result.push_str("No selection ranges available\n");
                continue;
            }

            let mut selection_range =
                Some(selection_range_result.selection_ranges.unwrap()[0].clone());

            // Add blank line after source code section
            result.push_str(new_line);

            // Walk through the selection range chain
            loop {
                let Some(sr) = &selection_range else { break };
                let (start, end) = {
                    let script = self.get_script_info_or_panic(&file_name);
                    let converters = self.test_converters();
                    (
                        converters.line_and_character_to_position(script, sr.range.start)
                            as usize,
                        converters.line_and_character_to_position(script, sr.range.end)
                            as usize,
                    )
                };

                // Create a masked version of the file showing only this range
                let runes: Vec<char> = file_content.chars().collect();
                let mut masked: Vec<char> = vec![' '; runes.len()];
                for (i, ch) in runes.iter().enumerate() {
                    if i >= start && i < end {
                        // Keep characters in the selection range
                        if *ch == ' ' {
                            masked[i] = '•';
                        } else {
                            masked[i] = *ch; // (line breaks kept, arrows added later)
                        }
                    } else {
                        // Replace characters outside the range
                        if *ch == '\n' || *ch == '\r' {
                            masked[i] = *ch;
                        } else {
                            masked[i] = ' ';
                        }
                    }
                }

                let mut masked_str: String = masked.into_iter().collect();

                // Add line break arrows
                masked_str = masked_str.replace('\n', "↲\n");
                masked_str = masked_str.replace('\r', "↲\r");

                // Remove blank lines
                let non_blank_lines: Vec<&str> = masked_str
                    .split('\n')
                    .filter(|line| {
                        let trimmed = line.trim();
                        !trimmed.is_empty() && trimmed != "↲"
                    })
                    .collect();
                masked_str = non_blank_lines.join("\n");

                // Find leading and trailing width of non-whitespace characters
                let masked_runes: Vec<char> = masked_str.chars().collect();
                let is_real_character = |ch: char| {
                    ch != '•' && ch != '↲' && !is_white_space_like(ch)
                };

                let leading_width = masked_runes.iter().position(|ch| is_real_character(*ch));
                let trailing_width = masked_runes.iter().rposition(|ch| is_real_character(*ch));

                if let (Some(leading), Some(trailing)) = (leading_width, trailing_width) {
                    if leading <= trailing {
                        // Clean up middle section
                        let prefix: String = masked_runes[..leading].iter().collect();
                        let middle: String = masked_runes[leading..=trailing].iter().collect();
                        let suffix: String = masked_runes[trailing + 1..].iter().collect();

                        let middle = middle.replace('•', " ").replace('↲', "");
                        masked_str = format!("{prefix}{middle}{suffix}");
                    }
                }

                // Add blank line before multi-line ranges
                if masked_str.contains('\n') {
                    result.push_str(new_line);
                }

                result.push_str(&masked_str);
                if !masked_str.ends_with('\n') {
                    result.push_str(new_line);
                }

                selection_range = sr.parent.clone().map(|p| *p);
            }
        }
        self.add_result_to_baseline(
            baselineutil::SMART_SELECTION_CMD,
            result.trim_end_matches('\n'),
        );
    }

    /// `VerifyBaselineCallHierarchy`
    pub fn verify_baseline_call_hierarchy(&mut self) {
        let file_name = self.active_filename.clone();
        let position = self.current_caret_position;

        let params = CallHierarchyPrepareParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&file_name),
            },
            position,
            ..Default::default()
        };

        let prepare_result = self.send_request(&TEXT_DOCUMENT_PREPARE_CALL_HIERARCHY_INFO, params);
        if prepare_result
            .call_hierarchy_items
            .as_ref()
            .is_none_or(|i| i.is_empty())
        {
            self.add_result_to_baseline(
                baselineutil::CALL_HIERARCHY_CMD,
                "No call hierarchy items available",
            );
            return;
        }

        let mut result = String::new();

        for call_hierarchy_item in prepare_result.call_hierarchy_items.unwrap() {
            let mut seen: HashMap<CallHierarchyItemKey, bool> = HashMap::new();
            let item_file_name = call_hierarchy_item.uri.file_name();
            self.get_or_load_script_info(&item_file_name);
            self.format_call_hierarchy_item(
                &item_file_name,
                &mut result,
                &call_hierarchy_item,
                CallHierarchyItemDirection::Root,
                &mut seen,
                "",
            );
        }

        self.add_result_to_baseline(
            baselineutil::CALL_HIERARCHY_CMD,
            result.trim_end_matches('\n'),
        );
    }

    /// `formatCallHierarchyItem`
    fn format_call_hierarchy_item(
        &mut self,
        file: &RootedFilePath,
        result: &mut String,
        call_hierarchy_item: &CallHierarchyItem,
        direction: CallHierarchyItemDirection,
        seen: &mut HashMap<CallHierarchyItemKey, bool>,
        prefix: &str,
    ) {
        let key = CallHierarchyItemKey {
            uri: call_hierarchy_item.uri.clone(),
            range: range_key(&call_hierarchy_item.range),
            direction,
        };
        let already_seen = seen.contains_key(&key);
        seen.insert(key, true);

        let mut incoming_calls = IncomingCallResult::default();
        let mut outgoing_calls = OutgoingCallResult::default();

        if direction == CallHierarchyItemDirection::Outgoing {
            incoming_calls.skip = true;
        } else if already_seen {
            incoming_calls.seen = true;
        } else {
            let incoming_params = CallHierarchyIncomingCallsParams {
                work_done_token: None,
                partial_result_token: None,
                item: Some(call_hierarchy_item.clone()),
            };
            let incoming_result =
                self.send_request(&CALL_HIERARCHY_INCOMING_CALLS_INFO, incoming_params);
            if let Some(calls) = incoming_result.call_hierarchy_incoming_calls {
                incoming_calls.values = calls;
            }
        }

        if direction == CallHierarchyItemDirection::Incoming {
            outgoing_calls.skip = true;
        } else if already_seen {
            outgoing_calls.seen = true;
        } else {
            let outgoing_params = CallHierarchyOutgoingCallsParams {
                work_done_token: None,
                partial_result_token: None,
                item: Some(call_hierarchy_item.clone()),
            };
            let outgoing_result =
                self.send_request(&CALL_HIERARCHY_OUTGOING_CALLS_INFO, outgoing_params);
            if let Some(calls) = outgoing_result.call_hierarchy_outgoing_calls {
                outgoing_calls.values = calls;
            }
        }

        let trailing_prefix = prefix.to_string();
        writeln!(result, "{prefix}╭ name: {}", call_hierarchy_item.name).unwrap();
        writeln!(
            result,
            "{prefix}├ kind: {}",
            symbol_kind_to_lowercase(call_hierarchy_item.kind)
        )
        .unwrap();
        if let Some(detail) = &call_hierarchy_item.detail {
            if !detail.is_empty() {
                writeln!(result, "{prefix}├ containerName: {detail}").unwrap();
            }
        }
        writeln!(
            result,
            "{prefix}├ file: {}",
            call_hierarchy_item.uri.file_name().as_string()
        )
        .unwrap();
        result.push_str(prefix);
        result.push_str("├ span:\n");
        self.format_call_hierarchy_item_span(
            file,
            result,
            &call_hierarchy_item.range,
            &format!("{prefix}│ "),
            &format!("{prefix}│ "),
        );
        result.push_str(prefix);
        result.push_str("├ selectionSpan:\n");
        self.format_call_hierarchy_item_span(
            file,
            result,
            &call_hierarchy_item.selection_range,
            &format!("{prefix}│ "),
            &format!("{prefix}│ "),
        );

        // Handle incoming calls
        if incoming_calls.seen {
            if outgoing_calls.skip {
                result.push_str(&trailing_prefix);
                result.push_str("╰ incoming: ...\n");
            } else {
                result.push_str(prefix);
                result.push_str("├ incoming: ...\n");
            }
        } else if !incoming_calls.skip {
            if incoming_calls.values.is_empty() {
                if outgoing_calls.skip {
                    result.push_str(&trailing_prefix);
                    result.push_str("╰ incoming: none\n");
                } else {
                    result.push_str(prefix);
                    result.push_str("├ incoming: none\n");
                }
            } else {
                result.push_str(prefix);
                result.push_str("├ incoming:\n");
                for (i, incoming_call) in incoming_calls.values.iter().enumerate() {
                    let from_file_name = incoming_call.from.as_ref().unwrap().uri.file_name();
                    self.get_or_load_script_info(&from_file_name);
                    result.push_str(prefix);
                    result.push_str("│ ╭ from:\n");
                    self.format_call_hierarchy_item(
                        &from_file_name,
                        result,
                        incoming_call.from.as_ref().unwrap(),
                        CallHierarchyItemDirection::Incoming,
                        seen,
                        &format!("{prefix}│ │ "),
                    );
                    result.push_str(prefix);
                    result.push_str("│ ├ fromSpans:\n");

                    let mut from_spans_trailing_prefix = format!("{trailing_prefix}╰ ╰ ");
                    if i < incoming_calls.values.len() - 1 {
                        from_spans_trailing_prefix = format!("{prefix}│ ╰ ");
                    } else if !outgoing_calls.skip
                        && (!outgoing_calls.seen || !outgoing_calls.values.is_empty())
                    {
                        from_spans_trailing_prefix = format!("{prefix}│ ╰ ");
                    }
                    self.format_call_hierarchy_item_spans(
                        &from_file_name,
                        result,
                        incoming_call.from_ranges.as_deref().unwrap_or(&[]),
                        &format!("{prefix}│ │ "),
                        &from_spans_trailing_prefix,
                    );
                }
            }
        }

        // Handle outgoing calls
        if outgoing_calls.seen {
            result.push_str(&trailing_prefix);
            result.push_str("╰ outgoing: ...\n");
        } else if !outgoing_calls.skip {
            if outgoing_calls.values.is_empty() {
                result.push_str(&trailing_prefix);
                result.push_str("╰ outgoing: none\n");
            } else {
                result.push_str(prefix);
                result.push_str("├ outgoing:\n");
                for (i, outgoing_call) in outgoing_calls.values.iter().enumerate() {
                    let to_file_name = outgoing_call.to.as_ref().unwrap().uri.file_name();
                    self.get_or_load_script_info(&to_file_name);
                    result.push_str(prefix);
                    result.push_str("│ ╭ to:\n");
                    self.format_call_hierarchy_item(
                        &to_file_name,
                        result,
                        outgoing_call.to.as_ref().unwrap(),
                        CallHierarchyItemDirection::Outgoing,
                        seen,
                        &format!("{prefix}│ │ "),
                    );
                    result.push_str(prefix);
                    result.push_str("│ ├ fromSpans:\n");

                    let mut from_spans_trailing_prefix = format!("{trailing_prefix}╰ ╰ ");
                    if i < outgoing_calls.values.len() - 1 {
                        from_spans_trailing_prefix = format!("{prefix}│ ╰ ");
                    }
                    self.format_call_hierarchy_item_spans(
                        file,
                        result,
                        outgoing_call.from_ranges.as_deref().unwrap_or(&[]),
                        &format!("{prefix}│ │ "),
                        &from_spans_trailing_prefix,
                    );
                }
            }
        }
    }

    /// `formatCallHierarchyItemSpan`
    fn format_call_hierarchy_item_span(
        &self,
        file: &RootedFilePath,
        result: &mut String,
        span: &Range,
        prefix: &str,
        closing_prefix: &str,
    ) {
        let script = self.get_script_info_or_panic(file);
        let start_lc = span.start;
        let end_lc = span.end;
        let converters = self.test_converters();
        let start_pos = converters.line_and_character_to_position(script, span.start);
        let end_pos = converters.line_and_character_to_position(script, span.end);

        // Compute line starts for the file
        let line_starts = compute_line_starts(&script.content);

        // Find the line boundaries - expand to full lines
        let mut context_start = start_pos as usize;
        let mut context_end = end_pos as usize;
        let content = script.content.as_bytes();

        // Expand to start of first line
        while context_start > 0
            && content[context_start - 1] != b'\n'
            && content[context_start - 1] != b'\r'
        {
            context_start -= 1;
        }

        // Expand to end of last line
        while context_end < content.len()
            && content[context_end] != b'\n'
            && content[context_end] != b'\r'
        {
            context_end += 1;
        }

        // Get actual line and character positions for the context
        let context_start_line = start_lc.line as usize;
        let context_end_line = end_lc.line as usize;

        // Calculate line number padding
        let line_num_width = (context_end_line + 1).to_string().len() + 2;

        writeln!(
            result,
            "{prefix}╭ {}:{}:{}-{}:{}",
            script.file_name.as_string(),
            start_lc.line + 1,
            start_lc.character + 1,
            end_lc.line + 1,
            end_lc.character + 1
        )
        .unwrap();

        for line_num in context_start_line..=context_end_line {
            let line_start = line_starts[line_num];
            let line_end = if line_num + 1 < line_starts.len() {
                line_starts[line_num + 1]
            } else {
                script.content.len()
            };

            // Get the line content, trimming trailing newlines
            let line_content = script.content[line_start..line_end]
                .trim_end_matches(['\r', '\n'])
                .to_string();

            // Format with line number
            let line_num_str = format!("{}:", line_num + 1);
            let padded_line_num =
                format!("{}{}", " ".repeat(line_num_width - line_num_str.len() - 1), line_num_str);
            if line_content.is_empty() {
                writeln!(result, "{prefix}│ {padded_line_num}").unwrap();
            } else {
                writeln!(result, "{prefix}│ {padded_line_num} {line_content}").unwrap();
            }

            // Add selection carets if this line contains part of the span
            if line_num >= start_lc.line as usize && line_num <= end_lc.line as usize {
                let mut sel_start = 0usize;
                let mut sel_end = line_content.len();

                if line_num == start_lc.line as usize {
                    sel_start = start_lc.character as usize;
                }
                if line_num == end_lc.line as usize {
                    sel_end = end_lc.character as usize;
                }

                // Don't show carets for empty selections
                let is_empty =
                    start_lc.line == end_lc.line && start_lc.character == end_lc.character;
                if is_empty {
                    // For empty selections, show a single "<" character
                    let padding = " ".repeat(line_num_width + sel_start);
                    writeln!(result, "{prefix}│ {padding}<").unwrap();
                } else {
                    // Calculate selection length (at least 1)
                    let mut sel_length = sel_end.saturating_sub(sel_start).max(1); // Trim to actual content on the line
                    if line_num < end_lc.line as usize {
                        // For lines before the last, trim to line content length
                        if sel_end > line_content.len() {
                            sel_end = line_content.len();
                            sel_length = sel_end - sel_start;
                        }
                    }

                    let padding = " ".repeat(line_num_width + sel_start);
                    let carets = "^".repeat(sel_length);
                    writeln!(result, "{prefix}│ {padding}{carets}").unwrap();
                }
            }
        }

        result.push_str(closing_prefix);
        result.push_str("╰\n");
    }

    /// `formatCallHierarchyItemSpans`
    fn format_call_hierarchy_item_spans(
        &self,
        file: &RootedFilePath,
        result: &mut String,
        spans: &[Range],
        prefix: &str,
        trailing_prefix: &str,
    ) {
        for (i, span) in spans.iter().enumerate() {
            let closing_prefix = if i == spans.len() - 1 {
                trailing_prefix
            } else {
                prefix
            };
            self.format_call_hierarchy_item_span(file, result, span, prefix, closing_prefix);
        }
    }

    /// `VerifyBaselineDocumentHighlights`
    pub fn verify_baseline_document_highlights(
        &mut self,
        preferences: Option<&UserPreferences>,
        marker_or_range_or_names: impl IntoIterator<Item = MarkerOrRangeOrName>,
    ) {
        self.verify_baseline_document_highlights_with_options(
            preferences,
            &[],
            marker_or_range_or_names,
        );
    }

    /// `VerifyBaselineDocumentHighlightsWithOptions`
    pub fn verify_baseline_document_highlights_with_options(
        &mut self,
        preferences: Option<&UserPreferences>,
        files_to_search: &[String],
        marker_or_range_or_names: impl IntoIterator<Item = MarkerOrRangeOrName>,
    ) {
        let marker_or_ranges = marker_or_ranges_from_names(self, marker_or_range_or_names);
        self.verify_baseline_document_highlights_impl(
            preferences,
            files_to_search,
            &marker_or_ranges,
        );
    }

    /// `verifyBaselineDocumentHighlights`
    fn verify_baseline_document_highlights_impl(
        &mut self,
        _preferences: Option<&UserPreferences>,
        files_to_search: &[String],
        marker_or_ranges: &[Rc<dyn MarkerOrRange>],
    ) {
        for marker_or_range in marker_or_ranges {
            self.go_to_marker_impl(marker_or_range);

            let mut spans: Vec<Location> = vec![];
            let mut header = String::new();

            if !files_to_search.is_empty() {
                // Multi-file: use the custom method.
                let search_uris: Vec<DocumentUri> = files_to_search
                    .iter()
                    .map(|file| {
                        lsconv::file_name_to_document_uri(&tspath::to_rooted_file_path(
                            file,
                            &root_dir(),
                        ))
                    })
                    .collect();

                let params = MultiDocumentHighlightParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&self.active_filename),
                    },
                    position: self.current_caret_position,
                    files_to_search: Some(search_uris),
                };
                let result =
                    self.send_request(&CUSTOM_TEXT_DOCUMENT_MULTI_DOCUMENT_HIGHLIGHT_INFO, params);
                let multi_highlights = result.multi_document_highlights.unwrap_or_default();

                for mh in &multi_highlights {
                    for h in mh.highlights.as_deref().unwrap_or(&[]) {
                        spans.push(Location {
                            uri: mh.uri.clone(),
                            range: h.range.clone(),
                        });
                    }
                }

                header.push_str("// filesToSearch:\n");
                for file in files_to_search {
                    writeln!(header, "//   {file}").unwrap();
                }
                header.push('\n');
            } else {
                // Single-file: use the standard LSP method.
                let params = DocumentHighlightParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&self.active_filename),
                    },
                    position: self.current_caret_position,
                    ..Default::default()
                };
                let result = self.send_request(&TEXT_DOCUMENT_DOCUMENT_HIGHLIGHT_INFO, params);
                let highlights = result.document_highlights.unwrap_or_default();

                for h in &highlights {
                    spans.push(Location {
                        uri: lsconv::file_name_to_document_uri(&self.active_filename),
                        range: h.range.clone(),
                    });
                }
            }

            // Add result to baseline
            let baseline = self.get_baseline_for_locations_with_file_contents(
                &spans,
                BaselineFourslashLocationsOptions {
                    marker: Some(marker_or_range.clone()),
                    marker_name: "/*HIGHLIGHTS*/".to_string(),
                    ..Default::default()
                },
            );
            self.add_result_to_baseline(
                baselineutil::DOCUMENT_HIGHLIGHTS_CMD,
                &format!("{header}{baseline}"),
            );
        }
    }

    /// `VerifyBaselineRename`
    pub fn verify_baseline_rename(
        &mut self,
        preferences: Option<&UserPreferences>,
        marker_or_name_or_ranges: impl IntoIterator<Item = MarkerOrRangeOrName>,
    ) {
        let marker_or_ranges = marker_or_ranges_from_names(self, marker_or_name_or_ranges);
        self.verify_baseline_rename_impl(preferences, &marker_or_ranges);
    }

    /// `verifyBaselineRename`
    fn verify_baseline_rename_impl(
        &mut self,
        preferences: Option<&UserPreferences>,
        marker_or_ranges: &[Rc<dyn MarkerOrRange>],
    ) {
        if let Some(prefs) = preferences {
            let original = self.configure_with_reset(prefs.clone());
            self.verify_baseline_rename_worker(preferences, marker_or_ranges);
            self.configure(original);
            return;
        }
        self.verify_baseline_rename_worker(preferences, marker_or_ranges);
    }

    fn verify_baseline_rename_worker(
        &mut self,
        preferences: Option<&UserPreferences>,
        marker_or_ranges: &[Rc<dyn MarkerOrRange>],
    ) {
        for marker_or_range in marker_or_ranges {
            self.go_to_marker_or_range(marker_or_range);

            let params = RenameParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                position: self.current_caret_position,
                new_name: "?".to_string(),
                ..Default::default()
            };

            let result = self.send_request(&TEXT_DOCUMENT_RENAME_INFO, params);

            let changes = result
                .workspace_edit
                .as_ref()
                .and_then(|e| e.changes.clone())
                .unwrap_or_default();
            let mut span_to_text_map: BTreeMap<DocumentSpanKey, String> = BTreeMap::new();
            let mut file_to_span: MultiMap<DocumentUri, DocumentSpan> = MultiMap::default();
            for (uri, edits) in &changes {
                for edit in edits {
                    let span = DocumentSpan {
                        uri: uri.clone(),
                        text_span: edit.range.clone(),
                        context_span: None,
                    };
                    file_to_span.add(uri.clone(), span.clone());
                    span_to_text_map.insert(DocumentSpanKey::from(&span), edit.new_text.clone());
                }
            }

            let mut rename_options = String::new();
            if let Some(prefs) = preferences {
                if prefs.provide_prefix_and_suffix_text_for_rename != TS_UNKNOWN {
                    writeln!(
                        rename_options,
                        "// @useAliasesForRename: {}",
                        prefs.provide_prefix_and_suffix_text_for_rename.is_true()
                    )
                    .unwrap();
                }
                if prefs.quote_preference != lsutil::QuotePreference::UNKNOWN {
                    writeln!(
                        rename_options,
                        "// @quotePreference: {}",
                        prefs.quote_preference.as_str()
                    )
                    .unwrap();
                }
            }

            // PORT: `Rc` shares the map between the two boxed callbacks.
            let span_to_text = Rc::new(span_to_text_map);
            let baseline_file_content = self.get_baseline_for_grouped_spans_with_file_contents(
                &file_to_span,
                &BaselineFourslashLocationsOptions {
                    marker: Some(marker_or_range.clone()),
                    marker_name: "/*RENAME*/".to_string(),
                    end_marker: "RENAME|]".to_string(),
                    start_marker_prefix: Some(Box::new({
                        let span_to_text = span_to_text.clone();
                        move |span: &DocumentSpan| {
                            let text = span_to_text.get(&DocumentSpanKey::from(span))?;
                            let prefix_and_suffix: Vec<&str> = text.split('?').collect();
                            if !prefix_and_suffix[0].is_empty() {
                                return Some(format!("/*START PREFIX*/{}", prefix_and_suffix[0]));
                            }
                            None
                        }
                    })),
                    end_marker_suffix: Some(Box::new({
                        let span_to_text = span_to_text.clone();
                        move |span: &DocumentSpan| {
                            let text = span_to_text.get(&DocumentSpanKey::from(span))?;
                            let prefix_and_suffix: Vec<&str> = text.split('?').collect();
                            if prefix_and_suffix.len() > 1 && !prefix_and_suffix[1].is_empty() {
                                return Some(format!("{}/*END SUFFIX*/", prefix_and_suffix[1]));
                            }
                            None
                        }
                    })),
                    ..Default::default()
                },
            );

            let baseline_result = if !rename_options.is_empty() {
                format!("{rename_options}\n{baseline_file_content}")
            } else {
                baseline_file_content
            };

            self.add_result_to_baseline(baselineutil::RENAME_CMD, &baseline_result);
        }
    }

    /// `VerifyBaselineRenameAtRangesWithText`
    pub fn verify_baseline_rename_at_ranges_with_text(
        &mut self,
        preferences: Option<&UserPreferences>,
        texts: &[String],
    ) {
        let mut marker_or_ranges: Vec<Rc<dyn MarkerOrRange>> = vec![];
        for text in texts {
            for r in self.get_ranges_by_text().get(text).to_vec() {
                marker_or_ranges.push(r as Rc<dyn MarkerOrRange>);
            }
        }
        self.verify_baseline_rename_impl(preferences, &marker_or_ranges);
    }

    /// `VerifyBaselineInlayHints`
    pub fn verify_baseline_inlay_hints(
        &mut self,
        span: Option<Range>,
        test_preferences: Option<&UserPreferences>,
    ) {
        let file_name = self.active_filename.clone();
        let lsp_range = match span {
            None => {
                let script = self.get_script_info_or_panic(&file_name);
                let len = script.content.len();
                self.test_converters()
                    .converters
                    .to_lsp_range(script, TextRange::new(0, len as i32))
                    .0
            }
            Some(span) => span,
        };

        let params = InlayHintParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&file_name),
            },
            range: lsp_range.clone(),
            ..Default::default()
        };

        let preferences = test_preferences
            .cloned()
            .unwrap_or_else(lsutil::new_default_user_preferences);
        let original = self.configure_with_reset(preferences);

        let prefix = format!(
            "At position (Ln {}, Col {}): ",
            lsp_range.start.line, lsp_range.start.character
        );
        let result = self.send_request(&TEXT_DOCUMENT_INLAY_HINT_INFO, params);
        let file_content = self.get_script_info_or_panic(&file_name).content.clone();
        let file_lines: Vec<&str> = file_content.split('\n').collect();
        let mut annotations: Vec<String> = vec![];
        if let Some(inlay_hints) = result.inlay_hints {
            let mut inlay_hints = inlay_hints;
            inlay_hints.sort_by(|a, b| compare_positions(&a.position, &b.position).cmp(&0));
            annotations = map(&inlay_hints, |hint| {
                // PORT: clone so we can zero out lib-file ranges before
                // stringifying (Go mutates the response in place).
                let mut hint = hint.clone();
                if let Some(parts) = &mut hint.label.inlay_hint_label_parts {
                    for part in parts {
                        // Avoid diffs caused by lib file updates.
                        if let Some(location) = &mut part.location {
                            if crate::fourslash::is_lib_file(location.uri.file_name().as_string()) {
                                location.range.start = Position {
                                    line: 0,
                                    character: 0,
                                };
                                location.range.end = Position {
                                    line: 0,
                                    character: 0,
                                };
                            }
                        }
                    }
                }
                let underline = " ".repeat(hint.position.character as usize) + "^";
                let hint_json = match stringify_json(&hint, "", "  ") {
                    Ok(j) => j,
                    Err(err) => {
                        panic!("{prefix}Failed to stringify inlay hint for baseline: {err}")
                    }
                };
                let mut annotation = file_lines[hint.position.line as usize].to_string();
                annotation += &format!("\n{underline}\n{hint_json}");
                annotation
            });
        }

        if annotations.is_empty() {
            annotations.push("=== No inlay hints ===".to_string());
        }

        self.add_result_to_baseline(baselineutil::INLAY_HINTS_CMD, &annotations.join("\n\n"));
        self.configure(original);
    }

    /// `VerifyBaselineLinkedEditing`
    pub fn verify_baseline_linked_editing(&mut self) {
        let mut baseline_builder = String::new();
        let mut offset = 0;

        // write to baseline in order of file appearance in test data
        for file in self.test_data.files.clone() {
            baseline_builder.push_str("// === Linked Editing ===\n");
            writeln!(baseline_builder, "=== {} ===", file.file_name().as_string()).unwrap();
            let mut results: Vec<LinkedEditingRanges> = vec![];
            let mut found: std::collections::HashSet<(u32, u32, u32, u32)> = std::collections::HashSet::new();

            // request linkedEditing at every position in the file
            for i in file.content.char_indices().map(|(i, _)| i) {
                let position = {
                    let script = self.get_script_info_or_panic(&file.file_name());
                    self.test_converters()
                        .position_to_line_and_character(script, i as i32)
                };
                let params = LinkedEditingRangeParams {
                    text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&file.file_name()),
                    },
                    position,
                    ..Default::default()
                };
                let result = self.send_request(&TEXT_DOCUMENT_LINKED_EDITING_RANGE_INFO, params);
                if let Some(ranges) = result.linked_editing_ranges {
                    if !ranges.ranges.as_deref().unwrap_or(&[]).is_empty() && !found.contains(&range_key(&ranges.ranges.as_deref().unwrap()[0])) {
                        found.insert(range_key(&ranges.ranges.as_deref().unwrap()[0]));
                        results.push(ranges);
                    }
                }
            }

            if results.is_empty() {
                writeln!(baseline_builder, "{}\n\n--No linked edits found--\n\n", file.content)
                    .unwrap();
                continue;
            }

            // sort entries in each file
            results.sort_by(|a, b| {
                compare_positions(&a.ranges.as_deref().unwrap()[0].start, &b.ranges.as_deref().unwrap()[0].start).cmp(&0)
            });
            let mut baseline_details: Vec<LocalBaselineDetail> = vec![];
            let mut found_edit_info_builder = String::new();
            for edit in &results {
                baseline_details.push(LocalBaselineDetail {
                    pos: edit.ranges.as_deref().unwrap_or(&[])[0].start,
                    position_marker: format!("[|/*{offset}*/"),
                });
                baseline_details.push(LocalBaselineDetail {
                    pos: edit.ranges.as_deref().unwrap_or(&[])[0].end,
                    position_marker: "|]".to_string(),
                });
                baseline_details.push(LocalBaselineDetail {
                    pos: edit.ranges.as_deref().unwrap_or(&[])[1].start,
                    position_marker: format!("[|/*{offset}*/"),
                });
                baseline_details.push(LocalBaselineDetail {
                    pos: edit.ranges.as_deref().unwrap_or(&[])[1].end,
                    position_marker: "|]".to_string(),
                });

                write!(
                    found_edit_info_builder,
                    "\n\n=== {offset} ===\n{}",
                    must(stringify_json(edit, "", "  "))
                )
                .unwrap();
                offset += 1;
            }

            // sort baselineDetails by position
            baseline_details.sort_by(|a, b| compare_positions(&a.pos, &b.pos).cmp(&0));

            // write file content with inline annotations for linked edits
            let mut last_position = 0usize;
            for detail in &baseline_details {
                let current_position = {
                    let script = self.get_script_info_or_panic(&file.file_name());
                    self.test_converters()
                        .line_and_character_to_position(script, detail.pos)
                        as usize
                };
                baseline_builder.push_str(&file.content[last_position..current_position]);
                baseline_builder.push_str(&detail.position_marker);
                last_position = current_position;
            }
            baseline_builder.push_str(&file.content[last_position..]);
            baseline_builder.push_str(&found_edit_info_builder);
            baseline_builder.push_str("\n\n\n");
        }

        self.write_to_baseline(baselineutil::LINKED_EDITING_CMD, &baseline_builder);
    }

    /// `VerifyBaselineNonSuggestionDiagnostics`
    pub fn verify_baseline_non_suggestion_diagnostics(&mut self) {
        let mut diagnostics: Vec<FourslashDiagnostic> = vec![];
        let mut files: Vec<TestFile> = vec![];
        for file_name in self.script_infos.keys().cloned().collect::<Vec<_>>() {
            if file_name.as_string().ends_with(".json") {
                continue;
            }
            files.push(TestFile {
                unit_name: file_name.as_string().to_string(),
                content: self.script_infos[&file_name].content.clone(),
            });
            let all_diagnostics = self.get_diagnostics(&file_name);
            let lsp_diagnostics = filter(&all_diagnostics, |d| {
                !is_suggestion_diagnostic(d)
            });
            let script_info = &self.script_infos[&file_name];
            diagnostics.extend(
                lsp_diagnostics
                    .iter()
                    .map(|d| self.to_diagnostic(script_info, d)),
            );
        }
        files.sort_by(|a, b| a.unit_name.cmp(&b.unit_name));
        let result = tsbaseline::get_error_baseline(
            &files,
            &diagnostics,
            compare_diagnostics,
            false, /*pretty*/
        );
        self.add_result_to_baseline(baselineutil::NON_SUGGESTION_DIAGNOSTICS_CMD, &result);
    }

    /// `toDiagnostic`
    fn to_diagnostic(&self, script_info: &ScriptInfo, lsp_diagnostic: &Diagnostic) -> FourslashDiagnostic {
        let category = match lsp_diagnostic.severity {
            Some(DiagnosticSeverity::Error) => Category::Error,
            Some(DiagnosticSeverity::Warning) => Category::Warning,
            Some(DiagnosticSeverity::Information) => Category::Message,
            Some(DiagnosticSeverity::Hint) => Category::Suggestion,
            _ => Category::Error,
        };
        let code = lsp_diagnostic
            .code
            .as_ref()
            .and_then(|c| c.integer)
            .unwrap_or(0);

        let mut related_diagnostics: Vec<FourslashDiagnostic> = vec![];
        if let Some(related_information) = &lsp_diagnostic.related_information {
            for info in related_information {
                let related_file = info.location.uri.file_name();
                let Some(related_script_info) = self.get_script_info(&related_file) else {
                    continue;
                };
                related_diagnostics.push(FourslashDiagnostic {
                    file: FileLike::from_text(
                        related_script_info.file_name.clone(),
                        related_script_info.content.clone(),
                    ),
                    loc: self.from_lsp_range(related_script_info, info.location.range.clone()),
                    code,
                    category,
                    message: info.message.clone(),
                    related_diagnostics: vec![],
                    reports_unnecessary: false,
                    reports_deprecated: false,
                });
            }
        }

        FourslashDiagnostic {
            file: FileLike::from_text(
                script_info.file_name.clone(),
                script_info.content.clone(),
            ),
            loc: self.from_lsp_range(script_info, lsp_diagnostic.range.clone()),
            code,
            category,
            message: lsp_diagnostic.message.as_string().to_string(),
            related_diagnostics,
            reports_unnecessary: false,
            reports_deprecated: false,
        }
    }

    /// `VerifyBaselineDocumentSymbol`
    pub fn verify_baseline_document_symbol(&mut self) {
        let params = DocumentSymbolParams {
            text_document: TextDocumentIdentifier {
                uri: lsconv::file_name_to_document_uri(&self.active_filename),
            },
            ..Default::default()
        };
        let result = self.send_request(&TEXT_DOCUMENT_DOCUMENT_SYMBOL_INFO, params);
        let uri = lsconv::file_name_to_document_uri(&self.active_filename);
        let mut symbol_by_span: BTreeMap<DocumentSpanKeyValue, DocumentSymbol> = BTreeMap::new();
        if let Some(symbols) = &result.document_symbols {
            for symbol in symbols {
                collect_document_symbol_spans(&uri, symbol, &mut symbol_by_span);
            }
        }
        let spans: Vec<DocumentSpan> = symbol_by_span
            .iter()
            .map(|(key, symbol)| DocumentSpan {
                uri: key.uri.clone(),
                text_span: range_from_key(key.text_span),
                context_span: Some(symbol.range.clone()),
            })
            .collect();
        let baseline = self.get_baseline_for_spans_with_file_contents(
            &spans,
            BaselineFourslashLocationsOptions {
                get_location_data: Some(Box::new(move |span: &DocumentSpan| {
                    let key = DocumentSpanKeyValue {
                        uri: span.uri.clone(),
                        text_span: range_key(&span.text_span),
                        context_span: span
                            .context_span
                            .as_ref()
                            .map(range_key)
                            .unwrap_or_default(),
                    };
                    let symbol = symbol_by_span.get(&key).unwrap();
                    format!("{{| name: {}, kind: {} |}}", symbol.name, symbol.kind)
                })),
                ..Default::default()
            },
        );
        self.add_result_to_baseline(baselineutil::DOCUMENT_SYMBOLS_CMD, &baseline);

        let mut details_builder = String::new();
        if let Some(symbols) = &result.document_symbols {
            write_document_symbol_details(symbols, 0, &mut details_builder);
        }
        self.write_to_baseline(
            baselineutil::DOCUMENT_SYMBOLS_CMD,
            &format!("\n\n// === Details ===\n{details_builder}"),
        );
    }

    /// `VerifyBaselineClosingTags` generates a baseline for JSX closing tag
    /// completions at all markers.
    pub fn verify_baseline_closing_tags(&mut self) {
        let markers_and_items: Vec<MarkerAndItem<Option<VSOnAutoInsertResponseItem>>> = map_filtered(
            &self.test_data.markers.clone(),
            |marker| {
                if marker.as_ref().name.is_none() {
                    return None;
                }
                let (file_name, position) = {
                    let m = marker.as_ref();
                    (m.file_name().clone(), m.ls_position)
                };
                let params = VSOnAutoInsertParams {
                    vs_text_document: TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&file_name),
                    },
                    vs_position: position,
                    vs_ch: ">".to_string(),
                };
                let result = self.send_request(&TEXT_DOCUMENT_VS_ON_AUTO_INSERT_INFO, params);
                Some(MarkerAndItem {
                    marker: marker.clone(),
                    item: result.vs_on_auto_insert_response_item,
                })
            },
        );

        let get_range = |_item: &Option<VSOnAutoInsertResponseItem>| -> Option<Range> {
            // Returning nil lets annotateContentWithTooltips render the caret marker at
            // the marker position. The text edit's range is zero-width at the cursor,
            // which would render as an empty underline.
            None
        };
        let get_tooltip_lines = |item: &Option<VSOnAutoInsertResponseItem>,
                                 _prev: &Option<VSOnAutoInsertResponseItem>|
         -> Vec<String> {
            let Some(item) = item else {
                return vec!["No closing tag".to_string()];
            };
            let Some(vs_text_edit) = &item.vs_text_edit else {
                return vec!["No closing tag".to_string()];
            };
            let format = if item.vs_text_edit_format == InsertTextFormat::Snippet {
                "snippet"
            } else {
                "plaintext"
            };
            vec![format!("{format}: {:?}", vs_text_edit.new_text)]
        };

        let baseline = self.annotate_content_with_tooltips(
            &markers_and_items,
            "closing tag",
            get_range,
            get_tooltip_lines,
        );
        self.add_result_to_baseline(baselineutil::CLOSING_TAG_CMD, &baseline);
    }

    /// `BaselineAutoImportsCompletions`
    pub fn baseline_auto_imports_completions(&mut self, marker_names: &[String]) {
        let prefs = UserPreferences {
            completion_preferences: lsutil::CompletionPreferences {
                include_completions_for_module_exports: TS_TRUE,
                include_completions_for_import_statements: TS_TRUE,
                ..Default::default()
            },
            import_module_specifier_preference: self
                .user_preferences
                .as_ref()
                .import_module_specifier_preference
                .clone(),
            import_module_specifier_ending: self
                .user_preferences
                .as_ref()
                .import_module_specifier_ending
                .clone(),
            auto_import_specifier_exclude_regexes: self
                .user_preferences
                .as_ref()
                .auto_import_specifier_exclude_regexes
                .clone(),
            auto_import_file_exclude_patterns: self
                .user_preferences
                .as_ref()
                .auto_import_file_exclude_patterns
                .clone(),
            prefer_type_only_auto_imports: self
                .user_preferences
                .as_ref()
                .prefer_type_only_auto_imports,
            auto_import_entrypoint_directory_search: self
                .user_preferences
                .as_ref()
                .auto_import_entrypoint_directory_search,
            ..Default::default()
        };
        let original = self.configure_with_reset(prefs);

        for marker_name in marker_names {
            self.go_to_marker(marker_name);
            let params = CompletionParams {
                text_document: TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&self.active_filename),
                },
                position: self.current_caret_position,
                context: Some(CompletionContext::default()),
                ..Default::default()
            };
            let result = self.send_request(&TEXT_DOCUMENT_COMPLETION_INFO, params);

            let prefix = format!("At marker '{marker_name}': ");

            self.write_to_baseline(baselineutil::AUTO_IMPORTS_CMD, "// === Auto Imports === \n");

            let Some(file_content) = self.text_of_file(&self.active_filename.clone()) else {
                panic!("{prefix}Failed to read file {} for auto-import baseline", self.active_filename.as_string());
            };

            let marker = self.test_data.marker_positions.get(marker_name).unwrap().clone();
            let ext = tspath::try_get_extension_from_path(self.active_filename.as_string())
                .trim_start_matches('.')
                .to_string();
            let lang = if ext == "mts" || ext == "cts" {
                "ts"
            } else {
                ext.as_str()
            };
            let marker_position = marker.as_ref().position as usize;
            self.write_to_baseline(
                baselineutil::AUTO_IMPORTS_CMD,
                &baselineutil::code_fence(
                    lang,
                    &format!(
                        "// @FileName: {}\n{}/*{marker_name}*/{}",
                        self.active_filename.as_string(),
                        &file_content[..marker_position],
                        &file_content[marker_position..]
                    ),
                ),
            );

            let current_file = new_script_info_from_file_name_public(
                self.active_filename.clone(),
                &file_content,
            );
            let converters = new_test_converters(lsconv::new_converters(
                PositionEncodingKind::UTF8,
                |_| &current_file.line_map,
            ));
            let list: Vec<CompletionItem> = match result.items {
                None => match &result.list {
                    None => {
                        self.write_to_baseline(
                            baselineutil::AUTO_IMPORTS_CMD,
                            "no autoimport completions found\n\n",
                        );
                        continue;
                    }
                    Some(list) if list.items.as_deref().unwrap_or(&[]).is_empty() => {
                        self.write_to_baseline(
                            baselineutil::AUTO_IMPORTS_CMD,
                            "no autoimport completions found\n\n",
                        );
                        continue;
                    }
                    Some(list) => list.items.clone().unwrap_or_default(),
                },
                Some(items) => items,
            };

            for item in &list {
                if item.data.is_none()
                    || item.sort_text.as_deref() != Some(crate::verify::SORT_TEXT_AUTO_IMPORT_SUGGESTIONS)
                {
                    continue;
                }
                let details = self.send_request(&COMPLETION_ITEM_RESOLVE_INFO, item.clone());
                let Some(all_changes) = details.and_then(|d| d.additional_text_edits) else {
                    panic!(
                        "{prefix}Entry {} from {:?} returned no code changes from completion details request",
                        item.label, item.detail
                    );
                };
                if all_changes.is_empty() {
                    panic!(
                        "{prefix}Entry {} from {:?} returned no code changes from completion details request",
                        item.label, item.detail
                    );
                }

                // sorted from back-of-file-most to front-of-file-most
                let mut all_changes = all_changes;
                all_changes.sort_by(|a, b| compare_positions(&b.range.start, &a.range.start).cmp(&0));
                let mut new_file_content = file_content.clone();
                for change in &all_changes {
                    let start =
                        converters.line_and_character_to_position(&current_file, change.range.start)
                            as usize;
                    let end =
                        converters.line_and_character_to_position(&current_file, change.range.end)
                            as usize;
                    new_file_content = format!(
                        "{}{}{}",
                        &new_file_content[..start],
                        change.new_text,
                        &new_file_content[end..]
                    );
                }
                self.write_to_baseline(
                    baselineutil::AUTO_IMPORTS_CMD,
                    &format!("{}\n\n", baselineutil::code_fence(lang, &new_file_content)),
                );
            }
        }
        self.configure(original);
    }
}

fn new_script_info_from_file_name_public(file_name: RootedFilePath, content: &str) -> ScriptInfo {
    crate::fourslash::new_script_info_from_file_name(file_name, content)
}

/// `renderVSContainerElement` renders a VS rich-content container element
/// (icon + colorized runs, possibly nested) into readable baseline lines.
fn render_vs_container_element(el: &VSContainerElement, indent: &str) -> Vec<String> {
    let mut lines = vec![format!("{indent}ContainerElement (Style={})", el.style)];
    let child_indent = format!("{indent}  ");
    for child in el.elements.as_deref().unwrap_or(&[]) {
        if let Some(image) = &child.image_element {
            // Go dereferences `ImageId` unconditionally; a nil pointer panics.
            let image_id = image.image_id.as_ref().expect("image_id");
            lines.push(format!(
                "{child_indent}ImageElement {{ Guid: {}, Id: 0x{:X} }}",
                image_id.guid, image_id.id
            ));
        } else if let Some(classified) = &child.classified_text_element {
            lines.push(format!("{child_indent}ClassifiedTextElement"));
            for run in classified.runs.as_deref().unwrap_or(&[]) {
                lines.push(format!(
                    "{child_indent}  [{}] {:?}",
                    run.classification_type_name, run.text
                ));
            }
        } else if let Some(container) = &child.container_element {
            lines.extend(render_vs_container_element(container, &child_indent));
        } else {
            lines.push(format!("{child_indent}<empty union element>"));
        }
    }
    lines
}

/// `appendLinesForMarkedStringWithLanguage`
fn append_lines_for_marked_string_with_language(
    mut result: Vec<String>,
    ms: &MarkedStringWithLanguage,
) -> Vec<String> {
    result.push(format!("```{}", ms.language));
    result.push(ms.value.clone());
    result.push("```".to_string());
    result
}

/// `type hoverWithVerbosity struct`
#[derive(Clone, Default, PartialEq, Serialize)]
struct HoverWithVerbosity {
    #[serde(rename = "hover")]
    hover: Option<Hover>,
    #[serde(rename = "verbosityLevel")]
    verbosity_level: i32,
}

/// `hoverContentString` extracts the text content from a hover response for comparison.
fn hover_content_string(hover: Option<&Hover>) -> String {
    let Some(hover) = hover else {
        return String::new();
    };
    if let Some(markup) = &hover.contents.markup_content {
        return markup.value.clone();
    }
    if let Some(s) = &hover.contents.string {
        return s.clone();
    }
    String::new()
}

/// `type callHierarchyItemDirection int`
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum CallHierarchyItemDirection {
    Root,
    Incoming,
    Outgoing,
}

/// `type callHierarchyItemKey struct`
#[derive(PartialEq, Eq, Hash)]
struct CallHierarchyItemKey {
    uri: DocumentUri,
    range: (u32, u32, u32, u32),
    direction: CallHierarchyItemDirection,
}

/// `(start.line, start.character, end.line, end.character)` — `Range`
/// doesn't implement `Eq`/`Hash`/`Ord`, so map/set keys use this tuple.
fn range_key(range: &Range) -> (u32, u32, u32, u32) {
    (
        range.start.line,
        range.start.character,
        range.end.line,
        range.end.character,
    )
}

/// Inverse of [`range_key`].
fn range_from_key(key: (u32, u32, u32, u32)) -> Range {
    Range {
        start: Position {
            line: key.0,
            character: key.1,
        },
        end: Position {
            line: key.2,
            character: key.3,
        },
    }
}

#[derive(Default)]
struct IncomingCallResult {
    skip: bool,
    seen: bool,
    values: Vec<CallHierarchyIncomingCall>,
}

#[derive(Default)]
struct OutgoingCallResult {
    skip: bool,
    seen: bool,
    values: Vec<CallHierarchyOutgoingCall>,
}

/// `type fourslashDiagnostic struct`
#[derive(Clone)]
struct FourslashDiagnostic {
    file: FileLike<'static>,
    loc: TextRange,
    code: i32,
    category: Category,
    message: String,
    related_diagnostics: Vec<FourslashDiagnostic>,
    reports_unnecessary: bool,
    reports_deprecated: bool,
}

impl DwDiagnostic for FourslashDiagnostic {
    fn file<'s>(&'s self) -> Option<FileLike<'s>> {
        Some(self.file.clone())
    }

    fn pos(&self) -> i32 {
        self.loc.pos()
    }

    fn end(&self) -> i32 {
        self.loc.end()
    }

    fn len(&self) -> i32 {
        self.loc.len()
    }

    fn code(&self) -> i32 {
        self.code
    }

    fn category(&self) -> Category {
        self.category
    }

    fn source(&self) -> String {
        String::new()
    }

    fn localize(&self, _locale: &Locale) -> String {
        self.message.clone()
    }

    fn message_chain<'s>(&'s self) -> Vec<Box<dyn DwDiagnostic + 's>> {
        vec![]
    }

    fn related_information<'s>(&'s self) -> Vec<Box<dyn DwDiagnostic + 's>> {
        self.related_diagnostics
            .iter()
            .map(|d| Box::new(d.clone()) as Box<dyn DwDiagnostic + 's>)
            .collect()
    }
}

/// `compareDiagnostics`
fn compare_diagnostics(d1: &FourslashDiagnostic, d2: &FourslashDiagnostic) -> i32 {
    let mut c = d1
        .file
        .file_name()
        .compare(d2.file.file_name());
    if c != 0 {
        return c;
    }
    c = d1.pos() - d2.pos();
    if c != 0 {
        return c;
    }
    c = d1.end() - d2.end();
    if c != 0 {
        return c;
    }
    c = d1.code - d2.code;
    if c != 0 {
        return c;
    }
    c = d1.message.cmp(&d2.message) as i32;
    if c != 0 {
        return c;
    }
    compare_related_diagnostics(&d1.related_diagnostics, &d2.related_diagnostics)
}

/// `compareRelatedDiagnostics`
fn compare_related_diagnostics(d1: &[FourslashDiagnostic], d2: &[FourslashDiagnostic]) -> i32 {
    let c = d2.len() as i32 - d1.len() as i32;
    if c != 0 {
        return c;
    }
    for i in 0..d1.len() {
        let c = compare_diagnostics(&d1[i], &d2[i]);
        if c != 0 {
            return c;
        }
    }
    0
}

/// `writeDocumentSymbolDetails`
fn write_document_symbol_details(symbols: &[DocumentSymbol], indent: usize, builder: &mut String) {
    for symbol in symbols {
        writeln!(
            builder,
            "{}({}) {}",
            "  ".repeat(indent),
            symbol.kind,
            symbol.name
        )
        .unwrap();
        if let Some(children) = &symbol.children {
            write_document_symbol_details(children, indent + 1, builder);
        }
    }
}

/// `documentSpanKey` — a value-comparable variant of `documentSpan` used to
/// deduplicate document symbols regardless of pointer identity.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct DocumentSpanKeyValue {
    uri: DocumentUri,
    text_span: (u32, u32, u32, u32),
    context_span: (u32, u32, u32, u32),
}

/// `DocumentSpan` map key — used where Go keys a map on `documentSpan` (which
/// holds a pointer contextSpan that can't hash); compare by value.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct DocumentSpanKey {
    uri: DocumentUri,
    text_span: (u32, u32, u32, u32),
    context_span: (u32, u32, u32, u32),
}

impl DocumentSpanKey {
    pub(crate) fn from(span: &DocumentSpan) -> DocumentSpanKey {
        DocumentSpanKey {
            uri: span.uri.clone(),
            text_span: range_key(&span.text_span),
            context_span: span
                .context_span
                .as_ref()
                .map(range_key)
                .unwrap_or_default(),
        }
    }
}

/// `collectDocumentSymbolSpans`
fn collect_document_symbol_spans(
    uri: &DocumentUri,
    symbol: &DocumentSymbol,
    symbol_by_span: &mut BTreeMap<DocumentSpanKeyValue, DocumentSymbol>,
) {
    // Deduplicate by value rather than by the documentSpan key, which holds a pointer to
    // the symbol's Range. The same logical symbol can be reached more than once
    // (e.g. a merged declaration), and depending on transport those occurrences may
    // be the same object (shared *Range) or independent copies (distinct *Range
    // after a JSON round-trip). A value-based key collapses them consistently.
    let key = DocumentSpanKeyValue {
        uri: uri.clone(),
        text_span: range_key(&symbol.selection_range),
        context_span: range_key(&symbol.range),
    };
    symbol_by_span.entry(key).or_insert_with(|| symbol.clone());
    if let Some(children) = &symbol.children {
        for child in children {
            collect_document_symbol_spans(uri, child, symbol_by_span);
        }
    }
}


/// `LocalBaselineDetail` — Go's `baselineDetail` is private to baselineutil.
struct LocalBaselineDetail {
    pos: Position,
    position_marker: String,
}
