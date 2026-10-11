// Ported from tsc/internal/testutil/tsbaseline/sourcemap_baseline.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::options_generated::CompilerOptions;
use tsc_tspath as tspath;

use super::js_emit_baseline::file_output;
use super::util::base64_encode_chunk;
use crate::baseline;
use crate::harnessutil::{CompilationResult, HarnessOptions, TestFile};

/// `DoSourcemapBaseline`.
#[allow(clippy::too_many_arguments)]
pub fn do_sourcemap_baseline(
    baseline_path: &str,
    header: &str,
    options: &CompilerOptions,
    result: &CompilationResult,
    harness_settings: &HarnessOptions,
    opts: baseline::Options,
) {
    let _ = header;
    let decl_maps = options.get_are_declaration_maps_enabled();
    if options.inline_source_map.is_true() {
        if result.maps.size() > 0 && !decl_maps {
            panic!("No sourcemap files should be generated if inlineSourceMaps was set.");
        }
        return;
    } else if options.source_map.is_true() || decl_maps {
        let mut expected_map_count = 0;
        if options.source_map.is_true() {
            expected_map_count += result.get_number_of_js_files(false /*include_json*/);
        }
        if decl_maps {
            expected_map_count += result.dts.size();
        }
        if result.maps.size() != expected_map_count {
            panic!("Number of sourcemap files should be same as js files.");
        }

        let source_map_code = if options.no_emit_on_error.is_true()
            && !result.diagnostics.is_empty()
            || result.maps.size() == 0
        {
            baseline::NO_CONTENT.to_string()
        } else {
            let mut source_map_code_builder = String::new();
            for source_map in result.maps.values() {
                if !source_map_code_builder.is_empty() {
                    source_map_code_builder.push_str("\r\n");
                }
                source_map_code_builder.push_str(&file_output(source_map, harness_settings));
                if !options.inline_source_map.is_true() {
                    source_map_code_builder
                        .push_str(&create_source_map_preview_link(source_map, result));
                }
            }
            source_map_code_builder
        };

        let mut baseline_path = baseline_path.to_string();
        if tspath::file_extension_is_one_of(
            &baseline_path,
            &[tspath::EXTENSION_TS, tspath::EXTENSION_TSX],
        ) {
            baseline_path =
                tspath::change_extension(&baseline_path, &format!("{}.map", tspath::EXTENSION_JS))
                    .into_owned();
        }

        baseline::run(&baseline_path, &source_map_code, &opts).unwrap_or_else(|e| panic!("{e}"));
    }
}

/// `createSourceMapPreviewLink`.
fn create_source_map_preview_link(source_map: &TestFile, result: &CompilationResult) -> String {
    // `json.Unmarshal([]byte(sourceMap.Content), &sourcemapJSON)` — only
    // `file`/`sources` are read, so decode via `serde_json::Value` rather
    // than `sourcemap.RawSourceMap` (which is serialize-only).
    let sourcemap_json: serde_json::Value =
        serde_json::from_str(&source_map.content).unwrap_or_else(|e| panic!("{e}"));
    let sourcemap_file = sourcemap_json
        .get("file")
        .and_then(|v| v.as_str())
        .unwrap_or_default()
        .to_string();

    let output_js_file = result
        .outputs()
        .iter()
        .find(|td| td.unit_name.ends_with(&sourcemap_file));

    // !!! Strada uses a fallible approach to associating inputs and outputs derived from a source map output. The
    // !!! commented logic below should be used after the Strada migration is complete:

    ////inputsAndOutputs := result.GetInputsAndOutputsForFile(sourceMap.UnitName)
    ////outputJSFile := inputsAndOutputs.Js

    let Some(output_js_file) = output_js_file else {
        return String::new();
    };

    ////if len(sourcemapJSON.Sources) == len(inputsAndOutputs.Inputs) {
    ////	sourceTDs = inputsAndOutputs.Inputs
    ////} else {
    let sources = sourcemap_json
        .get("sources")
        .and_then(|v| v.as_array())
        .cloned()
        .unwrap_or_default();
    let mut source_tds: Vec<TestFile> = Vec::with_capacity(sources.len());
    for s in &sources {
        let s = s.as_str().unwrap_or_default();
        let Some(source_file) = result.inputs().iter().find(|td| td.unit_name.ends_with(s)) else {
            // `slices.Contains(sourceTDs, nil)` — any missing source file
            // means no preview link.
            return String::new();
        };
        let mut td = (**source_file).clone();
        if let Some(program_source) = result.program.get_source_file(&tspath::to_rooted_file_path(
            &source_file.unit_name,
            &result.current_directory(),
        )) {
            let prog = result.program.program();
            let nodes = prog.arena_of(program_source);
            td.content = nodes[program_source]
                .as_source_file()
                .original_text()
                .to_string();
        }
        source_tds.push(td);
    }
    ////}

    let mut hash = String::new();
    hash.push_str("\n//// https://sokra.github.io/source-map-visualization#base64,");
    hash.push_str(&base64_encode_chunk(&output_js_file.content));
    hash.push(',');
    hash.push_str(&base64_encode_chunk(&source_map.content));
    for td in &source_tds {
        hash.push(',');
        hash.push_str(&base64_encode_chunk(&td.content));
    }
    hash.push('\n');
    hash
}
