// Ported from tsc/internal/api/encoder/encoder_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `parser.ParseSourceFile` returns `(NodeId, Vec<Node>)` and
// `encoder.EncodeSourceFile` returns `(Vec<u8>, NodeIndexTable)` — the arena
// is threaded explicitly. `baseline.Run`'s `*testing.T` errors come back as
// `Err` and are unwrapped. The `b.Loop()` benchmarks are kept as ignored
// single-iteration tests.

use tsc_ast::ast::ContentMapperSourceFileInfo;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::{Kind, MappedDiagnosticDirective, MappedDiagnosticDirectivePolicy};
use tsc_core::scriptkind::ScriptKind;
use tsc_core::text::TextRange;
use tsc_parser::parse_source_file;
use tsc_testutil::baseline;
use tsc_tspath::{path_key_from_canonical, rooted_file_path_from_normalized};

use crate::decoder_generated::kind_from_u32;
use crate::encoder::*;

// PORT: `testmain_test.go`'s `TestMain` holds `baseline.Track()` for the
// whole package and calls `core.ApplyDebugStackLimit()` (no Rust equivalent —
// test threads already use a larger stack). Rust has no per-package TestMain,
// so each baseline test holds a `track()` guard for its own duration.
fn track_baselines() -> baseline::TrackGuard {
    baseline::track()
}

fn read_uint32(buf: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(buf[offset..offset + 4].try_into().unwrap())
}

fn test_parse_options(file_name: &str) -> SourceFileParseOptions {
    SourceFileParseOptions {
        file_name: rooted_file_path_from_normalized(file_name),
        path_key: path_key_from_canonical(file_name),
        ..Default::default()
    }
}

#[test]
fn test_encode_source_file() {
    assert_eq!(HEADER_SIZE, 64);
    assert_eq!(NODE_SIZE, 28);
    let _baseline_tracking = track_baselines();
    let (file, mut nodes) = parse_source_file(
        test_parse_options("/test.ts"),
        "import { bar } from \"bar\";\nexport function foo<T, U>(a: string, b: string): any {}\nfoo();",
        ScriptKind::Ts,
    );
    let (buf, _table) = encode_source_file(&mut nodes, file);

    let s = format_encoded_source_file(&buf);
    baseline::run(
        "encodeSourceFile.txt",
        &s,
        &baseline::Options {
            subfolder: "api".to_string(),
            ..Default::default()
        },
    )
    .unwrap();
}

#[test]
fn test_encode_content_mapper_source_file_metadata() {
    assert_eq!(PROTOCOL_VERSION, 9, "protocol version");

    let (file, mut nodes) = parse_source_file(
        test_parse_options("/component.vue"),
        "\u{1F600}virtual",
        ScriptKind::Ts,
    );
    nodes[file]
        .as_source_file_mut()
        .set_content_mapper_info(ContentMapperSourceFileInfo {
            original_text: "\u{1F600}original".to_string(),
            content_mapper: "mapper@1.0.0".to_string(),
            virtual_file_name: rooted_file_path_from_normalized("/component.vue.ts"),
            diagnostic_directives: vec![MappedDiagnosticDirective {
                original_range: TextRange::new(4, 5),
                virtual_range: TextRange::new(4, 11),
                policy: MappedDiagnosticDirectivePolicy::Expect,
                unused_code: 2578,
                unused_message_text: "Unused framework directive.".to_string(),
                source: "mapper".to_string(),
            }],
            ..Default::default()
        });

    let (buf, _) = encode_source_file(&mut nodes, file);
    let nodes_offset = read_uint32(&buf, HEADER_OFFSET_NODES);
    let root_data = read_uint32(&buf, nodes_offset as usize + NODE_SIZE + NODE_OFFSET_DATA);
    let extended_offset = read_uint32(&buf, HEADER_OFFSET_EXTENDED_DATA)
        + (root_data & NODE_DATA_STRING_INDEX_MASK);
    if extended_offset as usize + 76 > buf.len() {
        panic!(
            "invalid extended offset {extended_offset} (nodes={nodes_offset} rootData={root_data:#x} extendedData={} len={})",
            read_uint32(&buf, HEADER_OFFSET_EXTENDED_DATA),
            buf.len()
        );
    }
    let content_mapper_index = read_uint32(&buf, extended_offset as usize + 64);
    let virtual_file_name_index = read_uint32(&buf, extended_offset as usize + 68);
    let diagnostic_directives_offset = read_uint32(&buf, extended_offset as usize + 72);
    assert_eq!(encoded_string(&buf, content_mapper_index), "mapper@1.0.0");
    assert_eq!(
        encoded_string(&buf, virtual_file_name_index),
        "/component.vue.ts"
    );
    let structured_data_offset = read_uint32(&buf, HEADER_OFFSET_STRUCTURED_DATA);
    let directive_offset = (structured_data_offset + diagnostic_directives_offset) as usize;
    assert_eq!(
        &buf[directive_offset..directive_offset + 10],
        &[
            0x91, // one directive
            0x96, // six-element tuple
            2, 1, // original range [2, 3) in UTF-16
            2, 7, // virtual range [2, 9) in UTF-16
            1,             // expect policy
            0xcd, 10, 18,  // unused diagnostic code 2578
        ]
    );
}

fn encoded_string(buf: &[u8], index: u32) -> String {
    let string_offsets = read_uint32(buf, HEADER_OFFSET_STRING_OFFSETS);
    let string_data = read_uint32(buf, HEADER_OFFSET_STRING_DATA);
    let start = read_uint32(buf, (string_offsets + index * 4) as usize) as usize;
    let end = read_uint32(buf, (string_offsets + index * 4 + 4) as usize) as usize;
    String::from_utf8_lossy(&buf[string_data as usize + start..string_data as usize + end])
        .into_owned()
}

#[test]
fn test_encode_source_file_with_unicode_escapes() {
    let _baseline_tracking = track_baselines();
    let (file, mut nodes) = parse_source_file(
        test_parse_options("/test.ts"),
        "let a = \"\u{1F603}\"; let b = \"\\ud83d\\ude03\"; let c = \"\\udc00\\ud83d\\ude03\"; let d = \"\\ud83d\\ud83d\\ude03\"",
        ScriptKind::Ts,
    );
    let (buf, _table) = encode_source_file(&mut nodes, file);

    let s = format_encoded_source_file(&buf);
    baseline::run(
        "encodeSourceFileWithUnicodeEscapes.txt",
        &s,
        &baseline::Options {
            subfolder: "api".to_string(),
            ..Default::default()
        },
    )
    .unwrap();
}

#[test]
fn test_build_node_index_table_matches_encode() {
    let (file, mut nodes) = parse_source_file(
        test_parse_options("/test.ts"),
        "import { bar } from \"bar\";\nexport function foo<T, U>(a: string, b: string): any {}\nfoo();",
        ScriptKind::Ts,
    );

    let (_, encode_table) = encode_source_file(&mut nodes, file);

    let build_table = build_node_index_table(&mut nodes, file);

    // Both tables should produce identical Nodes slices.
    assert_eq!(
        build_table.nodes.len(),
        encode_table.nodes.len(),
        "nodes slice length mismatch"
    );

    // Every index should map to the same node.
    for (i, (&enc, &bld)) in encode_table
        .nodes
        .iter()
        .zip(build_table.nodes.iter())
        .enumerate()
    {
        assert_eq!(bld, enc, "node mismatch at index {i}");
    }

    // GetIndex on both tables should agree for every non-nil node.
    for (i, node) in encode_table.nodes.iter().enumerate() {
        let Some(node) = node else { continue };
        let enc_idx = encode_table.get_index(*node);
        let build_idx = build_table.get_index(*node);
        assert_eq!(
            enc_idx,
            i as u32,
            "encode_table.get_index mismatch at index {i}, node kind={:?}",
            nodes[*node].kind
        );
        assert_eq!(
            build_idx, enc_idx,
            "build_table.get_index mismatch for node kind={:?}",
            nodes[*node].kind
        );
    }
}

/// `BenchmarkEncodeSourceFile` — kept as an ignored single-iteration test.
#[test]
#[ignore]
fn bench_encode_source_file() {
    let file_content = std::fs::read_to_string(format!(
        "{}/fixtures/compiler/checker.ts",
        tsc_repo::test_data_path()
    ))
    .unwrap();
    let (file, mut nodes) =
        parse_source_file(test_parse_options("/checker.ts"), &file_content, ScriptKind::Ts);
    let _ = encode_source_file(&mut nodes, file);
}

/// `BenchmarkBuildNodeIndexTable` — kept as an ignored single-iteration test.
#[test]
#[ignore]
fn bench_build_node_index_table() {
    let file_content = std::fs::read_to_string(format!(
        "{}/fixtures/compiler/checker.ts",
        tsc_repo::test_data_path()
    ))
    .unwrap();
    let (file, mut nodes) =
        parse_source_file(test_parse_options("/checker.ts"), &file_content, ScriptKind::Ts);
    let _ = build_node_index_table(&mut nodes, file);
}

/// `formatEncodedSourceFile` — the text dump compared against baselines.
fn format_encoded_source_file(encoded: &[u8]) -> String {
    let offset_nodes = read_uint32(encoded, HEADER_OFFSET_NODES) as usize;
    let offset_string_offsets = read_uint32(encoded, HEADER_OFFSET_STRING_OFFSETS);
    let offset_strings = read_uint32(encoded, HEADER_OFFSET_STRING_DATA);

    fn get_indent(encoded: &[u8], offset_nodes: usize, parent_index: u32) -> String {
        if parent_index == 0 {
            return String::new();
        }
        "  ".to_string()
            + &get_indent(
                encoded,
                offset_nodes,
                read_uint32(
                    encoded,
                    offset_nodes + parent_index as usize * NODE_SIZE + NODE_OFFSET_PARENT,
                ),
            )
    }

    let mut result = String::new();
    let mut j = 1usize;
    let mut i = offset_nodes + NODE_SIZE;
    while i < encoded.len() {
        let kind = read_uint32(encoded, i + NODE_OFFSET_KIND);
        let pos = read_uint32(encoded, i + NODE_OFFSET_POS);
        let end = read_uint32(encoded, i + NODE_OFFSET_END);
        let parent_index = read_uint32(encoded, i + NODE_OFFSET_PARENT);
        result.push_str(&get_indent(encoded, offset_nodes, parent_index));
        if kind == SYNTAX_KIND_NODE_LIST {
            result.push_str("NodeList");
        } else {
            // `ast.Kind(kind).String()` — matches Go's `%v` output.
            result.push_str(
                kind_from_u32(kind)
                    .map(|k| k.kind_string())
                    .unwrap_or("KindUnknown"),
            );
        }
        let data = read_uint32(encoded, i + NODE_OFFSET_DATA);
        let data_type = data & NODE_DATA_TYPE_MASK;
        let is_identifier = kind_from_u32(kind) == Some(Kind::Identifier);
        if is_identifier || data_type == NODE_DATA_TYPE_STRING {
            let string_index = data & NODE_DATA_STRING_INDEX_MASK;
            let str_start =
                read_uint32(encoded, (offset_string_offsets + string_index * 4) as usize) as usize;
            let str_end = read_uint32(
                encoded,
                (offset_string_offsets + string_index * 4 + 4) as usize,
            ) as usize;
            let s = String::from_utf8_lossy(
                &encoded[offset_strings as usize + str_start..offset_strings as usize + str_end],
            );
            result.push_str(&format!(" \"{s}\""));
        }
        result.push_str(&format!(
            " [{pos}, {end}), i={j}, next={}",
            encoded[i + NODE_OFFSET_NEXT]
        ));
        result.push('\n');
        j += 1;
        i += NODE_SIZE;
    }
    result
}
