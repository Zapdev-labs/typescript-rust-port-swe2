// Ported from tsc/internal/contentmapper/transform_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `files.Supplemental[i]` is a `ParsedSourceFile` — `NodeId` equality
// replaces Go's `*ast.SourceFile` pointer identity; `FileName().AsString()`
// → `file_name().as_string()`.

use std::sync::Arc;

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_spanmap::SpanMap;
use tsc_tspath as tspath;

use crate::contentmapper::Mapper;
use crate::host::{MappedResult, Result};
use crate::transform::parse_result;

fn component_parse_options() -> SourceFileParseOptions {
    SourceFileParseOptions {
        file_name: "/component.astro".into(),
        path_key: "/component.astro".into(),
        ..Default::default()
    }
}

#[test]
fn test_parse_result_supplemental_file_extensions() {
    let mappings = Some(Arc::new(SpanMap::new(&[])));
    let result = Result {
        virtual_extension: ".ts".into(),
        mappings: mappings.clone(),
        supplemental: [".js", ".jsx", ".ts", ".tsx", ".mts", ".cts", ".json"]
            .into_iter()
            .map(|extension| MappedResult {
                virtual_extension: extension.into(),
                mappings: mappings.clone(),
                ..Default::default()
            })
            .collect(),
        ..Default::default()
    };
    let files = parse_result(
        &component_parse_options(),
        "",
        &Arc::new(Mapper {
            extensions: Some(vec![".astro".into()]),
            name: "mapper".into(),
            ..Default::default()
        }),
        "transform-identity",
        result,
    )
    .unwrap();
    assert_eq!(
        files.canonical.content_mapper_transform_identity(),
        "transform-identity"
    );
    let canonical_supplementals = files.canonical.supplemental_source_files();
    assert_eq!(canonical_supplementals.len(), files.supplemental.len());

    let expected: [(&str, ScriptKind); 7] = [
        ("/component.astro.0.js", ScriptKind::Js),
        ("/component.astro.1.jsx", ScriptKind::Jsx),
        ("/component.astro.2.ts", ScriptKind::Ts),
        ("/component.astro.3.tsx", ScriptKind::Tsx),
        ("/component.astro.4.mts", ScriptKind::Ts),
        ("/component.astro.5.cts", ScriptKind::Ts),
        ("/component.astro.6.json", ScriptKind::Json),
    ];
    assert_eq!(files.supplemental.len(), expected.len());
    for (i, (file_name, script_kind)) in expected.iter().enumerate() {
        let supplemental = &files.supplemental[i];
        assert_eq!(supplemental.file_name().as_string(), *file_name);
        assert_eq!(
            *supplemental.path_key(),
            tspath::path_key_from_canonical(file_name)
        );
        assert_eq!(supplemental.script_kind(), *script_kind);
        assert_eq!(
            supplemental.content_mapper_transform_identity(),
            "transform-identity"
        );
        // Go: `canonicalSupplementals[i] == files.Supplemental[i]`
        assert_eq!(canonical_supplementals[i], supplemental.file);
        // Go: `files.Supplemental[i].CanonicalSourceFile() == files.Canonical`
        assert_eq!(
            supplemental.canonical_source_file(),
            Some(files.canonical.file)
        );
    }
}

#[test]
fn test_parse_result_allows_supplemental_modules() {
    let mappings = Some(Arc::new(SpanMap::new(&[])));
    let files = parse_result(
        &component_parse_options(),
        "",
        &Arc::new(Mapper {
            extensions: Some(vec![".astro".into()]),
            name: "mapper".into(),
            ..Default::default()
        }),
        "",
        Result {
            text: "export {};".into(),
            virtual_extension: ".ts".into(),
            mappings: mappings.clone(),
            supplemental: vec![MappedResult {
                text: "export const value = 1;".into(),
                virtual_extension: ".mts".into(),
                mappings,
                ..Default::default()
            }],
            ..Default::default()
        },
    )
    .unwrap();
    assert!(tsc_ast::utilities::is_external_module(
        files.supplemental[0].source_file()
    ));
}

#[test]
fn test_parse_result_does_not_leak_canonical_module_forcing_to_supplementals() {
    let mappings = Some(Arc::new(SpanMap::new(&[])));
    let files = parse_result(
        &component_parse_options(),
        "",
        &Arc::new(Mapper {
            name: "mapper".into(),
            ..Default::default()
        }),
        "",
        Result {
            text: "const canonical = 1;".into(),
            virtual_extension: ".mts".into(),
            mappings: mappings.clone(),
            supplemental: vec![MappedResult {
                text: "const supplemental = 1;".into(),
                virtual_extension: ".ts".into(),
                mappings,
                ..Default::default()
            }],
            ..Default::default()
        },
    )
    .unwrap();
    assert!(
        files
            .canonical
            .parse_options()
            .external_module_indicator_options
            .force
    );
    assert!(
        !files.supplemental[0]
            .parse_options()
            .external_module_indicator_options
            .force
    );
}
