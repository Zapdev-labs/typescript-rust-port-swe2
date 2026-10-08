// Ported from tsc/internal/sourcemap/source_mapper_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_tspath::{CaseSensitivity, RootedFilePath};

use crate::lineinfo::{EcmaLineInfo, create_ecma_line_info};
use crate::source_mapper::{
    DocumentPosition, Host, convert_document_to_source_mapper, get_document_position_mapper,
};

struct SourceMapperTestHost {
    files: FxHashMap<RootedFilePath, String>,
}

fn host_with_files(files: &[(&str, &str)]) -> SourceMapperTestHost {
    SourceMapperTestHost {
        files: files
            .iter()
            .map(|(path, text)| (RootedFilePath::from(*path), (*text).to_string()))
            .collect(),
    }
}

impl Host for SourceMapperTestHost {
    fn case_sensitivity(&self) -> CaseSensitivity {
        CaseSensitivity::CaseSensitive
    }

    fn get_ecma_line_info(&self, file_name: &RootedFilePath) -> Option<Rc<EcmaLineInfo>> {
        let text = self.files.get(file_name)?;
        Some(Rc::new(create_ecma_line_info(
            text.clone(),
            tsc_core::core::compute_ecma_line_starts(text),
        )))
    }

    fn read_file(&self, file_name: &RootedFilePath) -> Option<String> {
        self.files.get(file_name).cloned()
    }
}

#[test]
fn test_source_mapper_preserves_empty_source_entries() {
    let host = host_with_files(&[
        ("/project/out/out.d.ts", "generated"),
        ("/project/src/real.ts", "source"),
    ]);
    let mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sourceRoot":"../src","sources":["","real.ts"],"names":[],"mappings":"ACAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let mapper = mapper.expect("mapper should be created");
    assert_eq!(
        mapper.get_source_position(&DocumentPosition {
            file_name: RootedFilePath::from("/project/out/out.d.ts"),
            pos: 0,
        }),
        Some(DocumentPosition {
            file_name: RootedFilePath::from("/project/src/real.ts"),
            pos: 0,
        })
    );
    assert_eq!(
        mapper.get_generated_position(&DocumentPosition {
            file_name: RootedFilePath::from("/project/src/real.ts"),
            pos: 0,
        }),
        Some(DocumentPosition {
            file_name: RootedFilePath::from("/project/out/out.d.ts"),
            pos: 0,
        })
    );
}

#[test]
fn test_source_mapper_resolves_empty_source_to_source_root() {
    let host = host_with_files(&[
        ("/project/out/out.d.ts", "generated"),
        ("/project/src", "source"),
    ]);
    let mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sourceRoot":"../src","sources":[""],"names":[],"mappings":"AAAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let mapper = mapper.expect("mapper should be created");
    assert_eq!(
        mapper.get_source_position(&DocumentPosition {
            file_name: RootedFilePath::from("/project/out/out.d.ts"),
            pos: 0,
        }),
        Some(DocumentPosition {
            file_name: RootedFilePath::from("/project/src"),
            pos: 0,
        })
    );
}

#[test]
fn test_source_mapper_resolves_empty_source_to_map_url_without_source_root() {
    let host = host_with_files(&[
        ("/project/out/out.d.ts", "generated"),
        ("/project/out/out.d.ts.map", "source"),
    ]);
    let mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sources":[""],"names":[],"mappings":"AAAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let mapper = mapper.expect("mapper should be created");
    assert_eq!(
        mapper.get_source_position(&DocumentPosition {
            file_name: RootedFilePath::from("/project/out/out.d.ts"),
            pos: 0,
        }),
        Some(DocumentPosition {
            file_name: RootedFilePath::from("/project/out/out.d.ts.map"),
            pos: 0,
        })
    );
}

#[test]
fn test_source_mapper_treats_empty_source_root_as_absent() {
    let host = host_with_files(&[
        ("/project/out/out.d.ts", "generated"),
        ("/project/out/out.d.ts.map", "map-relative empty source"),
        ("/project/out/a.ts", "map-relative source"),
        ("/project/src/a.ts", "parent-relative source"),
        ("/", "unrelated root"),
        ("/a.ts", "unrelated root source"),
        ("/missing.ts", "unrelated root source"),
    ]);
    // {name, source, fileName}
    for (test_name, source, file_name) in [
        ("empty source", "", "/project/out/out.d.ts.map"),
        ("relative source", "a.ts", "/project/out/a.ts"),
        ("parent-relative source", "../src/a.ts", "/project/src/a.ts"),
        ("missing source", "missing.ts", ""),
    ] {
        // {name, field}
        for (root_name, field) in [("absent", ""), ("empty", r#""sourceRoot":"","#)] {
            let mapper = convert_document_to_source_mapper(
                &host,
                &format!(
                    r#"{{"version":3,"file":"out.d.ts",{field}"sources":["{source}"],"names":[],"mappings":"AAAA"}}"#
                ),
                RootedFilePath::from("/project/out/out.d.ts.map"),
            );
            let mapper = mapper
                .unwrap_or_else(|| panic!("mapper should be created ({test_name}/{root_name})"));
            let source_position = mapper.get_source_position(&DocumentPosition {
                file_name: RootedFilePath::from("/project/out/out.d.ts"),
                pos: 0,
            });
            if file_name.is_empty() {
                assert!(
                    source_position.is_none(),
                    "expected no source position ({test_name}/{root_name})"
                );
                continue;
            }
            assert_eq!(
                source_position,
                Some(DocumentPosition {
                    file_name: RootedFilePath::from(file_name),
                    pos: 0,
                }),
                "({test_name}/{root_name})"
            );
            assert_eq!(
                mapper.get_generated_position(&DocumentPosition {
                    file_name: RootedFilePath::from(file_name),
                    pos: 0,
                }),
                Some(DocumentPosition {
                    file_name: RootedFilePath::from("/project/out/out.d.ts"),
                    pos: 0,
                }),
                "({test_name}/{root_name})"
            );
        }
    }
}

#[test]
fn test_source_mapper_prefixes_absolute_source_with_nonempty_source_root() {
    let host = host_with_files(&[
        ("/project/out/out.d.ts", "generated"),
        ("/project/src/actual/a.ts", "prefixed source"),
        ("/actual/a.ts", "unprefixed source"),
    ]);
    let mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sourceRoot":"../src","sources":["/actual/a.ts"],"names":[],"mappings":"AAAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let mapper = mapper.expect("mapper should be created");
    assert_eq!(
        mapper.get_source_position(&DocumentPosition {
            file_name: RootedFilePath::from("/project/out/out.d.ts"),
            pos: 0,
        }),
        Some(DocumentPosition {
            file_name: RootedFilePath::from("/project/src/actual/a.ts"),
            pos: 0,
        })
    );
}

#[test]
fn test_source_mapper_retains_duplicate_source_indices() {
    let host = host_with_files(&[
        ("/project/out/out.d.ts", "generated"),
        ("/project/src", "source"),
    ]);
    let mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sourceRoot":"../src","sources":["",""],"names":[],"mappings":"AAAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let mapper = mapper.expect("mapper should be created");
    assert_eq!(
        mapper.get_generated_position(&DocumentPosition {
            file_name: RootedFilePath::from("/project/src"),
            pos: 0,
        }),
        Some(DocumentPosition {
            file_name: RootedFilePath::from("/project/out/out.d.ts"),
            pos: 0,
        })
    );
}

#[test]
fn test_source_mapper_preserves_null_source_entries() {
    let host = host_with_files(&[
        ("/project/out/out.d.ts", "generated"),
        ("/project/out/real.ts", "source"),
    ]);
    let mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sources":[null,"real.ts"],"names":[],"mappings":"ACAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let mapper = mapper.expect("mapper should be created");
    assert_eq!(
        mapper.get_source_position(&DocumentPosition {
            file_name: RootedFilePath::from("/project/out/out.d.ts"),
            pos: 0,
        }),
        Some(DocumentPosition {
            file_name: RootedFilePath::from("/project/out/real.ts"),
            pos: 0,
        })
    );

    let null_mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sources":[null],"names":[],"mappings":"AAAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let null_mapper = null_mapper.expect("null mapper should be created");
    assert!(
        null_mapper
            .get_source_position(&DocumentPosition {
                file_name: RootedFilePath::from("/project/out/out.d.ts"),
                pos: 0,
            })
            .is_none()
    );
}

#[test]
fn test_source_mapper_ignores_out_of_range_source_index() {
    let host = host_with_files(&[]);
    let mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sources":["real.ts"],"names":[],"mappings":"ACAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let mapper = mapper.expect("mapper should be created");
    assert!(
        mapper
            .get_source_position(&DocumentPosition {
                file_name: RootedFilePath::from("/project/out/out.d.ts"),
                pos: 0,
            })
            .is_none()
    );
}

#[test]
fn test_source_mapper_ignores_source_url_suffix() {
    let host = host_with_files(&[("/project/out/out.d.ts", "generated")]);
    let mapper = convert_document_to_source_mapper(
        &host,
        r#"{"version":3,"file":"out.d.ts","sources":["https://example.com/source.ts?version=1"],"names":[],"mappings":"AAAA"}"#,
        RootedFilePath::from("/project/out/out.d.ts.map"),
    );
    let mapper = mapper.expect("mapper should be created");
    assert!(
        mapper
            .get_source_position(&DocumentPosition {
                file_name: RootedFilePath::from("/project/out/out.d.ts"),
                pos: 0,
            })
            .is_none()
    );
}

#[test]
fn test_source_mapper_ignores_external_map_url_suffix() {
    const GENERATED_FILE: &str = "/project/out/out.d.ts";
    let host = host_with_files(&[(
        GENERATED_FILE,
        "declare const value: number;\n//# sourceMappingURL=https://example.com/out.d.ts.map?version=1",
    )]);
    assert!(get_document_position_mapper(&host, RootedFilePath::from(GENERATED_FILE)).is_none());
}
