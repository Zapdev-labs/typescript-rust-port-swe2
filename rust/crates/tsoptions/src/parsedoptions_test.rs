// Ported from tsc/internal/tsoptions/parsedoptions_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use crate::parsedoptions::ParsedOptions;
use tsc_collections::OrderedMap;
use tsc_contentmapper::Mapper;
use tsc_core::options_generated::{CompilerOptions, TypeAcquisition};
use tsc_core::projectreference::ProjectReference;
use tsc_core::tristate::{TS_FALSE, TS_TRUE};
use tsc_tspath::{RootedDirectoryPath, RootedFilePath, RootedPath};

fn raw_value(s: &str) -> tsc_json::Value {
    serde_json::value::RawValue::from_string(s.to_string()).unwrap()
}

fn make_options() -> ParsedOptions {
    ParsedOptions {
        compiler_options: Some(CompilerOptions {
            strict: TS_TRUE,
            ..Default::default()
        }),
        type_acquisition: Some(TypeAcquisition {
            enable: TS_TRUE,
            include: Some(vec!["a".into()]),
            exclude: Some(vec!["b".into()]),
            ..Default::default()
        }),
        file_names: vec![RootedFilePath::from("/a.ts"), RootedFilePath::from("/b.ts")],
        // PORT: Go's `[]*core.ProjectReference` can hold nil elements; the
        // second element here is a distinct non-nil reference so the
        // order-swap case still exercises equality.
        project_references: vec![
            ProjectReference {
                path: RootedPath::from("/project"),
                original_path: "../project".into(),
                circular: true,
            },
            ProjectReference {
                path: RootedPath::from("/other"),
                original_path: "../other".into(),
                circular: false,
            },
        ],
        content_mappers: vec![
            Arc::new(Mapper {
                package: "mapper".into(),
                extensions: Some(vec![".vue".into()]),
                options: Some(raw_value(r#"{"setting":true}"#)),
                name: "mapper".into(),
                version: "1".into(),
                exec: Some(vec!["node".into(), "mapper.js".into()]),
                compiler_options: Some(vec!["target".into()]),
                dynamic_config: true,
                package_directory: RootedDirectoryPath::from("/node_modules/mapper"),
                contribution_id: "extension".into(),
            }),
            Arc::new(Mapper {
                package: "other".into(),
                ..Default::default()
            }),
        ],
    }
}

/// The Rust stand-in for `reflect.DeepEqual`: field-wise structural
/// comparison preserving the nil-vs-empty (`None` vs `Some(empty)`)
/// distinctions that `Option` fields carry. Go's DeepEqual distinguishes
/// nil from empty slices, so `Option<Vec>` captures it exactly.
fn mapper_deep_equal(a: &Mapper, b: &Mapper) -> bool {
    a.package == b.package
        && a.extensions == b.extensions
        && match (&a.options, &b.options) {
            (None, None) => true,
            (Some(x), Some(y)) => x.get() == y.get(),
            _ => false,
        }
        && a.name == b.name
        && a.version == b.version
        && a.exec == b.exec
        && a.compiler_options == b.compiler_options
        && a.dynamic_config == b.dynamic_config
        && a.package_directory == b.package_directory
        && a.contribution_id == b.contribution_id
}

/// `reflect.DeepEqual` on `core.CompilerOptions`: serde serializes
/// `None` fields as omitted and `Some(empty)` fields as present-but-empty,
/// which preserves Go's nil-vs-allocated map/slice distinction, so JSON
/// value equality is a faithful proxy.
fn compiler_options_deep_equal(a: &CompilerOptions, b: &CompilerOptions) -> bool {
    serde_json::to_value(a).unwrap() == serde_json::to_value(b).unwrap()
}

fn type_acquisition_deep_equal(a: &TypeAcquisition, b: &TypeAcquisition) -> bool {
    a.enable == b.enable
        && a.include == b.include
        && a.exclude == b.exclude
        && a.disable_filename_based_type_acquisition == b.disable_filename_based_type_acquisition
}

fn parsed_options_deep_equal(a: &ParsedOptions, b: &ParsedOptions) -> bool {
    let compiler_options_equal = match (&a.compiler_options, &b.compiler_options) {
        (None, None) => true,
        (Some(x), Some(y)) => compiler_options_deep_equal(x, y),
        _ => false,
    };
    let type_acquisition_equal = match (&a.type_acquisition, &b.type_acquisition) {
        (None, None) => true,
        (Some(x), Some(y)) => type_acquisition_deep_equal(x, y),
        _ => false,
    };
    compiler_options_equal
        && type_acquisition_equal
        && a.file_names == b.file_names
        && a.project_references == b.project_references
        && a.content_mappers.len() == b.content_mappers.len()
        && a.content_mappers
            .iter()
            .zip(b.content_mappers.iter())
            .all(|(x, y)| mapper_deep_equal(x, y))
}

/// `check` — Go compares `a.Equals(b)` with `reflect.DeepEqual(a, b)`.
fn check(a: &ParsedOptions, b: &ParsedOptions) {
    let want = parsed_options_deep_equal(a, b);
    assert_eq!(a.equals(b), want, "equals mismatch for\n{:?}\n{:?}", a, b);
}

/// Go `(p *ParsedOptions) Equals` on a nil receiver / nil argument.
fn check_ref(a: Option<&ParsedOptions>, b: Option<&ParsedOptions>) -> bool {
    match (a, b) {
        (None, None) => true,
        (None, Some(_)) | (Some(_), None) => false,
        (Some(x), Some(y)) => x.equals(y),
    }
}

/// `TestParsedOptionsEquality`.
#[test]
fn test_parsed_options_equality() {
    // nil pairs: Go checks (nil,nil), (nil,&{}), (&{},nil), (&{},&{}).
    assert!(check_ref(None, None));
    assert!(!check_ref(None, Some(&ParsedOptions::default())));
    assert!(!check_ref(Some(&ParsedOptions::default()), None));
    check(&ParsedOptions::default(), &ParsedOptions::default());
    check(&make_options(), &make_options());

    struct Change {
        name: &'static str,
        f: fn(&mut ParsedOptions),
    }
    let changes = [
        Change {
            name: "compiler options",
            f: |p| {
                if let Some(o) = p.compiler_options.as_mut() {
                    o.strict = TS_FALSE;
                }
            },
        },
        Change {
            name: "nil compiler options",
            f: |p| p.compiler_options = None,
        },
        Change {
            name: "nil type acquisition",
            f: |p| p.type_acquisition = None,
        },
        Change {
            name: "type acquisition enable",
            f: |p| {
                if let Some(t) = p.type_acquisition.as_mut() {
                    t.enable = TS_FALSE;
                }
            },
        },
        Change {
            name: "type acquisition include",
            f: |p| {
                if let Some(t) = p.type_acquisition.as_mut() {
                    t.include.as_mut().unwrap()[0] = "other".into();
                }
            },
        },
        Change {
            name: "type acquisition exclude",
            f: |p| {
                if let Some(t) = p.type_acquisition.as_mut() {
                    t.exclude.as_mut().unwrap()[0] = "other".into();
                }
            },
        },
        Change {
            name: "type acquisition filename",
            f: |p| {
                if let Some(t) = p.type_acquisition.as_mut() {
                    t.disable_filename_based_type_acquisition = TS_TRUE;
                }
            },
        },
        Change {
            name: "filenames order",
            f: |p| {
                p.file_names = vec![RootedFilePath::from("/b.ts"), RootedFilePath::from("/a.ts")];
            },
        },
        Change {
            name: "reference path",
            f: |p| p.project_references[0].path = RootedPath::from("/other"),
        },
        Change {
            name: "reference original path",
            f: |p| p.project_references[0].original_path = "./other".into(),
        },
        Change {
            name: "reference circular",
            f: |p| p.project_references[0].circular = false,
        },
        Change {
            name: "reference order",
            f: |p| p.project_references.swap(0, 1),
        },
        Change {
            name: "mapper package",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0]).unwrap().package = "other".into();
            },
        },
        Change {
            name: "mapper extension",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0])
                    .unwrap()
                    .extensions
                    .as_mut()
                    .unwrap()[0] = ".other".into();
            },
        },
        Change {
            name: "mapper options",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0]).unwrap().options = Some(raw_value("{}"));
            },
        },
        Change {
            name: "mapper name",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0]).unwrap().name = "other".into();
            },
        },
        Change {
            name: "mapper version",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0]).unwrap().version = "2".into();
            },
        },
        Change {
            name: "mapper exec",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0])
                    .unwrap()
                    .exec
                    .as_mut()
                    .unwrap()[1] = "other.js".into();
            },
        },
        Change {
            name: "mapper compiler options",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0])
                    .unwrap()
                    .compiler_options
                    .as_mut()
                    .unwrap()[0] = "jsx".into();
            },
        },
        Change {
            name: "mapper dynamic config",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0])
                    .unwrap()
                    .dynamic_config = false;
            },
        },
        Change {
            name: "mapper directory",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0])
                    .unwrap()
                    .package_directory = RootedDirectoryPath::from("/other");
            },
        },
        Change {
            name: "mapper contribution",
            f: |p| {
                Arc::get_mut(&mut p.content_mappers[0])
                    .unwrap()
                    .contribution_id = "other".into();
            },
        },
        Change {
            name: "mapper order",
            f: |p| p.content_mappers.swap(0, 1),
        },
    ];
    // PORT: Go's "nil reference" / "nil mapper" changes set a slice element
    // to nil; Rust's `Vec<ProjectReference>` / `Vec<Arc<Mapper>>` elements
    // cannot be nil, so those cases are unrepresentable.
    for change in changes {
        let a = make_options();
        let mut b = make_options();
        (change.f)(&mut b);
        check(&a, &b);
        check(&b, &a);
        assert!(b.equals(&b), "{}: self-equality", change.name);
    }

    // Zeroing each ParsedOptions field (the Go reflect-driven "field
    // coverage" loop, enumerated by hand).
    for (name, f) in [
        (
            "compiler_options",
            (|p: &mut ParsedOptions| p.compiler_options = None) as fn(&mut ParsedOptions),
        ),
        ("type_acquisition", |p| p.type_acquisition = None),
        ("file_names", |p| p.file_names = Vec::new()),
        ("project_references", |p| p.project_references = Vec::new()),
        ("content_mappers", |p| p.content_mappers = Vec::new()),
    ] {
        let a = make_options();
        let mut b = make_options();
        f(&mut b);
        assert!(!a.equals(&b), "zeroing {name} must break equality");
        assert!(!b.equals(&a), "zeroing {name} must break equality");
    }

    // Zeroing each Mapper field (Go enumerates Definition and Manifest
    // fields; Mapper is flattened in Rust).
    for (name, f) in [
        (
            "package",
            (|m: &mut Mapper| m.package = String::new()) as fn(&mut Mapper),
        ),
        ("extensions", |m| m.extensions = None),
        ("options", |m| m.options = None),
        ("name", |m| m.name = String::new()),
        ("version", |m| m.version = String::new()),
        ("exec", |m| m.exec = None),
        ("compiler_options", |m| m.compiler_options = None),
        ("dynamic_config", |m| m.dynamic_config = false),
        ("package_directory", |m| {
            m.package_directory = RootedDirectoryPath::default()
        }),
        ("contribution_id", |m| m.contribution_id = String::new()),
    ] {
        let a = make_options();
        let mut b = make_options();
        f(Arc::get_mut(&mut b.content_mappers[0]).unwrap());
        assert!(!a.equals(&b), "zeroing Mapper.{name} must break equality");
        assert!(!b.equals(&a), "zeroing Mapper.{name} must break equality");
    }

    // Go's nil-vs-empty slice sweep over ParsedOptions / Definition /
    // Manifest: only the `Option<Vec>` Mapper fields preserve that
    // distinction in Rust (see PORT note above).
    for name in ["extensions", "exec", "compiler_options"] {
        // Populated vs allocated-but-empty.
        let a = make_options();
        let mut empty = make_options();
        {
            let m = Arc::get_mut(&mut empty.content_mappers[0]).unwrap();
            match name {
                "extensions" => m.extensions = Some(Vec::new()),
                "exec" => m.exec = Some(Vec::new()),
                "compiler_options" => m.compiler_options = Some(Vec::new()),
                _ => unreachable!(),
            }
        }
        assert!(!a.equals(&empty), "empty {name} must break equality");

        // nil (None) vs allocated-but-empty (Some([])).
        let mut nil = make_options();
        {
            let m = Arc::get_mut(&mut nil.content_mappers[0]).unwrap();
            match name {
                "extensions" => m.extensions = None,
                "exec" => m.exec = None,
                "compiler_options" => m.compiler_options = None,
                _ => unreachable!(),
            }
        }
        assert!(!nil.equals(&empty), "nil vs empty {name} must not be equal");
        assert!(!empty.equals(&nil), "empty vs nil {name} must not be equal");
    }
}

/// `TestParsedOptionsEqualityIgnoresEmptyTypeAcquisitionLists`.
#[test]
fn test_parsed_options_equality_ignores_empty_type_acquisition_lists() {
    let options = [
        TypeAcquisition::default(),
        TypeAcquisition {
            include: Some(Vec::new()),
            ..Default::default()
        },
        TypeAcquisition {
            exclude: Some(Vec::new()),
            ..Default::default()
        },
        TypeAcquisition {
            include: Some(Vec::new()),
            exclude: Some(Vec::new()),
            ..Default::default()
        },
    ];
    for a in &options {
        for b in &options {
            let left = ParsedOptions {
                type_acquisition: Some(a.clone()),
                ..Default::default()
            };
            let right = ParsedOptions {
                type_acquisition: Some(b.clone()),
                ..Default::default()
            };
            assert!(
                left.equals(&right),
                "nil and empty type acquisition lists must compare equal: {:?}, {:?}",
                a,
                b
            );
        }
    }
    // Also exercise `None` (nil slice) against `Some(vec![])`.
    let left = ParsedOptions {
        type_acquisition: Some(TypeAcquisition::default()),
        ..Default::default()
    };
    let right = ParsedOptions {
        type_acquisition: Some(TypeAcquisition {
            include: Some(Vec::new()),
            ..Default::default()
        }),
        ..Default::default()
    };
    assert!(left.equals(&right));
}

/// `TestParsedOptionsEqualityIgnoresPathsAllocation`.
#[test]
fn test_parsed_options_equality_ignores_paths_allocation() {
    let a = ParsedOptions {
        compiler_options: Some(CompilerOptions {
            paths: Some(OrderedMap::new()),
            ..Default::default()
        }),
        ..Default::default()
    };
    let b = ParsedOptions {
        compiler_options: Some(CompilerOptions {
            paths: Some(OrderedMap::new()),
            ..Default::default()
        }),
        ..Default::default()
    };
    assert!(
        a.equals(&b) && b.equals(&a),
        "empty paths maps must compare equal"
    );
}
