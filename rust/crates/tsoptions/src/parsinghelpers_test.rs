// Ported from tsc/internal/tsoptions/parsinghelpers_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::generated::options;
use crate::parsinghelpers::merge_compiler_options;
use crate::value::Value;
use tsc_collections::OrderedMap;
use tsc_core::options_generated::{CompilerOptions, ModuleDetectionKind};
use tsc_core::tristate::{TS_TRUE, TS_UNKNOWN};

fn raw_with_null_field(name: &str) -> Value {
    let mut null_options = OrderedMap::new();
    null_options.set(name.to_string(), Value::Null);
    let mut raw = OrderedMap::new();
    raw.set("compilerOptions".to_string(), Value::Map(null_options));
    Value::Map(raw)
}

/// `TestMergeCompilerOptions` — the Go test reflectively iterates every
/// `CompilerOptions` field; Rust has no field reflection, so this port
/// exercises representative fields of each generated merge shape: Tristate,
/// typed enums, `Option<Vec<_>>`, and rooted paths.
#[test]
fn test_merge_compiler_options() {
    // A nil source must leave the target unchanged.
    let mut unchanged = CompilerOptions {
        strict: TS_TRUE,
        ..Default::default()
    };
    merge_compiler_options(&mut unchanged, None, &Value::Null);
    assert_eq!(unchanged.strict, TS_TRUE);

    // Tristate field: explicit null zeroes, non-zero source overwrites, zero
    // source leaves target alone.
    for explicit_null in [false, true] {
        for source_value in [TS_UNKNOWN, TS_TRUE] {
            let mut target = CompilerOptions {
                strict: TS_TRUE,
                ..Default::default()
            };
            let source = CompilerOptions {
                strict: source_value,
                ..Default::default()
            };
            let raw = if explicit_null {
                raw_with_null_field("strict")
            } else {
                Value::Null
            };
            merge_compiler_options(&mut target, Some(&source), &raw);
            let expected = if explicit_null {
                TS_UNKNOWN
            } else if source_value != TS_UNKNOWN {
                source_value
            } else {
                TS_TRUE
            };
            assert_eq!(target.strict, expected, "explicitNull={explicit_null}");
            // Merge must not modify the source.
            assert_eq!(source.strict, source_value);
        }
    }

    // Typed enum field.
    let mut target = CompilerOptions {
        module_detection: ModuleDetectionKind::Force,
        ..Default::default()
    };
    let source = CompilerOptions {
        module_detection: ModuleDetectionKind::Auto,
        ..Default::default()
    };
    merge_compiler_options(&mut target, Some(&source), &Value::Null);
    assert_eq!(target.module_detection, ModuleDetectionKind::Auto);

    // Slice/Vec field: source value is cloned into the target.
    let mut target = CompilerOptions::default();
    let source = CompilerOptions {
        custom_conditions: Some(vec!["a".to_string()]),
        ..Default::default()
    };
    merge_compiler_options(&mut target, Some(&source), &Value::Null);
    assert_eq!(target.custom_conditions, Some(vec!["a".to_string()]));
    assert_eq!(source.custom_conditions, Some(vec!["a".to_string()]));
}

/// `TestMergeCompilerOptionsRawNulls`.
#[test]
fn test_merge_compiler_options_raw_nulls() {
    for name in [
        "moduleDetection",
        "ModuleDetection",
        "moduleDetectionKind",
        "unknownOption",
    ] {
        let raw = raw_with_null_field(name);
        let mut target = CompilerOptions {
            module_detection: ModuleDetectionKind::Force,
            ..Default::default()
        };
        let source = CompilerOptions {
            module_detection: ModuleDetectionKind::Auto,
            ..Default::default()
        };
        let mut expected = ModuleDetectionKind::Auto;
        if name == "moduleDetection" {
            expected = ModuleDetectionKind::None;
        }
        merge_compiler_options(&mut target, Some(&source), &raw);
        assert_eq!(
            target.module_detection, expected,
            "name={name}: target got {:?}, want {:?}",
            target.module_detection, expected
        );
        let mut source2 = source.clone();
        merge_compiler_options(&mut source2, Some(&source.clone()), &raw);
        assert_eq!(
            source2.module_detection, expected,
            "name={name}: merging an object with itself must still apply explicit nulls"
        );
    }
}

/// `TestParseCompilerOptionNoMissingFields` — the Go test reflectively lists
/// `CompilerOptions` json field names; the list is captured here from the Go
/// struct at the baseline commit. `parse_compiler_options` is the generated
/// function that returns `foundKey`.
#[test]
fn test_parse_compiler_option_no_missing_fields() {
    const FIELD_NAMES: &[&str] = &[
        "allowJs",
        "allowArbitraryExtensions",
        "allowImportingTsExtensions",
        "allowNonTsExtensions",
        "allowUmdGlobalAccess",
        "allowUnreachableCode",
        "allowUnusedLabels",
        "assumeChangesOnlyAffectDirectDependencies",
        "checkJs",
        "customConditions",
        "composite",
        "emitDeclarationOnly",
        "emitBOM",
        "emitDecoratorMetadata",
        "declaration",
        "declarationDir",
        "declarationMap",
        "deduplicatePackages",
        "disableSizeLimit",
        "disableSourceOfProjectReferenceRedirect",
        "disableSolutionSearching",
        "disableReferencedProjectLoad",
        "erasableSyntaxOnly",
        "exactOptionalPropertyTypes",
        "experimentalDecorators",
        "forceConsistentCasingInFileNames",
        "isolatedModules",
        "isolatedDeclarations",
        "ignoreConfig",
        "ignoreDeprecations",
        "importHelpers",
        "inlineSourceMap",
        "inlineSources",
        "init",
        "incremental",
        "jsx",
        "jsxFactory",
        "jsxFragmentFactory",
        "jsxImportSource",
        "lib",
        "libReplacement",
        "locale",
        "mapRoot",
        "module",
        "moduleResolution",
        "moduleSuffixes",
        "moduleDetection",
        "newLine",
        "noEmit",
        "noCheck",
        "noErrorTruncation",
        "noFallthroughCasesInSwitch",
        "noImplicitAny",
        "noImplicitThis",
        "noImplicitReturns",
        "noEmitHelpers",
        "noLib",
        "noPropertyAccessFromIndexSignature",
        "noUncheckedIndexedAccess",
        "noEmitOnError",
        "noUnusedLocals",
        "noUnusedParameters",
        "noResolve",
        "noImplicitOverride",
        "noUncheckedSideEffectImports",
        "outDir",
        "paths",
        "plugins",
        "preserveConstEnums",
        "preserveSymlinks",
        "project",
        "resolveJsonModule",
        "resolvePackageJsonExports",
        "resolvePackageJsonImports",
        "removeComments",
        "rewriteRelativeImportExtensions",
        "reactNamespace",
        "rootDir",
        "rootDirs",
        "skipLibCheck",
        "stableTypeOrdering",
        "strict",
        "strictBindCallApply",
        "strictBuiltinIteratorReturn",
        "strictFunctionTypes",
        "strictNullChecks",
        "strictPropertyInitialization",
        "stripInternal",
        "skipDefaultLibCheck",
        "sourceMap",
        "sourceRoot",
        "suppressOutputPathCheck",
        "target",
        "traceResolution",
        "tsBuildInfoFile",
        "typeRoots",
        "types",
        "useDefineForClassFields",
        "useUnknownInCatchVariables",
        "verbatimModuleSyntax",
        "maxNodeModuleJsDepth",
        "allowSyntheticDefaultImports",
        "alwaysStrict",
        "baseUrl",
        "downlevelIteration",
        "esModuleInterop",
        "outFile",
        "configFilePath",
        "noDtsResolution",
        "pathsBasePath",
        "diagnostics",
        "extendedDiagnostics",
        "generateCpuProfile",
        "generateTrace",
        "listEmittedFiles",
        "listFiles",
        "explainFiles",
        "listFilesOnly",
        "noEmitForJsFiles",
        "preserveWatchOutput",
        "pretty",
        "version",
        "watch",
        "showConfig",
        "build",
        "help",
        "all",
        "runExternalCode",
        "pprofDir",
        "singleThreaded",
        "quiet",
        "checkers",
    ];
    let mut missing_keys = Vec::new();
    for key_name in FIELD_NAMES {
        let mut co = CompilerOptions::default();
        let found = options::parse_compiler_options(key_name, &Value::Int(0), &mut co);
        if !found {
            missing_keys.push(*key_name);
        }
    }
    assert!(
        missing_keys.is_empty(),
        "The following keys are missing entries in the parse_compiler_options \
         match statement:\n{missing_keys:?}"
    );
}
