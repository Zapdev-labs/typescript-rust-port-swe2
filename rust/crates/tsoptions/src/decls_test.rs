// Ported from tsc/internal/tsoptions/decls_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;

use crate::commandlineoption::CommandLineOptionPathKind;
use crate::generated::declarations;
use crate::namemap::compiler_name_map;

/// `TestCompilerOptionsDeclaration` — the Go test reflectively reads the json
/// tags of `core.CompilerOptions`; the (field name -> json tag) list captured
/// from the baseline Go struct is used instead.
#[test]
fn test_compiler_options_declaration() {
    // (Go field name, json tag name) pairs for core.CompilerOptions.
    const FIELDS: &[(&str, &str)] = &[
        ("AllowJs", "allowJs"),
        ("AllowArbitraryExtensions", "allowArbitraryExtensions"),
        ("AllowImportingTsExtensions", "allowImportingTsExtensions"),
        ("AllowNonTsExtensions", "allowNonTsExtensions"),
        ("AllowUmdGlobalAccess", "allowUmdGlobalAccess"),
        ("AllowUnreachableCode", "allowUnreachableCode"),
        ("AllowUnusedLabels", "allowUnusedLabels"),
        (
            "AssumeChangesOnlyAffectDirectDependencies",
            "assumeChangesOnlyAffectDirectDependencies",
        ),
        ("CheckJs", "checkJs"),
        ("CustomConditions", "customConditions"),
        ("Composite", "composite"),
        ("EmitDeclarationOnly", "emitDeclarationOnly"),
        ("EmitBOM", "emitBOM"),
        ("EmitDecoratorMetadata", "emitDecoratorMetadata"),
        ("Declaration", "declaration"),
        ("DeclarationDir", "declarationDir"),
        ("DeclarationMap", "declarationMap"),
        ("DeduplicatePackages", "deduplicatePackages"),
        ("DisableSizeLimit", "disableSizeLimit"),
        (
            "DisableSourceOfProjectReferenceRedirect",
            "disableSourceOfProjectReferenceRedirect",
        ),
        ("DisableSolutionSearching", "disableSolutionSearching"),
        (
            "DisableReferencedProjectLoad",
            "disableReferencedProjectLoad",
        ),
        ("ErasableSyntaxOnly", "erasableSyntaxOnly"),
        ("ExactOptionalPropertyTypes", "exactOptionalPropertyTypes"),
        ("ExperimentalDecorators", "experimentalDecorators"),
        (
            "ForceConsistentCasingInFileNames",
            "forceConsistentCasingInFileNames",
        ),
        ("IsolatedModules", "isolatedModules"),
        ("IsolatedDeclarations", "isolatedDeclarations"),
        ("IgnoreConfig", "ignoreConfig"),
        ("IgnoreDeprecations", "ignoreDeprecations"),
        ("ImportHelpers", "importHelpers"),
        ("InlineSourceMap", "inlineSourceMap"),
        ("InlineSources", "inlineSources"),
        ("Init", "init"),
        ("Incremental", "incremental"),
        ("Jsx", "jsx"),
        ("JsxFactory", "jsxFactory"),
        ("JsxFragmentFactory", "jsxFragmentFactory"),
        ("JsxImportSource", "jsxImportSource"),
        ("Lib", "lib"),
        ("LibReplacement", "libReplacement"),
        ("Locale", "locale"),
        ("MapRoot", "mapRoot"),
        ("Module", "module"),
        ("ModuleResolution", "moduleResolution"),
        ("ModuleSuffixes", "moduleSuffixes"),
        ("ModuleDetection", "moduleDetection"),
        ("NewLine", "newLine"),
        ("NoEmit", "noEmit"),
        ("NoCheck", "noCheck"),
        ("NoErrorTruncation", "noErrorTruncation"),
        ("NoFallthroughCasesInSwitch", "noFallthroughCasesInSwitch"),
        ("NoImplicitAny", "noImplicitAny"),
        ("NoImplicitThis", "noImplicitThis"),
        ("NoImplicitReturns", "noImplicitReturns"),
        ("NoEmitHelpers", "noEmitHelpers"),
        ("NoLib", "noLib"),
        (
            "NoPropertyAccessFromIndexSignature",
            "noPropertyAccessFromIndexSignature",
        ),
        ("NoUncheckedIndexedAccess", "noUncheckedIndexedAccess"),
        ("NoEmitOnError", "noEmitOnError"),
        ("NoUnusedLocals", "noUnusedLocals"),
        ("NoUnusedParameters", "noUnusedParameters"),
        ("NoResolve", "noResolve"),
        ("NoImplicitOverride", "noImplicitOverride"),
        (
            "NoUncheckedSideEffectImports",
            "noUncheckedSideEffectImports",
        ),
        ("OutDir", "outDir"),
        ("Paths", "paths"),
        ("Plugins", "plugins"),
        ("PreserveConstEnums", "preserveConstEnums"),
        ("PreserveSymlinks", "preserveSymlinks"),
        ("Project", "project"),
        ("ResolveJsonModule", "resolveJsonModule"),
        ("ResolvePackageJsonExports", "resolvePackageJsonExports"),
        ("ResolvePackageJsonImports", "resolvePackageJsonImports"),
        ("RemoveComments", "removeComments"),
        (
            "RewriteRelativeImportExtensions",
            "rewriteRelativeImportExtensions",
        ),
        ("ReactNamespace", "reactNamespace"),
        ("RootDir", "rootDir"),
        ("RootDirs", "rootDirs"),
        ("SkipLibCheck", "skipLibCheck"),
        ("StableTypeOrdering", "stableTypeOrdering"),
        ("Strict", "strict"),
        ("StrictBindCallApply", "strictBindCallApply"),
        ("StrictBuiltinIteratorReturn", "strictBuiltinIteratorReturn"),
        ("StrictFunctionTypes", "strictFunctionTypes"),
        ("StrictNullChecks", "strictNullChecks"),
        (
            "StrictPropertyInitialization",
            "strictPropertyInitialization",
        ),
        ("StripInternal", "stripInternal"),
        ("SkipDefaultLibCheck", "skipDefaultLibCheck"),
        ("SourceMap", "sourceMap"),
        ("SourceRoot", "sourceRoot"),
        ("SuppressOutputPathCheck", "suppressOutputPathCheck"),
        ("Target", "target"),
        ("TraceResolution", "traceResolution"),
        ("TsBuildInfoFile", "tsBuildInfoFile"),
        ("TypeRoots", "typeRoots"),
        ("Types", "types"),
        ("UseDefineForClassFields", "useDefineForClassFields"),
        ("UseUnknownInCatchVariables", "useUnknownInCatchVariables"),
        ("VerbatimModuleSyntax", "verbatimModuleSyntax"),
        ("MaxNodeModuleJsDepth", "maxNodeModuleJsDepth"),
        (
            "AllowSyntheticDefaultImports",
            "allowSyntheticDefaultImports",
        ),
        ("AlwaysStrict", "alwaysStrict"),
        ("BaseUrl", "baseUrl"),
        ("DownlevelIteration", "downlevelIteration"),
        ("ESModuleInterop", "esModuleInterop"),
        ("OutFile", "outFile"),
        ("ConfigFilePath", "configFilePath"),
        ("NoDtsResolution", "noDtsResolution"),
        ("PathsBasePath", "pathsBasePath"),
        ("Diagnostics", "diagnostics"),
        ("ExtendedDiagnostics", "extendedDiagnostics"),
        ("GenerateCpuProfile", "generateCpuProfile"),
        ("GenerateTrace", "generateTrace"),
        ("ListEmittedFiles", "listEmittedFiles"),
        ("ListFiles", "listFiles"),
        ("ExplainFiles", "explainFiles"),
        ("ListFilesOnly", "listFilesOnly"),
        ("NoEmitForJsFiles", "noEmitForJsFiles"),
        ("PreserveWatchOutput", "preserveWatchOutput"),
        ("Pretty", "pretty"),
        ("Version", "version"),
        ("Watch", "watch"),
        ("ShowConfig", "showConfig"),
        ("Build", "build"),
        ("Help", "help"),
        ("All", "all"),
        ("RunExternalCode", "runExternalCode"),
        ("PprofDir", "pprofDir"),
        ("SingleThreaded", "singleThreaded"),
        ("Quiet", "quiet"),
        ("Checkers", "checkers"),
    ];

    let mut decls: HashMap<String, &crate::commandlineoption::CommandLineOption> = HashMap::new();
    for decl in declarations::options_declarations() {
        decls.insert(decl.name.to_lowercase(), decl);
    }

    // internalOptions
    let internal_options_map: HashMap<String, &str> = [
        "allowNonTsExtensions",
        "build",
        "configFilePath",
        "noDtsResolution",
        "noEmitForJsFiles",
        "pathsBasePath",
        "suppressOutputPathCheck",
    ]
    .iter()
    .map(|opt| (opt.to_lowercase(), *opt))
    .collect();

    let mut failures = Vec::new();
    for (field_name, json_name) in FIELDS {
        let lower_name = field_name.to_lowercase();
        match decls.get(&lower_name).copied() {
            None => {
                if let Some(&want) = internal_options_map.get(&lower_name) {
                    // checkCompilerOptionJsonTagName: json tag must match.
                    if *json_name != want {
                        failures.push(format!(
                            "Field {field_name} has json tag {json_name}, want {want}"
                        ));
                    }
                    continue;
                }
                failures.push(format!(
                    "CompilerOptions.{field_name} has no options declaration"
                ));
            }
            Some(decl) => {
                decls.remove(&lower_name);
                if decl.name != *json_name {
                    failures.push(format!(
                        "Field {field_name} has json tag {json_name}, but the option \
                         declaration has name {}",
                        decl.name
                    ));
                }
            }
        }
    }

    // skippedOptions
    for opt in ["plugins"] {
        decls.remove(opt);
    }

    for decl in decls.values() {
        failures.push(format!(
            "Option declaration {} is not present in CompilerOptions",
            decl.name
        ));
    }

    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `TestCommandLineOptionPathKinds`.
#[test]
fn test_command_line_option_path_kinds() {
    let mut expected: HashMap<&str, CommandLineOptionPathKind> = [
        ("baseUrl", CommandLineOptionPathKind::Directory),
        ("declarationDir", CommandLineOptionPathKind::Directory),
        ("generateCpuProfile", CommandLineOptionPathKind::File),
        ("generateTrace", CommandLineOptionPathKind::Directory),
        ("mapRoot", CommandLineOptionPathKind::SourceMapLocation),
        ("outDir", CommandLineOptionPathKind::Directory),
        ("outFile", CommandLineOptionPathKind::File),
        ("pprofDir", CommandLineOptionPathKind::Directory),
        ("project", CommandLineOptionPathKind::FileOrDirectory),
        ("rootDir", CommandLineOptionPathKind::Directory),
        ("sourceRoot", CommandLineOptionPathKind::SourceMapLocation),
        ("tsBuildInfoFile", CommandLineOptionPathKind::File),
    ]
    .into_iter()
    .collect();

    let mut failures = Vec::new();
    for option in declarations::options_declarations() {
        match expected.get(option.name).copied() {
            None => {
                if option.path_kind != CommandLineOptionPathKind::None {
                    failures.push(format!(
                        "{} has unexpected path kind {:?}",
                        option.name, option.path_kind
                    ));
                }
            }
            Some(path_kind) => {
                if option.path_kind != path_kind {
                    failures.push(format!(
                        "{} has path kind {:?}, want {:?}",
                        option.name, option.path_kind, path_kind
                    ));
                }
                expected.remove(option.name);
            }
        }
    }
    for option_name in expected.keys() {
        failures.push(format!(
            "{option_name} was not found in option declarations"
        ));
    }

    for option_name in ["rootDirs", "typeRoots"] {
        let option = compiler_name_map().get_option_declaration_from_name(option_name, false);
        let element_path_kind = option.and_then(|o| o.elements()).map(|e| e.path_kind);
        if element_path_kind != Some(CommandLineOptionPathKind::Directory) {
            failures.push(format!(
                "{option_name} element is not classified as a directory"
            ));
        }
    }

    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
