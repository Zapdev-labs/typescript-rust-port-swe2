// Ported from tsc/internal/module @ ec47d33c23e464a17cdf2475632cba629bee8763

pub mod cache;
pub mod resolver;
pub mod staticresolver;
pub mod types;
pub mod util;

#[cfg(test)]
mod staticresolver_test;

pub use cache::{ModeAwareCache, ResolutionData, ResolverOptions};
pub use resolver::{
    get_automatic_type_directive_names, get_compiler_options_with_redirect,
    get_conditions, match_pattern_or_exact, resolve_config, try_parse_patterns,
    DefaultResolver, DiagAndArgs, Ending, ParsedPatterns, ResolvedEntrypoint,
};
pub use staticresolver::{
    new_static_resolver, new_static_resolutions, StaticResolutionEntry, StaticResolver,
    StaticResolutions,
};
pub use types::{
    ModeAwareCacheKey, NodeResolutionFeatures, PackageId, ResolutionHost, ResolvedModule,
    ResolvedProjectReference, ResolvedTypeReferenceDirective, Resolver,
};
pub use util::{
    get_package_name_from_types_package_name, get_resolution_diagnostic,
    get_types_package_name, is_applicable_versioned_types_key,
    mangle_scoped_package_name, node_module_package_root_for_directory,
    node_module_package_root_for_file, parse_package_name, try_get_js_extension_for_file,
    try_get_js_extension_for_file_name, unmangle_scoped_package_name, compare_pattern_keys,
    INFERRED_TYPES_CONTAINING_FILE,
};
