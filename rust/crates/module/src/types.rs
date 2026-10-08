// Ported from tsc/internal/module/types.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::sync::Arc;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::options_generated::CompilerOptions;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

use crate::resolver::DiagAndArgs;

/// `type ResolutionHost interface`
///
/// PORT: `FS() vfs.FS` returns the shared `Arc<dyn Vfs>`; `GetCurrentDirectory`
/// borrows from `self` where Go copies the string header.
pub trait ResolutionHost: Send + Sync {
    fn fs(&self) -> &Arc<dyn Vfs>;
    fn get_current_directory(&self) -> RootedDirectoryPath;
}

/// `type Resolver interface`
///
/// PORT: Go's trailing `error` return is dropped — no implementation in this
/// package ever produces one; callers that need it can layer it back on.
/// `*ResolvedModule` results are `Option<ResolvedModule>` (Go nil → `None`).
pub trait Resolver: Send + Sync {
    fn base_directory(&self) -> RootedDirectoryPath;
    fn resolve_module_name(
        &self,
        module_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>);
    fn resolve_module_name_from_directory(
        &self,
        module_name: &str,
        containing_directory: &RootedDirectoryPath,
        resolution_mode: ResolutionMode,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>);
    fn resolve_type_reference_directive(
        &self,
        type_reference_directive_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (ResolvedTypeReferenceDirective, Vec<DiagAndArgs>);
    fn get_resolution_data(&self) -> &ResolutionData;
}

use crate::cache::ResolutionData;

/// `type ModeAwareCacheKey struct`
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ModeAwareCacheKey {
    pub name: String,
    pub mode: ResolutionMode,
}

/// `type ResolvedProjectReference interface`
///
/// PORT: `CompilerOptions() *core.CompilerOptions` returns `Option<&CompilerOptions>`
/// (Go nil → `None`); `ConfigName` borrows rather than copying the path.
pub trait ResolvedProjectReference: Send + Sync {
    fn config_name(&self) -> &RootedFilePath;
    fn compiler_options(&self) -> Option<&CompilerOptions>;
}

/// `type NodeResolutionFeatures int32`
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct NodeResolutionFeatures(pub i32);

impl NodeResolutionFeatures {
    pub const IMPORTS: NodeResolutionFeatures = NodeResolutionFeatures(1 << 0);
    pub const SELF_NAME: NodeResolutionFeatures = NodeResolutionFeatures(1 << 1);
    pub const EXPORTS: NodeResolutionFeatures = NodeResolutionFeatures(1 << 2);
    pub const EXPORTS_PATTERN_TRAILERS: NodeResolutionFeatures = NodeResolutionFeatures(1 << 3);
    // allowing `#/` root imports in package.json imports field
    // not supported until mass adoption - https://github.com/nodejs/node/pull/60864
    pub const IMPORTS_PATTERN_ROOT: NodeResolutionFeatures = NodeResolutionFeatures(1 << 4);

    pub const NONE: NodeResolutionFeatures = NodeResolutionFeatures(0);
    pub const ALL: NodeResolutionFeatures = NodeResolutionFeatures(
        Self::IMPORTS.0
            | Self::SELF_NAME.0
            | Self::EXPORTS.0
            | Self::EXPORTS_PATTERN_TRAILERS.0
            | Self::IMPORTS_PATTERN_ROOT.0,
    );
    pub const NODE16_DEFAULT: NodeResolutionFeatures = NodeResolutionFeatures(
        Self::IMPORTS.0 | Self::SELF_NAME.0 | Self::EXPORTS.0 | Self::EXPORTS_PATTERN_TRAILERS.0,
    );
    pub const NODE_NEXT_DEFAULT: NodeResolutionFeatures = Self::ALL;
    pub const BUNDLER_DEFAULT: NodeResolutionFeatures = NodeResolutionFeatures(
        Self::IMPORTS.0
            | Self::SELF_NAME.0
            | Self::EXPORTS.0
            | Self::EXPORTS_PATTERN_TRAILERS.0
            | Self::IMPORTS_PATTERN_ROOT.0,
    );

    /// `r.features&NodeResolutionFeaturesExports != 0` style membership test.
    pub fn contains(self, other: NodeResolutionFeatures) -> bool {
        self.0 & other.0 != 0
    }
}

impl std::ops::BitOr for NodeResolutionFeatures {
    type Output = NodeResolutionFeatures;
    fn bitor(self, other: NodeResolutionFeatures) -> NodeResolutionFeatures {
        NodeResolutionFeatures(self.0 | other.0)
    }
}

impl std::ops::BitOrAssign for NodeResolutionFeatures {
    fn bitor_assign(&mut self, other: NodeResolutionFeatures) {
        self.0 |= other.0;
    }
}

impl std::ops::BitAnd for NodeResolutionFeatures {
    type Output = NodeResolutionFeatures;
    fn bitand(self, other: NodeResolutionFeatures) -> NodeResolutionFeatures {
        NodeResolutionFeatures(self.0 & other.0)
    }
}

/// `type PackageId struct`
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct PackageId {
    pub name: String,
    pub sub_module_name: String,
    pub version: String,
    pub peer_dependencies: String,
}

impl PackageId {
    /// `func (p *PackageId) PackageName() string`
    pub fn package_name(&self) -> String {
        if !self.sub_module_name.is_empty() {
            return format!("{}/{}", self.name, self.sub_module_name);
        }
        self.name.clone()
    }
}

/// `func (p *PackageId) String() string`
impl fmt::Display for PackageId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}@{}{}",
            self.package_name(),
            self.version,
            self.peer_dependencies
        )
    }
}

/// `type ResolvedModule struct`
///
/// PORT: `ResolvedFileName != ""` nil-receiver checks become `Option`
/// combinators at call sites; on the value itself [ResolvedModule::is_resolved]
/// reproduces `r.ResolvedFileName != ""`.
#[derive(Clone, Default)]
pub struct ResolvedModule {
    pub resolution_diagnostics: Vec<DiagnosticRef>,
    pub resolved_file_name: RootedFilePath,
    pub resolved_path: PathKey,
    pub original_path: RootedFilePath,
    pub extension: String,
    pub resolved_using_ts_extension: bool,
    pub resolved_using_extra_extensions: bool,
    pub is_external_library_import: bool,
    pub is_custom_resolution: bool,
    pub package_id: PackageId,
    pub alternate_result: RootedFilePath,
}

impl ResolvedModule {
    /// `func (r *ResolvedModule) IsResolved() bool`
    ///
    /// PORT: Go's nil-receiver case (`r == nil`) is the caller's `None`.
    pub fn is_resolved(&self) -> bool {
        !self.resolved_file_name.as_string().is_empty()
    }
}

/// `type ResolvedTypeReferenceDirective struct`
#[derive(Clone, Default)]
pub struct ResolvedTypeReferenceDirective {
    pub resolution_diagnostics: Vec<DiagnosticRef>,
    pub primary: bool,
    pub resolved_file_name: RootedFilePath,
    pub resolved_path: PathKey,
    pub original_path: RootedFilePath,
    pub package_id: PackageId,
    pub is_external_library_import: bool,
}

impl ResolvedTypeReferenceDirective {
    /// `func (r *ResolvedTypeReferenceDirective) IsResolved() bool`
    pub fn is_resolved(&self) -> bool {
        !self.resolved_file_name.as_string().is_empty()
    }
}

/// `type extensions int32`
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub(crate) struct Extensions(pub i32);

pub(crate) const EXTENSIONS_TYPE_SCRIPT: Extensions = Extensions(1 << 0);
pub(crate) const EXTENSIONS_JAVA_SCRIPT: Extensions = Extensions(1 << 1);
pub(crate) const EXTENSIONS_DECLARATION: Extensions = Extensions(1 << 2);
pub(crate) const EXTENSIONS_JSON: Extensions = Extensions(1 << 3);

pub(crate) const EXTENSIONS_IMPLEMENTATION_FILES: Extensions =
    Extensions(EXTENSIONS_TYPE_SCRIPT.0 | EXTENSIONS_JAVA_SCRIPT.0);

impl std::ops::BitOr for Extensions {
    type Output = Extensions;
    fn bitor(self, other: Extensions) -> Extensions {
        Extensions(self.0 | other.0)
    }
}

impl std::ops::BitOrAssign for Extensions {
    fn bitor_assign(&mut self, other: Extensions) {
        self.0 |= other.0;
    }
}

impl std::ops::BitAnd for Extensions {
    type Output = Extensions;
    fn bitand(self, other: Extensions) -> Extensions {
        Extensions(self.0 & other.0)
    }
}

impl Extensions {
    /// `extensions&e != 0` membership test.
    pub(crate) fn contains(self, other: Extensions) -> bool {
        self.0 & other.0 != 0
    }
}

/// `func (e extensions) String() string`
impl fmt::Display for Extensions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result: Vec<&str> = Vec::with_capacity(self.0.count_ones() as usize);
        if self.contains(EXTENSIONS_TYPE_SCRIPT) {
            result.push("TypeScript");
        }
        if self.contains(EXTENSIONS_JAVA_SCRIPT) {
            result.push("JavaScript");
        }
        if self.contains(EXTENSIONS_DECLARATION) {
            result.push("Declaration");
        }
        if self.contains(EXTENSIONS_JSON) {
            result.push("JSON");
        }
        f.write_str(&result.join(", "))
    }
}

impl Extensions {
    /// `func (e extensions) Array() []string`
    pub(crate) fn array(&self) -> Vec<&'static str> {
        let mut result = Vec::new();
        if self.contains(EXTENSIONS_TYPE_SCRIPT) {
            result.extend_from_slice(tsc_tspath::SUPPORTED_TS_IMPLEMENTATION_EXTENSIONS);
        }
        if self.contains(EXTENSIONS_JAVA_SCRIPT) {
            result.extend_from_slice(tsc_tspath::SUPPORTED_JS_EXTENSIONS_FLAT);
        }
        if self.contains(EXTENSIONS_DECLARATION) {
            result.extend_from_slice(tsc_tspath::SUPPORTED_DECLARATION_EXTENSIONS);
        }
        if self.contains(EXTENSIONS_JSON) {
            result.push(tsc_tspath::EXTENSION_JSON);
        }
        result
    }
}
