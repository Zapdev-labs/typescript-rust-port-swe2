// Ported from tsc/internal/testutil/autoimporttestutil/fixtures.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `testing.T` is dropped (see crate root): `t.Cleanup(session.Close)`
//   becomes a `Drop` impl on [Fixture]/[MonorepoFixture] that closes the
//   session, `t.Helper` disappears.
// - Go's `map[string]any` file map becomes `FxHashMap<String,
//   vfstest::TestFile>` (`TestFile::Text` / `TestFile::MapFile`).
// - `ProjectFileHandle` embeds `FileHandle` in Go; a `Deref` impl provides
//   the promoted `file_name`/`content`/`uri` accessors.
// - `RootedDirectoryPath` replaces Go's map key directly (it is `Hash`).

use std::ops::Deref;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use tsc_lsconv as lsconv;
use tsc_lsproto::DocumentUri;
use tsc_project::session::Session;
use tsc_tspath::{self as tspath, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::vfstest;

use crate::projecttestutil::{self, SessionUtils};

/// FileHandle represents a file created for an autoimport lifecycle test.
#[derive(Clone, Debug, Default)]
pub struct FileHandle {
    file_name: RootedFilePath,
    content: String,
}

impl FileHandle {
    /// `func (f FileHandle) FileName() tspath.RootedFilePath`
    pub fn file_name(&self) -> RootedFilePath {
        self.file_name.clone()
    }

    /// `func (f FileHandle) Content() string`
    pub fn content(&self) -> &str {
        &self.content
    }

    /// `func (f FileHandle) URI() lsproto.DocumentUri`
    pub fn uri(&self) -> DocumentUri {
        lsconv::file_name_to_document_uri(&self.file_name)
    }
}

/// ProjectFileHandle adds export metadata for TypeScript source files.
#[derive(Clone, Debug, Default)]
pub struct ProjectFileHandle {
    /// `FileHandle` — Go embeds it; `Deref` provides the promoted methods.
    pub file_handle: FileHandle,
    /// `exportIdentifier` — `pub` for parity with Go's in-package access.
    pub export_identifier: String,
}

/// Go's embedded `FileHandle` — promoted `file_name`/`content`/`uri` access.
impl Deref for ProjectFileHandle {
    type Target = FileHandle;
    fn deref(&self) -> &FileHandle {
        &self.file_handle
    }
}

/// NodeModulesPackageHandle describes a generated package under node_modules.
#[derive(Clone, Debug, Default)]
pub struct NodeModulesPackageHandle {
    pub name: String,
    pub directory: RootedDirectoryPath,
    package_json: FileHandle,
    declaration: FileHandle,
}

impl NodeModulesPackageHandle {
    /// `func (p NodeModulesPackageHandle) PackageJSONFile() FileHandle`
    pub fn package_json_file(&self) -> FileHandle {
        self.package_json.clone()
    }

    /// `func (p NodeModulesPackageHandle) DeclarationFile() FileHandle`
    pub fn declaration_file(&self) -> FileHandle {
        self.declaration.clone()
    }
}

/// MonorepoHandle exposes the generated monorepo layout including root and
/// packages.
#[derive(Clone, Debug, Default)]
pub struct MonorepoHandle {
    root: RootedDirectoryPath,
    root_node_modules: Vec<NodeModulesPackageHandle>,
    root_dependencies: Vec<String>,
    packages: Vec<ProjectHandle>,
    root_tsconfig: FileHandle,
    root_package_json: FileHandle,
}

impl MonorepoHandle {
    /// `func (m MonorepoHandle) Root() tspath.RootedDirectoryPath`
    pub fn root(&self) -> RootedDirectoryPath {
        self.root.clone()
    }

    /// `func (m MonorepoHandle) RootNodeModules() []NodeModulesPackageHandle`
    pub fn root_node_modules(&self) -> Vec<NodeModulesPackageHandle> {
        self.root_node_modules.clone()
    }

    /// `func (m MonorepoHandle) RootDependencies() []string`
    pub fn root_dependencies(&self) -> Vec<String> {
        self.root_dependencies.clone()
    }

    /// `func (m MonorepoHandle) Packages() []ProjectHandle`
    pub fn packages(&self) -> Vec<ProjectHandle> {
        self.packages.clone()
    }

    /// `func (m MonorepoHandle) Package(index int) ProjectHandle`
    pub fn package(&self, index: usize) -> ProjectHandle {
        if index >= self.packages.len() {
            panic!("package index {index} out of range");
        }
        self.packages[index].clone()
    }

    /// `func (m MonorepoHandle) RootTSConfig() FileHandle`
    pub fn root_tsconfig(&self) -> FileHandle {
        self.root_tsconfig.clone()
    }

    /// `func (m MonorepoHandle) RootPackageJSONFile() FileHandle`
    pub fn root_package_json_file(&self) -> FileHandle {
        self.root_package_json.clone()
    }
}

/// ProjectHandle exposes the generated project layout for a fixture project
/// root.
#[derive(Clone, Debug, Default)]
pub struct ProjectHandle {
    root: RootedDirectoryPath,
    files: Vec<ProjectFileHandle>,
    tsconfig: FileHandle,
    package_json: FileHandle,
    node_modules: Vec<NodeModulesPackageHandle>,
    dependencies: Vec<String>,
}

impl ProjectHandle {
    /// `func (p ProjectHandle) Root() tspath.RootedDirectoryPath`
    pub fn root(&self) -> RootedDirectoryPath {
        self.root.clone()
    }

    /// `func (p ProjectHandle) Files() []ProjectFileHandle`
    pub fn files(&self) -> Vec<ProjectFileHandle> {
        self.files.clone()
    }

    /// `func (p ProjectHandle) File(index int) ProjectFileHandle`
    pub fn file(&self, index: usize) -> ProjectFileHandle {
        if index >= self.files.len() {
            panic!("file index {index} out of range");
        }
        self.files[index].clone()
    }

    /// `func (p ProjectHandle) TSConfig() FileHandle`
    pub fn tsconfig(&self) -> FileHandle {
        self.tsconfig.clone()
    }

    /// `func (p ProjectHandle) PackageJSONFile() FileHandle`
    pub fn package_json_file(&self) -> FileHandle {
        self.package_json.clone()
    }

    /// `func (p ProjectHandle) NodeModules() []NodeModulesPackageHandle`
    pub fn node_modules(&self) -> Vec<NodeModulesPackageHandle> {
        self.node_modules.clone()
    }

    /// `func (p ProjectHandle) Dependencies() []string`
    pub fn dependencies(&self) -> Vec<String> {
        self.dependencies.clone()
    }

    /// `func (p ProjectHandle) NodeModuleByName(name string) *NodeModulesPackageHandle`
    pub fn node_module_by_name(&self, name: &str) -> Option<&NodeModulesPackageHandle> {
        self.node_modules.iter().find(|pkg| pkg.name == name)
    }
}

/// Fixture encapsulates a fully-initialized auto import lifecycle test
/// session.
///
/// `Drop` closes the session (Go's `t.Cleanup(session.Close)`).
pub struct Fixture {
    session: Arc<Session>,
    utils: SessionUtils,
    projects: Vec<ProjectHandle>,
}

impl Fixture {
    /// `func (f *Fixture) Session() *project.Session`
    pub fn session(&self) -> &Arc<Session> {
        &self.session
    }

    /// `func (f *Fixture) Utils() *projecttestutil.SessionUtils`
    pub fn utils(&self) -> &SessionUtils {
        &self.utils
    }

    /// `func (f *Fixture) Projects() []ProjectHandle`
    pub fn projects(&self) -> Vec<ProjectHandle> {
        self.projects.clone()
    }

    /// `func (f *Fixture) Project(index int) ProjectHandle`
    pub fn project(&self, index: usize) -> ProjectHandle {
        if index >= self.projects.len() {
            panic!("project index {index} out of range");
        }
        self.projects[index].clone()
    }

    /// `func (f *Fixture) SingleProject() ProjectHandle`
    pub fn single_project(&self) -> ProjectHandle {
        self.project(0)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        // Go: `t.Cleanup(session.Close)`.
        self.session.close();
    }
}

/// MonorepoFixture encapsulates a fully-initialized monorepo lifecycle test
/// session.
///
/// `Drop` closes the session (Go's `t.Cleanup(session.Close)`).
pub struct MonorepoFixture {
    session: Arc<Session>,
    utils: SessionUtils,
    monorepo: MonorepoHandle,
    extra: Vec<FileHandle>,
}

impl MonorepoFixture {
    /// `func (f *MonorepoFixture) Session() *project.Session`
    pub fn session(&self) -> &Arc<Session> {
        &self.session
    }

    /// `func (f *MonorepoFixture) Utils() *projecttestutil.SessionUtils`
    pub fn utils(&self) -> &SessionUtils {
        &self.utils
    }

    /// `func (f *MonorepoFixture) Monorepo() MonorepoHandle`
    pub fn monorepo(&self) -> MonorepoHandle {
        self.monorepo.clone()
    }

    /// `func (f *MonorepoFixture) ExtraFiles() []FileHandle`
    pub fn extra_files(&self) -> Vec<FileHandle> {
        self.extra.clone()
    }

    /// `func (f *MonorepoFixture) ExtraFile(path string) FileHandle`
    pub fn extra_file(&self, path: &str) -> FileHandle {
        let normalized = tspath::rooted_file_path_from_absolute(path);
        for handle in &self.extra {
            if handle.file_name == normalized {
                return handle.clone();
            }
        }
        panic!("extra file not found: {path}");
    }
}

impl Drop for MonorepoFixture {
    fn drop(&mut self) {
        // Go: `t.Cleanup(session.Close)`.
        self.session.close();
    }
}

/// MonorepoPackageTemplate captures the reusable settings for a package.json
/// scope: the node_modules packages that exist alongside the package.json and
/// the dependency names that should be written into that package.json. When
/// DependencyNames is empty, all available node_modules packages in scope are
/// used.
#[derive(Clone, Debug, Default)]
pub struct MonorepoPackageTemplate {
    pub name: String,
    pub node_module_names: Vec<String>,
    pub dependency_names: Vec<String>,
}

/// MonorepoSetupConfig describes the monorepo root and packages to create.
/// The embedded MonorepoPackageTemplate describes the monorepo root package
/// located at Root. DependencyNames defaults to NodeModuleNames when empty.
/// Package.MonorepoPackageTemplate.DependencyNames defaults to the union of
/// the root node_modules packages and the package's own NodeModuleNames when
/// empty.
///
/// PORT: Go's embedded `MonorepoPackageTemplate` fields are flattened in
/// (`name`, `node_module_names`, `dependency_names`).
#[derive(Default)]
pub struct MonorepoSetupConfig {
    pub root: String,
    // `MonorepoPackageTemplate` (embedded in Go):
    pub name: String,
    pub node_module_names: Vec<String>,
    pub dependency_names: Vec<String>,
    // end embedded fields
    pub packages: Vec<MonorepoPackageConfig>,
    pub extra_files: Vec<TextFileSpec>,
    pub symlinks: Vec<SymlinkSpec>,
}

/// `type MonorepoPackageConfig struct` — `MonorepoPackageTemplate` flattened
/// in as in [MonorepoSetupConfig].
#[derive(Default)]
pub struct MonorepoPackageConfig {
    pub file_count: i32,
    // `MonorepoPackageTemplate` (embedded in Go):
    pub name: String,
    pub node_module_names: Vec<String>,
    pub dependency_names: Vec<String>,
}

/// TextFileSpec describes an additional file to place in the fixture.
pub struct TextFileSpec {
    pub path: String,
    pub content: String,
}

/// SymlinkSpec describes a symlink to create in the fixture.
pub struct SymlinkSpec {
    /// The symlink path.
    pub link: String,
    /// The target path the symlink points to.
    pub target: String,
}

/// SetupMonorepoLifecycleSession builds a monorepo workspace with root-level
/// node_modules and multiple packages, each potentially with their own
/// node_modules. The structure is:
///
/// ```text
/// root/
/// ├── tsconfig.json (base config)
/// ├── package.json
/// ├── node_modules/
/// │   └── <rootNodeModuleCount packages>
/// └── packages/
///     ├── package-a/
///     │   ├── tsconfig.json
///     │   ├── package.json
///     │   ├── node_modules/
///     │   │   └── <package-specific packages>
///     │   └── *.ts files
///     └── package-b/
///         └── ...
/// ```
pub fn setup_monorepo_lifecycle_session(config: MonorepoSetupConfig) -> MonorepoFixture {
    let mut builder = FileMapBuilder::new(FxHashMap::default());

    let monorepo_root = tspath::rooted_directory_path_from_absolute(&config.root);
    let monorepo_name = if config.name.is_empty() {
        "monorepo"
    } else {
        config.name.as_str()
    };

    // Add root tsconfig.json
    let root_tsconfig_path = monorepo_root.resolve_file("tsconfig.json");
    let root_tsconfig_content = "{\n  \"compilerOptions\": {\n    \"module\": \"esnext\",\n    \"target\": \"esnext\",\n    \"strict\": true,\n    \"baseUrl\": \".\",\n    \"allowJs\": true,\n    \"checkJs\": true\n  }\n}\n";
    builder.add_text_file(root_tsconfig_path.as_string(), root_tsconfig_content);
    let root_tsconfig = FileHandle {
        file_name: root_tsconfig_path,
        content: root_tsconfig_content.to_string(),
    };

    // Add root node_modules
    let root_node_modules_dir = monorepo_root.resolve_directory("node_modules");
    let root_node_modules = builder.add_node_modules_packages_with_names(
        root_node_modules_dir.as_string(),
        &config.node_module_names,
    );

    // Add root package.json with dependencies (default to all root node_modules if unspecified)
    let root_dependencies = select_packages_by_name(&root_node_modules, &config.dependency_names);
    let root_package_json =
        builder.add_root_package_json(monorepo_root.as_string(), monorepo_name, &root_dependencies);
    let root_dependency_names = package_names(&root_dependencies);

    // Build each package in packages/
    let packages_dir = monorepo_root.resolve_directory("packages");
    let mut package_handles = Vec::with_capacity(config.packages.len());
    for pkg in &config.packages {
        let pkg_dir = packages_dir.resolve_directory(&pkg.name);
        builder.add_local_project(pkg_dir.as_string(), pkg.file_count);

        let mut pkg_node_modules = Vec::new();
        if !pkg.node_module_names.is_empty() {
            let pkg_node_modules_dir = pkg_dir.resolve_directory("node_modules");
            pkg_node_modules = builder.add_node_modules_packages_with_names(
                pkg_node_modules_dir.as_string(),
                &pkg.node_module_names,
            );
        }

        let mut available_deps = root_node_modules.clone();
        available_deps.extend(pkg_node_modules.iter().cloned());
        let selected_deps = select_packages_by_name(&available_deps, &pkg.dependency_names);
        if !selected_deps.is_empty() {
            builder.add_package_json_with_dependencies_named(
                pkg_dir.as_string(),
                &pkg.name,
                &selected_deps,
            );
        }
    }

    // Add arbitrary extra files
    let mut extra_handles = Vec::with_capacity(config.extra_files.len());
    for extra in &config.extra_files {
        builder.add_text_file(&extra.path, &extra.content);
        extra_handles.push(FileHandle {
            file_name: tspath::rooted_file_path_from_absolute(&extra.path),
            content: extra.content.clone(),
        });
    }

    // Add symlinks
    for symlink in &config.symlinks {
        builder.add_symlink(&symlink.link, &symlink.target);
    }

    // Build project handles after all packages are created
    for pkg in &config.packages {
        let pkg_dir = packages_dir.resolve_directory(&pkg.name);
        if let Some(record) = builder.projects.get(&pkg_dir) {
            package_handles.push(record.to_handles());
        }
    }

    let (session, session_utils) = projecttestutil::setup(builder.files());
    // Go: `t.Cleanup(session.Close)` — `MonorepoFixture::drop` closes it.

    // Build root node_modules handle by looking at the project record for the
    // workspace root (created as side effect of AddNodeModulesPackages)
    let mut root_node_modules_handles = Vec::new();
    if let Some(root_record) = builder.projects.get(&monorepo_root) {
        root_node_modules_handles = root_record.node_modules.clone();
    }

    MonorepoFixture {
        session,
        utils: session_utils,
        monorepo: MonorepoHandle {
            root: monorepo_root,
            root_node_modules: root_node_modules_handles,
            root_dependencies: root_dependency_names,
            packages: package_handles,
            root_tsconfig,
            root_package_json,
        },
        extra: extra_handles,
    }
}

/// SetupLifecycleSession builds a basic single-project workspace configured
/// with the requested number of TypeScript files and a single synthetic
/// node_modules package.
pub fn setup_lifecycle_session(project_root: &str, file_count: i32) -> Fixture {
    let mut builder = FileMapBuilder::new(FxHashMap::default());
    builder.add_local_project(project_root, file_count);
    let node_modules_dir = tspath::combine_paths(project_root, &["node_modules"]);
    let deps = builder.add_node_modules_packages(&node_modules_dir, 1);
    builder.add_package_json_with_dependencies(project_root, &deps);
    let (session, session_utils) = projecttestutil::setup(builder.files());
    // Go: `t.Cleanup(session.Close)` — `Fixture::drop` closes it.
    Fixture {
        session,
        utils: session_utils,
        projects: builder.project_handles(),
    }
}

/// `type fileMapBuilder struct`
struct FileMapBuilder {
    /// `files map[string]any` — `vfstest::TestFile` values (`Text` or a
    /// `MapFile` symlink).
    files: FxHashMap<String, vfstest::TestFile>,
    next_package_id: i32,
    next_project_id: i32,
    projects: FxHashMap<RootedDirectoryPath, ProjectRecord>,
}

/// `type projectRecord struct`
#[derive(Default)]
struct ProjectRecord {
    root: RootedDirectoryPath,
    source_files: Vec<ProjectFile>,
    tsconfig: FileHandle,
    package_json: Option<FileHandle>,
    node_modules: Vec<NodeModulesPackageHandle>,
    dependencies: Vec<String>,
}

/// `type projectFile struct`
struct ProjectFile {
    file_name: RootedFilePath,
    export_identifier: String,
    content: String,
}

impl FileMapBuilder {
    /// `func newFileMapBuilder(initial map[string]any) *fileMapBuilder`
    fn new(initial: FxHashMap<String, vfstest::TestFile>) -> FileMapBuilder {
        let mut b = FileMapBuilder {
            files: FxHashMap::default(),
            next_package_id: 0,
            next_project_id: 0,
            projects: FxHashMap::default(),
        };
        for (path, content) in initial {
            b.files.insert(normalize_absolute_path(&path), content);
        }
        b
    }

    /// `func (b *fileMapBuilder) ensureProjectRecord(root) *projectRecord`
    fn ensure_project_record(&mut self, root: RootedDirectoryPath) -> &mut ProjectRecord {
        self.projects
            .entry(root.clone())
            .or_insert_with(|| ProjectRecord {
                root,
                ..Default::default()
            })
    }

    /// `func (b *fileMapBuilder) projectHandles() []ProjectHandle`
    fn project_handles(&self) -> Vec<ProjectHandle> {
        let mut keys: Vec<RootedDirectoryPath> = self.projects.keys().cloned().collect();
        keys.sort_by(|a, b| a.compare(b).cmp(&0));
        keys.iter().map(|key| self.projects[key].to_handles()).collect()
    }

    /// `func (b *fileMapBuilder) Files() map[string]any`
    fn files(&self) -> FxHashMap<String, vfstest::TestFile> {
        self.files.clone()
    }

    /// `func (b *fileMapBuilder) AddTextFile(path string, contents string)`
    fn add_text_file(&mut self, path: &str, contents: &str) {
        self.files.insert(
            normalize_absolute_path(path),
            vfstest::TestFile::Text(contents.to_string()),
        );
    }

    /// AddSymlink creates a symlink from link_path to target_path.
    /// The target_path should be an absolute path.
    fn add_symlink(&mut self, link_path: &str, target_path: &str) {
        self.files.insert(
            normalize_absolute_path(link_path),
            vfstest::TestFile::MapFile(vfstest::symlink(&normalize_absolute_path(target_path))),
        );
    }

    /// `func (b *fileMapBuilder) AddNodeModulesPackages(nodeModulesDir string, count int) []NodeModulesPackageHandle`
    fn add_node_modules_packages(
        &mut self,
        node_modules_dir: &str,
        count: i32,
    ) -> Vec<NodeModulesPackageHandle> {
        let mut packages = Vec::with_capacity(count.max(0) as usize);
        for _ in 0..count {
            packages.push(self.add_node_modules_package(node_modules_dir));
        }
        packages
    }

    /// `func (b *fileMapBuilder) AddNodeModulesPackagesWithNames(nodeModulesDir string, names []string) []NodeModulesPackageHandle`
    fn add_node_modules_packages_with_names(
        &mut self,
        node_modules_dir: &str,
        names: &[String],
    ) -> Vec<NodeModulesPackageHandle> {
        let mut packages = Vec::with_capacity(names.len());
        for name in names {
            packages.push(self.add_named_node_modules_package(node_modules_dir, name));
        }
        packages
    }

    /// `func (b *fileMapBuilder) AddNodeModulesPackage(nodeModulesDir string) NodeModulesPackageHandle`
    fn add_node_modules_package(&mut self, node_modules_dir: &str) -> NodeModulesPackageHandle {
        self.add_named_node_modules_package(node_modules_dir, "")
    }

    /// `func (b *fileMapBuilder) AddNamedNodeModulesPackage(nodeModulesDir string, name string) NodeModulesPackageHandle`
    fn add_named_node_modules_package(
        &mut self,
        node_modules_dir: &str,
        name: &str,
    ) -> NodeModulesPackageHandle {
        let normalized_dir = tspath::rooted_directory_path_from_absolute(node_modules_dir);
        if normalized_dir.base_name() != "node_modules" {
            panic!("nodeModulesDir must point to a node_modules directory: {node_modules_dir}");
        }
        self.next_package_id += 1;
        let resolved_name = if name.is_empty() {
            format!("pkg{}", self.next_package_id)
        } else {
            name.to_string()
        };
        let export_name = format!("{}_value", sanitize_identifier(&resolved_name));
        let pkg_dir = normalized_dir.resolve_directory(&resolved_name);
        let package_json_path = pkg_dir.resolve_file("package.json");
        let package_json_content =
            format!("{{\"name\":\"{resolved_name}\",\"types\":\"index.d.ts\"}}");
        self.files.insert(
            package_json_path.as_string().to_string(),
            vfstest::TestFile::Text(package_json_content.clone()),
        );
        let declaration_path = pkg_dir.resolve_file("index.d.ts");
        let declaration_content = format!("export declare const {export_name}: number;\n");
        self.files.insert(
            declaration_path.as_string().to_string(),
            vfstest::TestFile::Text(declaration_content.clone()),
        );
        let package_handle = NodeModulesPackageHandle {
            name: resolved_name,
            directory: pkg_dir,
            package_json: FileHandle {
                file_name: package_json_path,
                content: package_json_content,
            },
            declaration: FileHandle {
                file_name: declaration_path,
                content: declaration_content,
            },
        };
        let project_root = normalized_dir.as_path().directory();
        self.ensure_project_record(project_root)
            .node_modules
            .push(package_handle.clone());
        package_handle
    }

    /// `func (b *fileMapBuilder) AddLocalProject(projectDir string, fileCount int)`
    fn add_local_project(&mut self, project_dir: &str, file_count: i32) {
        if file_count < 0 {
            panic!("fileCount must be non-negative");
        }
        let dir = tspath::rooted_directory_path_from_absolute(project_dir);
        self.next_project_id += 1;
        let tsconfig_path = dir.resolve_file("tsconfig.json");
        let tsconfig_content = "{\n  \"compilerOptions\": {\n    \"module\": \"esnext\",\n    \"target\": \"esnext\",\n    \"strict\": true,\n    \"allowJs\": true,\n    \"checkJs\": true\n  }\n}\n";
        self.files.insert(
            tsconfig_path.as_string().to_string(),
            vfstest::TestFile::Text(tsconfig_content.to_string()),
        );
        let mut source_files = Vec::new();
        for i in 1..=file_count {
            let path = dir.resolve_file(&format!("file{i}.ts"));
            let export_name = format!("localExport{}_{}", self.next_project_id, i);
            let content = format!("export const {export_name} = {i};\n");
            self.files.insert(
                path.as_string().to_string(),
                vfstest::TestFile::Text(content.clone()),
            );
            source_files.push(ProjectFile {
                file_name: path,
                export_identifier: export_name,
                content,
            });
        }
        let record = self.ensure_project_record(dir);
        record.tsconfig = FileHandle {
            file_name: tsconfig_path,
            content: tsconfig_content.to_string(),
        };
        record.source_files.extend(source_files);
    }

    /// `func (b *fileMapBuilder) AddPackageJSONWithDependencies(projectDir string, deps []NodeModulesPackageHandle) FileHandle`
    fn add_package_json_with_dependencies(
        &mut self,
        project_dir: &str,
        deps: &[NodeModulesPackageHandle],
    ) -> FileHandle {
        self.next_project_id += 1;
        self.add_package_json_with_dependencies_named(
            project_dir,
            &format!("local-project-{}", self.next_project_id),
            deps,
        )
    }

    /// `func (b *fileMapBuilder) AddPackageJSONWithDependenciesNamed(projectDir string, packageName string, deps []NodeModulesPackageHandle) FileHandle`
    fn add_package_json_with_dependencies_named(
        &mut self,
        project_dir: &str,
        package_name: &str,
        deps: &[NodeModulesPackageHandle],
    ) -> FileHandle {
        let dir = tspath::rooted_directory_path_from_absolute(project_dir);
        let package_json_path = dir.resolve_file("package.json");
        let dependency_lines: Vec<String> = deps
            .iter()
            .map(|dep| format!("\"{}\": \"*\"", dep.name))
            .collect();
        let mut builder = String::new();
        let mut name = package_name.to_string();
        if name.is_empty() {
            self.next_project_id += 1;
            name = format!("local-project-{}", self.next_project_id);
        }
        builder.push_str(&format!("{{\n  \"name\": \"{name}\""));
        if !dependency_lines.is_empty() {
            builder.push_str(",\n  \"dependencies\": {\n    ");
            builder.push_str(&dependency_lines.join(",\n    "));
            builder.push_str("\n  }\n");
        } else {
            builder.push('\n');
        }
        builder.push_str("}\n");
        let content = builder;
        self.files.insert(
            package_json_path.as_string().to_string(),
            vfstest::TestFile::Text(content.clone()),
        );
        let package_handle = FileHandle {
            file_name: package_json_path,
            content,
        };
        let record = self.ensure_project_record(dir);
        record.package_json = Some(package_handle.clone());
        record.dependencies = package_names(deps);
        package_handle
    }

    /// `addRootPackageJSON` creates a root package.json for a monorepo without
    /// creating a project record. This is used to set up the root workspace
    /// config without treating it as a project.
    fn add_root_package_json(
        &mut self,
        root_dir: &str,
        package_name: &str,
        deps: &[NodeModulesPackageHandle],
    ) -> FileHandle {
        let dir = tspath::rooted_directory_path_from_absolute(root_dir);
        let package_json_path = dir.resolve_file("package.json");
        let dependency_lines: Vec<String> = deps
            .iter()
            .map(|dep| format!("\"{}\": \"*\"", dep.name))
            .collect();
        let mut builder = String::new();
        let pkg_name = if package_name.is_empty() {
            "monorepo-root"
        } else {
            package_name
        };
        builder.push_str(&format!("{{\n  \"name\": \"{pkg_name}\",\n  \"private\": true"));
        if !dependency_lines.is_empty() {
            builder.push_str(",\n  \"dependencies\": {\n    ");
            builder.push_str(&dependency_lines.join(",\n    "));
            builder.push_str("\n  }\n");
        } else {
            builder.push('\n');
        }
        builder.push_str("}\n");
        let content = builder;
        self.files.insert(
            package_json_path.as_string().to_string(),
            vfstest::TestFile::Text(content.clone()),
        );
        FileHandle {
            file_name: package_json_path,
            content,
        }
    }
}

impl ProjectRecord {
    /// `func (r *projectRecord) toHandles() ProjectHandle`
    fn to_handles(&self) -> ProjectHandle {
        let files = self
            .source_files
            .iter()
            .map(|file| ProjectFileHandle {
                file_handle: FileHandle {
                    file_name: file.file_name.clone(),
                    content: file.content.clone(),
                },
                export_identifier: file.export_identifier.clone(),
            })
            .collect();
        let package_json = self.package_json.clone().unwrap_or_default();
        ProjectHandle {
            root: self.root.clone(),
            files,
            tsconfig: self.tsconfig.clone(),
            package_json,
            node_modules: self.node_modules.clone(),
            dependencies: self.dependencies.clone(),
        }
    }
}

/// `func selectPackagesByName(available []NodeModulesPackageHandle, names []string) []NodeModulesPackageHandle`
fn select_packages_by_name(
    available: &[NodeModulesPackageHandle],
    names: &[String],
) -> Vec<NodeModulesPackageHandle> {
    if names.is_empty() {
        return available.to_vec();
    }
    let mut result = Vec::with_capacity(names.len());
    for name in names {
        let mut found = false;
        for candidate in available {
            if candidate.name == *name {
                result.push(candidate.clone());
                found = true;
                break;
            }
        }
        if !found {
            panic!("dependency not found: {name}");
        }
    }
    result
}

/// `func packageNames(deps []NodeModulesPackageHandle) []string`
fn package_names(deps: &[NodeModulesPackageHandle]) -> Vec<String> {
    deps.iter().map(|dep| dep.name.clone()).collect()
}

/// `func sanitizeIdentifier(name string) string` — `strings.Map` with `r == -1`
/// dropping the rune.
fn sanitize_identifier(name: &str) -> String {
    let sanitized: String = name
        .chars()
        .filter_map(|r| match r {
            'a'..='z' | 'A'..='Z' | '0'..='9' => Some(r),
            '_' | '-' => Some('_'),
            _ => None,
        })
        .collect();
    if sanitized.is_empty() {
        "pkg".to_string()
    } else {
        sanitized
    }
}

/// `func normalizeAbsolutePath(path string) string`
fn normalize_absolute_path(path: &str) -> String {
    let normalized = tspath::normalize_path(path);
    if !tspath::path_is_absolute(&normalized) {
        panic!("paths used in lifecycle tests must be absolute: {path}");
    }
    normalized.into_owned()
}
