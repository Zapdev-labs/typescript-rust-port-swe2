// Ported from tsc/internal/ls/autoimport/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(concurrency): `createCheckerPool`'s goroutine pool becomes a
// single-slot sequential pool — `Checker`/`Node`/`Symbol` arenas are
// `Rc`/`RefCell`-based and cannot cross threads.
//
// `*ast.Symbol` → `SymbolId`; node dereferences go through per-file arenas
// reached via the checker's `program_nodes` (each declaration can live in a
// different file arena, so helpers take `SymbolId`/`NodeId` and borrow the
// arena of each node they touch rather than a single `nodes` slice).

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

use tsc_ast::Kind;
use tsc_ast::ast::Node;
use tsc_ast::symbol::Symbol;
use tsc_ast::{NodeId, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_collections::Set;
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_module::resolver::DefaultResolver;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::autoimport::export::{ModuleID, ambient_module_id, file_module_id};

/// `toUpper`/`toLower` — Go's `unicode.ToUpper`/`unicode.ToLower` apply the
/// Unicode *simple* (single-char) case mapping; Rust's `char::to_uppercase`
/// applies the *full* mapping (which expands e.g. 'ß' to "SS"). Keeping only
/// single-char mappings matches Go's behavior for word indexing.
pub(crate) fn to_upper(c: char) -> char {
    let mut it = c.to_uppercase();
    let first = it.next().unwrap_or(c);
    if it.next().is_some() { c } else { first }
}

/// `unicode.ToLower` — see `to_upper`.
pub(crate) fn to_lower(c: char) -> char {
    let mut it = c.to_lowercase();
    let first = it.next().unwrap_or(c);
    if it.next().is_some() { c } else { first }
}

/// `unicode.IsUpper`/`unicode.IsLower` shorthands.
pub(crate) fn is_upper(c: char) -> bool {
    c.is_uppercase()
}
pub(crate) fn is_lower(c: char) -> bool {
    c.is_lowercase()
}

/// `ast.GetSourceFileOfNode` — arena-aware: climbs `parent` links, borrowing
/// each node's own file arena through the checker.
pub(crate) fn get_source_file_of_node(node: Option<NodeId>, ch: &Checker) -> Option<NodeId> {
    let mut node = node;
    while let Some(n) = node {
        let nodes = ch.program_nodes(n);
        if nodes[n].kind == Kind::SourceFile {
            return Some(n);
        }
        node = nodes[n].parent;
    }
    None
}

/// `ast.GetNonAugmentationDeclaration` — arena-aware: each declaration is
/// inspected in its own file's arena.
pub(crate) fn get_non_augmentation_declaration(symbol: &Symbol, ch: &Checker) -> Option<NodeId> {
    symbol.declarations.iter().copied().find(|&d| {
        let nodes = ch.program_nodes(d);
        !tsc_ast::is_external_module_augmentation(&nodes[d], &nodes)
            && !tsc_ast::is_global_scope_augmentation(&nodes[d])
    })
}

/// `ast.GetSourceFileOfModule` — arena-aware variant taking `SymbolId`.
pub(crate) fn get_source_file_of_module(
    module: SymbolId,
    ch: &Rc<RefCell<Checker>>,
) -> Option<NodeId> {
    let declaration = {
        let c = ch.borrow();
        let sa = c.symbol_arena.borrow();
        let sym = &sa[module.index()];
        match sym.value_declaration {
            Some(d) => Some(d),
            None => get_non_augmentation_declaration(sym, &c),
        }
    };
    get_source_file_of_node(declaration, &ch.borrow())
}

/// `tryGetModuleIDAndFileNameOfModuleSymbol` — `(ModuleID, RootedFilePath,
/// bool)` becomes `Option<(ModuleID, RootedFilePath)>`.
pub(crate) fn try_get_module_id_and_file_name_of_module_symbol(
    symbol: SymbolId,
    ch: &Rc<RefCell<Checker>>,
) -> Option<(ModuleID, RootedFilePath)> {
    let decl = {
        let c = ch.borrow();
        let sa = c.symbol_arena.borrow();
        let sym = &sa[symbol.index()];
        if !sym.is_external_module() {
            return None;
        }
        get_non_augmentation_declaration(sym, &c)
    }?;
    let c = ch.borrow();
    let nodes = c.program_nodes(decl);
    if nodes[decl].kind == Kind::SourceFile {
        let sf = nodes[decl].as_source_file();
        return Some((
            file_module_id(sf.path_key().clone()),
            sf.file_name().clone(),
        ));
    }
    if tsc_ast::is_module_with_string_literal_name(&nodes[decl], &nodes) {
        let name = nodes[decl].name().expect("module name");
        return Some((
            ambient_module_id(&nodes[name].text(&nodes)),
            RootedFilePath::default(),
        ));
    }
    None
}

/// `getModuleIDAndFileNameOfModuleSymbol` — panics like Go when the symbol is
/// not a module.
#[allow(dead_code)]
pub(crate) fn get_module_id_and_file_name_of_module_symbol(
    symbol: SymbolId,
    ch: &Rc<RefCell<Checker>>,
) -> (ModuleID, RootedFilePath) {
    try_get_module_id_and_file_name_of_module_symbol(symbol, ch)
        .map(|(id, name)| {
            if id.kind == crate::autoimport::export::ModuleIdKind::Invalid {
                panic!("could not determine module ID of module symbol");
            }
            (id, name)
        })
        .expect("module symbol is not an external module or has no declaration")
}

/// `wordIndices` splits an identifier into its constituent words based on
/// camelCase and snake_case conventions by returning the starting byte
/// indices of each word. The first index is always 0.
///   - `CamelCase` → `^    ^`
///   - `snake_case` → `^     ^`
///   - `ParseURL` → `^    ^`
///   - `__proto__` → `^`
pub(crate) fn word_indices(s: &str) -> Vec<usize> {
    let mut indices = Vec::new();
    let mut prev_char: Option<char> = None;
    for (byte_index, rune_value) in s.char_indices() {
        if byte_index == 0 {
            indices.push(byte_index);
            prev_char = Some(rune_value);
            continue;
        }
        if rune_value == '_' {
            let bytes = s.as_bytes();
            if byte_index + 1 < s.len() && bytes[byte_index + 1] != b'_' {
                indices.push(byte_index + 1);
            }
            prev_char = Some(rune_value);
            continue;
        }
        if is_upper(rune_value) {
            let prev_is_lower = prev_char.is_some_and(is_lower);
            let next_is_lower = s[byte_index + rune_value.len_utf8()..]
                .chars()
                .next()
                .is_some_and(is_lower);
            if prev_is_lower || next_is_lower {
                indices.push(byte_index);
            }
        }
        prev_char = Some(rune_value);
    }
    indices
}

/// `getPackageNamesInNodeModules`.
pub(crate) fn get_package_names_in_node_modules(
    node_modules_dir: &RootedDirectoryPath,
    fs: &Arc<dyn tsc_vfs::Vfs>,
) -> Set<String> {
    let mut package_names = Set::new();
    if node_modules_dir.as_path().base_name() != "node_modules" {
        panic!("nodeModulesDir is not a node_modules directory");
    }
    // A missing node_modules directory yields no entries (GetAccessibleEntries
    // returns empty), so there's no need to check existence first: a deleted
    // node_modules is handled upstream in updateBucketAndDirectoryExistence,
    // which drops the bucket.
    let entries = fs.get_accessible_entries(node_modules_dir);
    for base_name in &entries.directories {
        if base_name.starts_with('.') {
            continue;
        }
        if base_name.starts_with('@') {
            let scoped_dir_path = node_modules_dir.resolve_directory(base_name);
            for scoped_package_dir_name in &fs.get_accessible_entries(&scoped_dir_path).directories
            {
                let scoped_base_name = tsc_tspath::get_base_file_name(scoped_package_dir_name);
                if base_name == "@types" {
                    package_names.add(tsc_module::get_package_name_from_types_package_name(
                        &tsc_tspath::combine_paths("@types", &[scoped_base_name.as_ref()]),
                    ));
                } else {
                    package_names.add(tsc_tspath::combine_paths(
                        base_name,
                        &[scoped_base_name.as_ref()],
                    ));
                }
            }
            continue;
        }
        package_names.add(base_name.clone());
    }
    package_names
}

/// `getDefaultLikeExportNameFromDeclaration`.
pub(crate) fn get_default_like_export_name_from_declaration(
    symbol: &Symbol,
    ch: &Rc<RefCell<Checker>>,
) -> String {
    for &d in &symbol.declarations {
        let c = ch.borrow();
        let nodes = c.program_nodes(d);
        // "export default" in this case. See `ExportAssignment` for more details.
        if tsc_ast::is_export_assignment(&nodes[d]) {
            let inner_expression = tsc_ast::skip_outer_expressions(
                nodes[d].expression().unwrap(),
                tsc_ast::utilities::outer_expression_kinds::ALL,
                &nodes,
            );
            if tsc_ast::is_identifier(&nodes[inner_expression]) {
                return nodes[inner_expression].text(&nodes).to_string();
            }
            continue;
        }
        // "export { ~ as default }"
        if tsc_ast::is_export_specifier(&nodes[d]) {
            let is_alias = nodes[d].symbol().is_some_and(|s| {
                c.symbol_arena.borrow()[s.index()].flags == tsc_ast::symbolflags::SymbolFlags::ALIAS
            });
            if is_alias && nodes[d].property_name().is_some() {
                let property_name = nodes[d].property_name().unwrap();
                if nodes[property_name].kind == Kind::Identifier {
                    return nodes[property_name].text(&nodes).to_string();
                }
                continue;
            }
        }
        // GH#52694
        if let Some(name) = tsc_ast::get_name_of_declaration(Some(d), &nodes)
            && nodes[name].kind == Kind::Identifier
        {
            return nodes[name].text(&nodes).to_string();
        }
        if let Some(parent) = symbol.parent {
            let parent_sym_is_external = {
                let sa = c.symbol_arena.borrow();
                sa[parent.index()].is_external_module()
            };
            if !parent_sym_is_external {
                return c.symbol_arena.borrow()[parent.index()].name.clone();
            }
        }
    }
    String::new()
}

/// `getResolvedPackageNames`.
pub(crate) fn get_resolved_package_names(ctx: &Context, program: &Rc<Program>) -> Set<String> {
    let raw_names = program.resolved_package_names();
    let unresolved_package_names = program.unresolved_package_names();

    // Normalize @types/ package names to their actual package names
    // (e.g., "@types/react" → "react"). ResolvedPackageNames can contain
    // @types names when the program resolves an import like "react" to
    // "@types/react/index.d.ts" via the PackageId.Name field.
    let mut resolved_package_names = Set::with_size_hint(raw_names.len());
    for name in raw_names.iter() {
        resolved_package_names.add(tsc_module::get_package_name_from_types_package_name(name));
    }

    if let Some(types) = &program.options().types {
        for name in types {
            if name != "*" {
                resolved_package_names
                    .add(tsc_module::get_package_name_from_types_package_name(name));
            }
        }
    }

    if !unresolved_package_names.is_empty() {
        let (checker, done) = program.get_type_checker(ctx.clone());
        for name in unresolved_package_names.iter() {
            if let Some(symbol) = checker.borrow_mut().try_find_ambient_module_api(name)
                && let Some(declaring_file) = get_source_file_of_module(symbol, &checker)
            {
                let file_name = {
                    let c = checker.borrow();
                    let nodes = c.program_nodes(declaring_file);
                    nodes[declaring_file].as_source_file().file_name().clone()
                };
                let declaring_file_path = file_name.as_path();
                let package_name = tsc_modulespecifiers::util::get_package_name_from_directory(
                    &declaring_file_path,
                );
                if !package_name.is_empty() {
                    resolved_package_names.add(
                        tsc_module::get_package_name_from_types_package_name(package_name),
                    );
                }
            }
        }
        drop(done);
    }
    resolved_package_names
}

/// `addProjectReferenceOutputMappings` adds output .d.ts to source file
/// mappings from a program's project references to the provided map. This is
/// used during node_modules bucket building to redirect extraction from output
/// files to source files when the output is from a project reference.
pub(crate) fn add_project_reference_output_mappings(
    program: &Program,
    result: &mut rustc_hash::FxHashMap<PathKey, RootedFilePath>,
) {
    for refr in program.get_resolved_project_references() {
        let Some(refr) = refr else { continue };
        refr.parse_input_output_names();
        if let Some(mappings) = refr.output_dts_to_project_reference() {
            for (output_dts_path, mapping) in mappings.iter() {
                // Only add if not already present (first program wins)
                result
                    .entry(output_dts_path.clone())
                    .or_insert_with(|| mapping.source.clone());
            }
        }
    }
}

/// `createCheckerPool` — Go pools checkers across `runtime.GOMAXPROCS`
/// goroutines; this port is single-threaded (see module comment), so the pool
/// lazily creates a single checker and hands it out sequentially.
pub(crate) struct CheckerPool {
    program: Rc<dyn tsc_checker::checker_types::Program>,
    checker: RefCell<Option<Rc<RefCell<Checker>>>>,
    created: std::cell::Cell<u32>,
}

impl CheckerPool {
    pub(crate) fn new(program: Rc<dyn tsc_checker::checker_types::Program>) -> Self {
        Self {
            program,
            checker: RefCell::new(None),
            created: std::cell::Cell::new(0),
        }
    }

    /// `getChecker()` — returns the shared checker; the returned guard is a
    /// no-op (`done()` in Go returns the checker to the pool).
    pub(crate) fn get_checker(&self) -> (Rc<RefCell<Checker>>, impl FnOnce()) {
        let mut slot = self.checker.borrow_mut();
        if slot.is_none() {
            self.created.set(self.created.get() + 1);
            *slot = Some(Rc::new(RefCell::new(
                tsc_checker::checker_core::Checker::new_checker(self.program.clone(), None),
            )));
        }
        (slot.clone().unwrap(), || {})
    }

    /// `getCreatedCount`.
    pub(crate) fn created_count(&self) -> u32 {
        self.created.get()
    }
}

/// `addPackageJsonDependencies` adds all dependencies and peerDependencies
/// from a package.json to the given set, canonicalizing @types package names
/// to their base names.
pub(crate) fn add_package_json_dependencies(
    contents: &tsc_packagejson::PackageJson,
    deps: &mut Set<String>,
) {
    contents.range_dependencies(|name, _version, field| {
        if name.is_empty() || name == "@types/" || name.starts_with('.') {
            // Edge cases that could make us blow up probably
            return true;
        }
        if field == "dependencies" || field == "peerDependencies" {
            deps.add(tsc_module::get_package_name_from_types_package_name(name));
        }
        true
    });
}

/// `pathAndFileName`.
#[derive(Clone, Default)]
pub(crate) struct PathAndFileName {
    pub path: PathKey,
    pub file_name: RootedFilePath,
}

/// `type realpathFn func(tspath.RootedFilePath) tspath.RootedFilePath`.
///
/// PORT: `Arc` + `Send + Sync` (rather than `Rc`) because the function is
/// installed into `wrapvfs::Replacements`, whose overrides must be `Send`.
pub(crate) type RealpathFn = Arc<dyn Fn(&RootedFilePath) -> RootedFilePath + Send + Sync>;

/// `getPackageRealpathFuncs` returns functions to transform between symlink
/// and realpath for files within a package. It calls `FS.Realpath` once per
/// package directory and uses prefix substitution for files within that
/// directory, avoiding expensive realpath syscalls for each file. For files
/// outside the package (e.g. re-exported dependencies reached through
/// node_modules symlinks), it resolves the file's directory realpath once,
/// finds the symlink boundary (the package root where the symlink lives), and
/// caches that prefix mapping. All subsequent files under the same symlinked
/// package directory use prefix substitution with no syscalls.
pub(crate) fn get_package_realpath_funcs(
    fs: &Arc<dyn tsc_vfs::Vfs>,
    package_directory: &RootedDirectoryPath,
) -> (RealpathFn, RealpathFn) {
    let real_package_directory =
        tsc_tspath::rooted_directory_path_from_path(fs.realpath(&package_directory.as_path()));
    let is_symlinked = real_package_directory != *package_directory;
    // Cache of package-directory-level symlink→realpath prefix mappings for
    // external packages encountered via re-exports. Keyed by the node_modules
    // package directory (e.g. "/app/node_modules/dep"), so all files under
    // that package reuse a single realpath lookup.
    let dir_cache: Mutex<HashMap<RootedDirectoryPath, RootedDirectoryPath>> =
        Mutex::new(HashMap::new());
    let fs2 = fs.clone();
    let package_directory2 = package_directory.clone();
    let real_package_directory2 = real_package_directory.clone();
    let to_realpath: RealpathFn = Arc::new(move |file_name: &RootedFilePath| {
        // Fast path: files within the package use prefix substitution.
        if is_symlinked && let Some(relative) = file_name.relative_to(&package_directory2) {
            return real_package_directory2.resolve_relative_file(&relative);
        }
        // Files outside the package (e.g. re-exports into symlinked deps):
        // find the node_modules package directory, resolve it once, and cache.
        let mut file_package_dir = tsc_module::node_module_package_root_for_file(file_name);
        if file_package_dir.as_string().is_empty() {
            return file_name.clone();
        }
        // The wrapped FS also calls Realpath while traversing directories.
        // The two parses differ only when the path may be a package root,
        // so establish its kind before using the package cache.
        let directory = tsc_tspath::rooted_directory_path_from_path(RootedPath::from(
            file_name.as_string().to_string(),
        ));
        let directory_package = tsc_module::node_module_package_root_for_directory(&directory);
        if directory_package != file_package_dir && fs2.directory_exists(&directory) {
            file_package_dir = directory_package;
        }
        let mut cache = dir_cache.lock().unwrap();
        if let Some(real_dir) = cache.get(&file_package_dir) {
            if *real_dir == file_package_dir {
                return file_name.clone();
            }
            let relative = file_name.relative_to(&file_package_dir).unwrap_or_default();
            return real_dir.resolve_relative_file(&relative);
        }
        let real_dir =
            tsc_tspath::rooted_directory_path_from_path(fs2.realpath(&file_package_dir.as_path()));
        cache.insert(file_package_dir.clone(), real_dir.clone());
        if real_dir == file_package_dir {
            return file_name.clone();
        }
        let relative = file_name.relative_to(&file_package_dir).unwrap_or_default();
        real_dir.resolve_relative_file(&relative)
    });
    if !is_symlinked {
        // `toSymlink` is `core.Identity`.
        return (to_realpath.clone(), to_realpath);
    }
    // toSymlink only handles files within the package directory (reversing
    // the packageDir→realPackageDir substitution). It does not handle
    // arbitrary external paths; callers should only use it for files known to
    // be within the package.
    let package_directory3 = package_directory.clone();
    let to_symlink: RealpathFn = Arc::new(move |file_name: &RootedFilePath| {
        if let Some(relative) = file_name.relative_to(&real_package_directory) {
            return package_directory3.resolve_relative_file(&relative);
        }
        file_name.clone()
    });
    (to_realpath, to_symlink)
}

/// `type resolutionHost struct` — `module.ResolutionHost`.
pub(crate) struct ResolutionHostImpl {
    pub fs: Arc<dyn tsc_vfs::Vfs>,
    pub current_directory: RootedDirectoryPath,
}

impl tsc_module::types::ResolutionHost for ResolutionHostImpl {
    fn fs(&self) -> &Arc<dyn tsc_vfs::Vfs> {
        &self.fs
    }
    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.current_directory.clone()
    }
}

/// `getModuleResolver`.
pub(crate) fn get_module_resolver(
    fs: &Arc<dyn tsc_vfs::Vfs>,
    current_directory: &RootedDirectoryPath,
    realpath: RealpathFn,
    mut opts: tsc_module::ResolverOptions,
) -> DefaultResolver {
    let realpath_path = move |path: &RootedPath| -> RootedPath {
        realpath(&tsc_tspath::rooted_file_path_from_path(path.clone())).as_path()
    };
    let rh = ResolutionHostImpl {
        fs: tsc_vfs::wrapvfs::wrap(
            fs.clone(),
            tsc_vfs::wrapvfs::Replacements {
                realpath: Some(Box::new(realpath_path)),
                ..Default::default()
            },
        ),
        current_directory: current_directory.clone(),
    };
    opts.host = Arc::new(rh);
    opts.compiler_options = Arc::new(tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS.clone());
    DefaultResolver::new(opts)
}
