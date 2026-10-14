// Ported from tsc/internal/compiler/checkerpool.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: the Go pool parallelizes checker creation and checker-group work via
// `core.WorkGroup` and guards each checker with a `sync.Mutex`. The Rust port
// is intentionally single-threaded (see PORTING-NOTES): checkers live behind
// `Rc<RefCell<Checker>>` (not `Send`), so `forEachChecker*` run sequentially
// and the `locks`/`sync.Once` fields become `Cell`s/`RefCell`s with no-op
// release functions. `*ast.SourceFile` file associations key on `NodeId`.
// The association algorithm (weighted FENNEL partitioning) is preserved
// verbatim — it still runs, and still matters, because it assigns each file
// to exactly one checker.

use std::cell::{Cell, RefCell};
use std::rc::{Rc, Weak};
use std::sync::Arc;

use rustc_hash::FxHashMap;

use tsc_ast::NodeId;
use tsc_ast::diagnostic::{
    DiagnosticRef, compare_diagnostics, equal_diagnostics, equal_diagnostics_no_related_info,
    lock_diagnostic,
};
use tsc_checker::checker_core::Checker;
use tsc_checker::checker_types::Program as CheckerProgram;
use tsc_checker::tracer::Tracer;
use tsc_core::context::Context;
use tsc_tracing::Tracing;

/// `*Program` view needed by the checker pool beyond what
/// `tsc_checker::checker_types::Program` already exposes (`options`,
/// `source_files`, `nodes`, `get_resolved_modules`,
/// `get_source_file_for_resolved_module`). program.rs implements this for
/// `crate::program::Program`; keeping the boundary here decouples the pool
/// from `Program`'s concrete layout.
/// `'static`: checker construction erases `P` into `Rc<dyn CheckerProgram>`.
pub trait CheckerPoolProgram: CheckerProgram + 'static {
    /// `p.SingleThreaded()`.
    fn single_threaded(&self) -> bool;
    /// Per-`file_index` arena lengths at a point in time (None = absent).
    /// The fork-parallel check path snapshots this before `fork` so a
    /// diagnostic referencing a node minted after the fork (invisible to
    /// the parent) can be detected.
    fn arena_lengths(&self) -> Vec<Option<usize>>;
    /// PORT(addition): emit a single file inside the fused fork child —
    /// `try_fork_check_and_emit` runs it after collecting the file's
    /// checker diagnostics, reusing the child's warm COW checker state.
    /// `self` is the child's private program copy. Only called on Unix;
    /// default panics so non-`Program` implementors can't be reached.
    #[cfg(unix)]
    fn emit_one_forked(
        &self,
        ctx: Context,
        file: NodeId,
        emit_only: crate::emit_host::EmitOnly,
        force_emit: bool,
        force_dts_emit: bool,
        force_js_emit: bool,
    ) -> crate::emit_host::EmitResult {
        let _ = (ctx, file, emit_only, force_emit, force_dts_emit, force_js_emit);
        unimplemented!("emit_one_forked requires the concrete Program")
    }
}

/// PORT(addition): emit parameters for the fused check+emit fork wave —
/// see `CompilerCheckerPool::try_fork_check_and_emit`. `emit_files` is the
/// already-resolved emit set (`get_source_files_to_emit`); each child
/// emits the intersection of its check group with this set.
#[derive(Clone)]
pub struct ForkEmitPlan {
    pub emit_only: crate::emit_host::EmitOnly,
    pub force_emit: bool,
    pub force_dts_emit: bool,
    pub force_js_emit: bool,
    pub emit_files: Vec<NodeId>,
}

/// `func SortAndDeduplicateDiagnostics` (program.go). Kept in this module —
/// checkerpool.go is a caller and program.rs is ported separately; program.rs
/// can re-export `crate::checker_pool::sort_and_deduplicate_diagnostics`.
pub fn sort_and_deduplicate_diagnostics(mut diagnostics: Vec<DiagnosticRef>) -> Vec<DiagnosticRef> {
    // `slices.Clone` is implicit — the caller hands ownership over.
    // `slices.SortFunc` is unstable pdqsort → `sort_unstable_by`.
    diagnostics.sort_unstable_by(|a, b| compare_diagnostics(a, b).cmp(&0));
    compact_and_merge_related_infos(diagnostics)
}

/// `func compactAndMergeRelatedInfos` — remove duplicate diagnostics and, for
/// runs of diagnostics that differ only by related information, create a
/// single diagnostic with sorted and deduplicated related information.
/// Compacts in place like the Go slice version.
fn compact_and_merge_related_infos(mut diagnostics: Vec<DiagnosticRef>) -> Vec<DiagnosticRef> {
    if diagnostics.len() < 2 {
        return diagnostics;
    }
    let mut i = 0usize;
    let mut j = 0usize;
    while i < diagnostics.len() {
        let mut d = diagnostics[i].clone();
        let mut n = 1usize;
        while i + n < diagnostics.len()
            && equal_diagnostics_no_related_info(&d, &diagnostics[i + n])
        {
            n += 1;
        }
        if n > 1 {
            let mut related_infos: Vec<DiagnosticRef> = Vec::new();
            for k in 0..n {
                related_infos.extend(
                    lock_diagnostic(&diagnostics[i + k])
                        .related_information()
                        .iter()
                        .cloned(),
                );
            }
            if !related_infos.is_empty() {
                related_infos.sort_unstable_by(|a, b| compare_diagnostics(a, b).cmp(&0));
                // `slices.CompactFunc` — consecutive dedup.
                related_infos.dedup_by(|a, b| equal_diagnostics(a, b));
                // `d.Clone().SetRelatedInfo(relatedInfos)`.
                d = {
                    let guard = lock_diagnostic(&d);
                    guard.clone_diagnostic()
                };
                lock_diagnostic(&d).set_related_info(related_infos);
            }
        }
        diagnostics[j] = d;
        i += n;
        j += 1;
    }
    diagnostics.truncate(j);
    diagnostics
}

/// `func()` — the release function returned with each checker.
pub type DoneFn = Box<dyn FnOnce()>;

/// `type CheckerPool interface` — implemented by the project system to
/// provide checkers with request-scoped lifetime and reclamation. Each
/// acquisition is exclusive (a `&mut` through `RefCell` in this port) and
/// not reentrant; the release function must be called when done.
///
/// PORT: `file *ast.SourceFile` is `Option<NodeId>` (Go nil-able).
pub trait CheckerPool {
    /// `GetChecker(ctx, file)`.
    fn get_checker(&self, ctx: Context, file: Option<NodeId>) -> (Rc<RefCell<Checker>>, DoneFn);
}

pub const CHECKER_ASSOCIATION_TEXT_WEIGHT_DIVISOR: i64 = 100;
pub const CHECKER_ASSOCIATION_SOURCE_FILE_WEIGHT_MULTIPLIER: i64 = 4;
pub const CHECKER_ASSOCIATION_BALANCE_PENALTY_MULTIPLIER: i64 = 16;
pub const CHECKER_ASSOCIATION_PRIORITIZED_SOURCE_PENALTY: i64 = 12;
pub const CHECKER_ASSOCIATION_STRONG_BALANCE_MIN_CHECKER_COUNT: usize = 4;

/// `type checkerAssociationPolicy struct`.
#[derive(Debug, PartialEq, Eq)]
struct CheckerAssociationPolicy {
    prioritize_source_files: bool,
    source_file_weight_multiplier: i64,
    balance_penalty_multiplier: i64,
}

/// `getCheckerAssociationPolicy` — see the extensive calibration comments in
/// checkerpool.go; the operating points are verbatim.
fn get_checker_association_policy(
    total_weight: i64,
    declaration_weight: i64,
    checker_count: usize,
) -> CheckerAssociationPolicy {
    if should_prioritize_source_files(total_weight, declaration_weight, checker_count) {
        return CheckerAssociationPolicy {
            prioritize_source_files: true,
            source_file_weight_multiplier: 1,
            balance_penalty_multiplier: CHECKER_ASSOCIATION_PRIORITIZED_SOURCE_PENALTY,
        };
    }
    if checker_count >= CHECKER_ASSOCIATION_STRONG_BALANCE_MIN_CHECKER_COUNT {
        return CheckerAssociationPolicy {
            prioritize_source_files: false,
            source_file_weight_multiplier: CHECKER_ASSOCIATION_SOURCE_FILE_WEIGHT_MULTIPLIER,
            balance_penalty_multiplier: CHECKER_ASSOCIATION_BALANCE_PENALTY_MULTIPLIER,
        };
    }
    CheckerAssociationPolicy {
        prioritize_source_files: false,
        source_file_weight_multiplier: 1,
        balance_penalty_multiplier: 1,
    }
}

/// `getCheckerAssociationsInOrder` — weighted FENNEL (gamma = 3/2); a `None`
/// order means stable program order.
pub fn get_checker_associations_in_order(
    file_weights: &[i64],
    adjacent_files: &[Vec<usize>],
    file_order: Option<&[usize]>,
    checker_count: usize,
    penalty_multiplier: i64,
) -> Vec<i32> {
    if file_weights.is_empty() {
        return Vec::new();
    }

    let mut total_weight: i64 = 0;
    let mut max_file_weight: i64 = 0;
    let mut edge_count: i64 = 0;
    for (i, &weight) in file_weights.iter().enumerate() {
        total_weight += weight;
        max_file_weight = max_file_weight.max(weight);
        edge_count += adjacent_files[i].len() as i64;
    }

    let mut associations = vec![-1i32; file_weights.len()];
    let mut checker_weights = vec![0i64; checker_count];
    let average_checker_weight = (total_weight + checker_count as i64 - 1) / checker_count as i64;
    let max_checker_weight =
        max_file_weight.max(average_checker_weight + average_checker_weight / 100);
    let total_weight_float = total_weight as f64;
    let alpha = penalty_multiplier as f64 * (edge_count / 2) as f64 * (checker_count as f64).sqrt()
        / (total_weight_float * total_weight_float.sqrt());
    let mut neighbor_counts = vec![0i64; checker_count];

    for position in 0..file_weights.len() {
        let file_index = match file_order {
            Some(order) => order[position],
            None => position,
        };

        neighbor_counts.fill(0);
        for &adjacent_file in &adjacent_files[file_index] {
            let checker_index = associations[adjacent_file];
            if checker_index >= 0 {
                neighbor_counts[checker_index as usize] += 1;
            }
        }

        let mut best_checker: i32 = -1;
        let mut best_score = f64::NEG_INFINITY;
        for (checker_index, &checker_weight) in checker_weights.iter().enumerate() {
            if checker_weight + file_weights[file_index] > max_checker_weight {
                continue;
            }
            let old_weight = checker_weight as f64;
            let new_weight = (checker_weight + file_weights[file_index]) as f64;
            let new_penalty = new_weight * new_weight.sqrt();
            let old_penalty = old_weight * old_weight.sqrt();
            let penalty = alpha * (new_penalty - old_penalty);
            let score = neighbor_counts[checker_index] as f64 - penalty;
            if score > best_score
                || score == best_score
                    && (best_checker < 0 || checker_weight < checker_weights[best_checker as usize])
            {
                best_checker = checker_index as i32;
                best_score = score;
            }
        }
        if best_checker < 0 {
            best_checker = 0;
            for (checker_index, &checker_weight) in checker_weights[1..].iter().enumerate() {
                if checker_weight < checker_weights[best_checker as usize] {
                    best_checker = checker_index as i32 + 1;
                }
            }
        }
        associations[file_index] = best_checker;
        checker_weights[best_checker as usize] += file_weights[file_index];
    }
    associations
}

/// `getCheckerAssociationOrder` — `None` preserves program order.
fn get_checker_association_order(
    file_weights: &[i64],
    is_declaration_file: &[bool],
    prioritize_source_files: bool,
) -> Option<Vec<usize>> {
    if !prioritize_source_files {
        return None;
    }
    let mut file_order: Vec<usize> = (0..file_weights.len()).collect();
    // `sort.Slice` (unstable) — Go's comparator is a strict weak ordering
    // here, so `sort_unstable` matches.
    file_order.sort_unstable_by(|&i, &j| {
        let left = i;
        let right = j;
        if is_declaration_file[left] != is_declaration_file[right] {
            // `return !isDeclarationFile[left]` — source files before
            // declarations.
            return is_declaration_file[left].cmp(&is_declaration_file[right]);
        }
        if file_weights[left] != file_weights[right] {
            return file_weights[right].cmp(&file_weights[left]);
        }
        left.cmp(&right)
    });
    Some(file_order)
}

/// `getCheckerAssociationBaseWeight`.
fn get_checker_association_base_weight(node_count: i64, text_length: i64) -> i64 {
    (node_count + text_length / CHECKER_ASSOCIATION_TEXT_WEIGHT_DIVISOR).max(1)
}

/// `shouldPrioritizeSourceFiles` — `declarationWeight <= totalWeight /
/// (2 * checkerCount)`.
fn should_prioritize_source_files(
    total_weight: i64,
    declaration_weight: i64,
    checker_count: usize,
) -> bool {
    declaration_weight * checker_count as i64 * 2 <= total_weight
}

/// `getCheckerAssociationWeights`.
fn get_checker_association_weights(base_weights: &[i64], import_counts: &[i64]) -> Vec<i64> {
    let mut total_base_weight: i64 = 0;
    let mut total_imports: i64 = 0;
    for (i, &base_weight) in base_weights.iter().enumerate() {
        total_base_weight += base_weight;
        total_imports += import_counts[i];
    }
    let import_weight = if total_imports > 0 {
        (total_base_weight / total_imports).max(1)
    } else {
        0
    };
    base_weights
        .iter()
        .enumerate()
        .map(|(i, &base_weight)| base_weight + import_counts[i] * import_weight)
        .collect()
}

/// `type checkerPool struct` — the built-in compiler checker pool.
///
/// PORT: `program` is `Weak` (Go's `*Program` back-edge would create an
/// `Rc` cycle). `locks` are dropped — the single-threaded port serializes
/// checker access through `RefCell` borrows; `done` release functions are
/// no-ops.
pub struct CompilerCheckerPool<P: CheckerPoolProgram> {
    program: Weak<P>,
    tracing: Option<Arc<Tracing>>,

    /// `createCheckersOnce` + `checkers` + `fileAssociations`.
    checkers_created: Cell<bool>,
    checkers: RefCell<Vec<Rc<RefCell<Checker>>>>,
    file_associations: RefCell<FxHashMap<NodeId, usize>>,
    checker_count: usize,
}

/// `newCheckerPool`.
pub fn new_checker_pool<P: CheckerPoolProgram>(program: &Rc<P>) -> CompilerCheckerPool<P> {
    new_checker_pool_with_tracing(program, None)
}

/// `newCheckerPool` / `newCheckerPoolWithTracing`.
pub fn new_checker_pool_with_tracing<P: CheckerPoolProgram>(
    program: &Rc<P>,
    tr: Option<Arc<Tracing>>,
) -> CompilerCheckerPool<P> {
    let mut checker_count = 4;
    if program.single_threaded() {
        checker_count = 1;
    } else if let Some(c) = program.options().checkers {
        checker_count = c as usize;
    }
    // DEBUG: isolate cross-checker TypeId aliasing.
    if std::env::var("TSC_ONE_CHECKER").is_ok() {
        checker_count = 1;
    }

    checker_count = checker_count
        .min(program.source_files().len())
        .min(256)
        .max(1);

    CompilerCheckerPool {
        program: Rc::downgrade(program),
        checkers: RefCell::new(Vec::new()),
        file_associations: RefCell::new(FxHashMap::default()),
        tracing: tr,
        checkers_created: Cell::new(false),
        checker_count,
    }
}

fn noop_done() -> DoneFn {
    Box::new(|| {})
}

impl<P: CheckerPoolProgram> CompilerCheckerPool<P> {
    /// `createCheckers` — lazily create the checkers and compute file→checker
    /// associations.
    fn create_checkers(&self) {
        if self.checkers_created.replace(true) {
            return;
        }
        let Some(program) = self.program.upgrade() else {
            return;
        };
        let checker_count = self.checker_count;
        // Go queues checker creation on a work group; here it is sequential.
        let program_trait: Rc<dyn CheckerProgram> = program.clone();
        let mut checkers = Vec::with_capacity(checker_count);
        for i in 0..checker_count {
            let tracer = self.tracing.as_ref().map(|tr| Tracer::new(tr, i as i32));
            checkers.push(Rc::new(RefCell::new(Checker::new_checker(
                program_trait.clone(),
                tracer,
            ))));
        }

        let files = program.source_files();
        let mut associations = vec![0i32; files.len()];
        if checker_count > 1 {
            let mut base_weights = Vec::with_capacity(files.len());
            let mut import_counts = Vec::with_capacity(files.len());
            let mut is_declaration_file = Vec::with_capacity(files.len());
            let mut total_base_weight: i64 = 0;
            let mut declaration_base_weight: i64 = 0;
            for &file in files.iter() {
                let nodes = program.nodes(file.file_index());
                let sf = nodes[file].as_source_file();
                let base_weight =
                    get_checker_association_base_weight(sf.node_count as i64, sf.text.len() as i64);
                total_base_weight += base_weight;
                if sf.is_declaration_file {
                    declaration_base_weight += base_weight;
                }
                base_weights.push(base_weight);
                import_counts.push(sf.imports().len() as i64);
                is_declaration_file.push(sf.is_declaration_file);
            }
            let policy = get_checker_association_policy(
                total_base_weight,
                declaration_base_weight,
                checker_count,
            );
            if policy.source_file_weight_multiplier != 1 {
                // Apply this before import normalization. The policy
                // intentionally increases both source-file work and the
                // normalized import unit.
                for (i, &declaration) in is_declaration_file.iter().enumerate() {
                    if !declaration {
                        base_weights[i] *= policy.source_file_weight_multiplier;
                    }
                }
            }
            let file_weights = get_checker_association_weights(&base_weights, &import_counts);
            let adjacent_files = self.get_import_adjacency(&program);
            let file_order = get_checker_association_order(
                &file_weights,
                &is_declaration_file,
                policy.prioritize_source_files,
            );
            associations = get_checker_associations_in_order(
                &file_weights,
                &adjacent_files,
                file_order.as_deref(),
                checker_count,
                policy.balance_penalty_multiplier,
            );
        }
        let mut file_associations =
            FxHashMap::with_capacity_and_hasher(files.len(), Default::default());
        for (i, &file) in files.iter().enumerate() {
            file_associations.insert(file, associations[i] as usize);
        }
        *self.file_associations.borrow_mut() = file_associations;
        *self.checkers.borrow_mut() = checkers;
    }

    /// `getImportAdjacency` — an undirected import graph by file index.
    fn get_import_adjacency(&self, program: &Rc<P>) -> Vec<Vec<usize>> {
        let files = program.source_files();
        let file_indices: FxHashMap<NodeId, usize> =
            files.iter().enumerate().map(|(i, &f)| (f, i)).collect();
        let mut adjacent_files: Vec<Vec<usize>> = vec![Vec::new(); files.len()];
        for (file_index, &file) in files.iter().enumerate() {
            let path_key = {
                let nodes = program.nodes(file.file_index());
                nodes[file].as_source_file().path_key().clone()
            };
            let resolved_modules = program
                .get_resolved_modules()
                .get(&path_key)
                .cloned()
                .unwrap_or_default();
            for resolved in resolved_modules.values() {
                let Some(resolved) = resolved else {
                    continue;
                };
                if !resolved.is_resolved() {
                    continue;
                }
                let Some(imported_file) = program.get_source_file_for_resolved_module(resolved)
                else {
                    continue;
                };
                let Some(&imported_index) = file_indices.get(&imported_file) else {
                    continue;
                };
                if imported_index == file_index {
                    continue;
                }
                adjacent_files[file_index].push(imported_index);
                adjacent_files[imported_index].push(file_index);
            }
        }
        adjacent_files
    }

    /// `getCheckerForFileNonExclusive` — emit resolver path; no locking in
    /// the single-threaded port.
    pub fn get_checker_for_file_non_exclusive(
        &self,
        file: NodeId,
    ) -> (Rc<RefCell<Checker>>, DoneFn) {
        self.create_checkers();
        let idx = self
            .file_associations
            .borrow()
            .get(&file)
            .copied()
            .unwrap_or(0);
        (self.checkers.borrow()[idx].clone(), noop_done())
    }

    /// `getCheckerForFileExclusive`.
    pub fn get_checker_for_file_exclusive(
        &self,
        _ctx: Context,
        file: NodeId,
    ) -> (Rc<RefCell<Checker>>, DoneFn) {
        self.create_checkers();
        let idx = self
            .file_associations
            .borrow()
            .get(&file)
            .copied()
            .unwrap_or(0);
        (self.checkers.borrow()[idx].clone(), noop_done())
    }

    /// `getCheckerNonExclusive`.
    pub fn get_checker_non_exclusive(&self) -> (Rc<RefCell<Checker>>, DoneFn) {
        self.create_checkers();
        (self.checkers.borrow()[0].clone(), noop_done())
    }

    /// `forEachCheckerParallel` — sequential in the single-threaded port.
    pub fn for_each_checker_parallel(&self, cb: &mut dyn FnMut(usize, &Rc<RefCell<Checker>>)) {
        self.create_checkers();
        for (idx, checker) in self.checkers.borrow().iter().enumerate() {
            cb(idx, checker);
        }
    }

    /// `GetGlobalDiagnostics`.
    pub fn get_global_diagnostics(&self) -> Vec<DiagnosticRef> {
        self.create_checkers();
        let mut global_diagnostics: Vec<DiagnosticRef> = Vec::new();
        self.for_each_checker_parallel(&mut |_idx, checker| {
            global_diagnostics.extend(checker.borrow_mut().get_global_diagnostics());
        });
        sort_and_deduplicate_diagnostics(global_diagnostics)
    }

    /// `forEachCheckerGroupDo` — one task per checker; each task iterates
    /// the provided files, processing only those assigned to its checker.
    /// Sequential under the single-threaded port.
    pub fn for_each_checker_group_do(
        &self,
        _ctx: Context,
        files: &[NodeId],
        _single_threaded: bool,
        cb: &mut dyn FnMut(&Rc<RefCell<Checker>>, usize, NodeId),
    ) {
        let __ct = std::time::Instant::now();
        self.create_checkers();
        if std::env::var("TSC_FILE_TIME").is_ok() {
            eprintln!("[create-checkers] {:?}", __ct.elapsed());
        }
        let mut __cb_total = std::time::Duration::ZERO;
        let __wall0 = std::time::Instant::now();
        let checker_count = self.checkers.borrow().len();
        for checker_idx in 0..checker_count {
            let checker = self.checkers.borrow()[checker_idx].clone();
            for (i, &file) in files.iter().enumerate() {
                if self
                    .file_associations
                    .borrow()
                    .get(&file)
                    .copied()
                    .unwrap_or(0)
                    == checker_idx
                {
                    let __t = std::time::Instant::now();
                    cb(&checker, i, file);
                    let __e = __t.elapsed();
                    __cb_total += __e;
                    if std::env::var("TSC_FILE_TIME").is_ok() {
                        eprintln!(
                            "[cb-gap] start={:?} dur={__e:?} fidx={i}",
                            __t - __wall0
                        );
                    }
                }
            }
        }
        if std::env::var("TSC_FILE_TIME").is_ok() {
            eprintln!("[cb-total] {__cb_total:?} wall={:?}", __wall0.elapsed());
        }
    }

    pub fn checker_count(&self) -> usize {
        self.checkers.borrow().len().max(self.checker_count)
    }

    /// PORT(addition): run each checker group's `collect` in a *forked*
    /// child process — parallel type checking without the `Rc`→`Arc`
    /// refactor. `fork` clones the address space; each child gets
    /// COW-private copies of the program/checker state, runs `collect` for
    /// its group's files, and streams the diagnostics back over a pipe
    /// (`tsc_ast::diagnostic::write_diagnostic`). The parent runs group 0
    /// itself, reads children to EOF, `waitpid`s, and deserializes —
    /// `NodeId`s inside children's diagnostics resolve parent-side because
    /// the arenas are identical (child writes never escape COW).
    ///
    /// Returns `None` when forking is not applicable (single checker/file,
    /// `singleThreaded`, `TSC_NO_FORK_CHECK`/`TSC_FILE_TIME` env, a pprof
    /// dir configured — the pprof sampler thread must not survive fork),
    /// or when a `pipe`/`fork` syscall fails — callers fall back to the
    /// sequential path in that case. A child that crashes or produces a
    /// diagnostics blob containing a node-less `DiagnosticFile` likewise
    /// degrades: its group re-runs sequentially in the parent.
    ///
    /// SAFETY/fork contract:
    /// - The child body runs between `fork` and `libc::_exit` — it must
    ///   not run destructors of objects the parent will reuse (it doesn't:
    ///   `Vec<DiagnosticRef>` writes into its own COW copies), must not
    ///   take locks a dead sibling thread held (no threads run inside
    ///   `collect`; the pprof sampler is gated out), and must not unwind
    ///   past the child boundary (the `catch_unwind` + `_exit` does it).
    /// - Children only ever `write()` to their pipe — no printf-path
    ///   locks, no allocator-at-exit (`_exit` skips `atexit`/destructors).
    #[cfg(unix)]
    #[allow(unsafe_code)]
    pub fn try_fork_collect(
        &self,
        ctx: Context,
        files: &[NodeId],
        single_threaded: bool,
        collect: &mut dyn FnMut(Context, &Rc<RefCell<Checker>>, NodeId) -> Vec<DiagnosticRef>,
    ) -> Option<Vec<Vec<DiagnosticRef>>> {
        use tsc_ast::diagnostic::DiagnosticFile;
        use tsc_ast::diagnostic::{has_unresolvable_files, read_diagnostic, write_diagnostic};

        if single_threaded
            || std::env::var("TSC_NO_FORK_CHECK").is_ok()
            || std::env::var("TSC_FILE_TIME").is_ok()
        {
            return None;
        }
        self.create_checkers();
        let checkers = self.checkers.borrow().clone();
        if checkers.len() <= 1 || files.len() <= 1 {
            return None;
        }
        let program = self.program.upgrade()?;
        // The pprof profiler runs a sampler thread — a child forking from
        // a multithreaded parent may inherit a held malloc/profiling lock.
        if !program.options().pprof_dir.as_string().is_empty() {
            return None;
        }
        // Arena lengths now = the node ids the parent can resolve after
        // the fork. A child diagnostic pointing past this (into a node's
        // scratch/synthetic pushes, or an arena absent pre-fork) can't be
        // rebuilt parent-side — such blobs are flagged and the group
        // re-runs sequentially.
        let arena_lens = program.arena_lengths();

        // Files grouped per checker index, file order preserved within
        // each group. PORT(divergence): Go assigns files to checkers
        // round-robin via `fileAssociations`; the fork wall time is the
        // slowest *group*, so we LPT-balance groups by per-file node
        // count instead — one giant file would otherwise strand its
        // group as the critical path while siblings idle. Diagnostics
        // are per-file deterministic regardless of which checker runs
        // them (Go's own parallel pool relies on that), and the parent
        // reassembles by original file index, so output is unchanged.
        let mut by_cost: Vec<(usize, NodeId, u64)> = files
            .iter()
            .enumerate()
            .map(|(i, &f)| {
                let cost = program.nodes(f.file_index()).len() as u64;
                (i, f, cost)
            })
            .collect();
        by_cost.sort_unstable_by(|a, b| b.2.cmp(&a.2));
        let mut loads = vec![0u64; checkers.len()];
        let mut groups: Vec<Vec<(usize, NodeId)>> = vec![Vec::new(); checkers.len()];
        for (i, file, cost) in by_cost {
            let g = loads
                .iter()
                .enumerate()
                .min_by_key(|&(_, &l)| l)
                .map(|(gi, _)| gi)
                .unwrap_or(0);
            groups[g].push((i, file));
            loads[g] += cost;
        }
        for group in &mut groups {
            group.sort_unstable_by_key(|&(i, _)| i);
        }

        let mut diagnostics: Vec<Vec<DiagnosticRef>> = vec![Vec::new(); files.len()];
        // (pid, read_fd, group_index) — read ends stay open until drained.
        let mut children: Vec<(libc::pid_t, libc::c_int, usize)> = Vec::new();

        for (g, group) in groups.iter().enumerate().skip(1) {
            if group.is_empty() {
                continue;
            }
            let mut fds = [0 as libc::c_int; 2];
            // SAFETY: `fds` points at valid storage.
            if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
                return None;
            }
            // SAFETY: preconditions per the doc contract — forked children
            // below are confined to their own COW state plus one pipe.
            let pid = unsafe { libc::fork() };
            if pid < 0 {
                unsafe {
                    libc::close(fds[0]);
                    libc::close(fds[1]);
                }
                // Keep groups already forked running; the failed group
                // runs sequentially below.
                continue;
            }
            if pid == 0 {
                // ------- CHILD -------
                // SAFETY: the read end is never used here.
                unsafe { libc::close(fds[0]) };
                let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut buf = Vec::new();
                    let checker = &checkers[g];
                    buf.extend_from_slice(&(group.len() as u32).to_le_bytes());
                    let mut unresolvable = false;
                    for &(i, file) in group {
                        let diags = collect(ctx.clone(), checker, file);
                        if !unresolvable
                            && diags.iter().any(|d| {
                                has_unresolvable_files(d)
                                    || has_foreign_nodes(d, &arena_lens)
                            })
                        {
                            unresolvable = true;
                        }
                        buf.extend_from_slice(&(i as u32).to_le_bytes());
                        buf.extend_from_slice(&(diags.len() as u32).to_le_bytes());
                        for d in &diags {
                            let _ = write_diagnostic(d, &mut buf);
                        }
                    }
                    // Trailer: 1 = cleanly reimportable, 0 = contains a
                    // node-less DiagnosticFile — parent re-runs the group.
                    buf.push(if unresolvable { 0 } else { 1 });
                    let mut off = 0;
                    while off < buf.len() {
                        // SAFETY: `buf[off..]` is a valid byte range; `fds[1]`
                        // is the live write end of this child's pipe.
                        let n = unsafe {
                            libc::write(
                                fds[1],
                                buf.as_ptr().add(off) as *const libc::c_void,
                                buf.len() - off,
                            )
                        };
                        if n <= 0 {
                            break;
                        }
                        off += n as usize;
                    }
                }));
                // SAFETY: `_exit` skips destructors/atexit — mandatory in
                // the forked child (parent threads may hold stdio or
                // allocator locks the child can never release).
                unsafe { libc::_exit(0) };
            }
            unsafe { libc::close(fds[1]) };
            children.push((pid, fds[0], g));
        }

        // Group 0 runs in the parent (matches the sequential path's
        // first-checker-in-parent behavior).
        for &(i, file) in &groups[0] {
            diagnostics[i] = collect(ctx.clone(), &checkers[0], file);
        }

        let read_all = |fd: libc::c_int| -> Vec<u8> {
            let mut out = Vec::new();
            let mut chunk = [0u8; 1 << 16];
            loop {
                // SAFETY: `chunk` is a valid buffer and `fd` is a live
                // read end until close.
                let n = unsafe {
                    libc::read(fd, chunk.as_mut_ptr() as *mut libc::c_void, chunk.len())
                };
                if n <= 0 {
                    break;
                }
                out.extend_from_slice(&chunk[..n as usize]);
            }
            unsafe { libc::close(fd) };
            out
        };

        let mut blobs: Vec<(usize, Option<Vec<u8>>)> = Vec::new();
        for (pid, fd, g) in children {
            let buf = read_all(fd);
            let mut status: libc::c_int = 0;
            // SAFETY: `status` points at valid storage; `pid` is our child.
            let rc = unsafe { libc::waitpid(pid, &mut status, 0) };
            let clean =
                rc == pid && libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0;
            let blob = if clean && !buf.is_empty() { Some(buf) } else { None };
            blobs.push((g, blob));
        }

        let mut resolve_file = |node: NodeId| -> Option<DiagnosticFile> {
            let len = arena_lens
                .get(node.file_index() as usize)
                .copied()
                .flatten()?;
            if node.local_index() as usize >= len {
                return None;
            }
            Some(DiagnosticFile::from_node(
                node,
                &program.nodes(node.file_index()),
            ))
        };

        for (g, blob) in blobs {
            let ok = blob
                .as_ref()
                .is_some_and(|b| *b.last().unwrap_or(&0) == 1);
            if let Some(mut b) = blob.filter(|_| ok) {
                b.pop(); // trailer byte
                let mut cursor = std::io::Cursor::new(b);
                let parsed: Option<()> = (|| {
                    let count = r_u32_wire(&mut cursor).ok()?;
                    for _ in 0..count {
                        let i = r_u32_wire(&mut cursor).ok()? as usize;
                        let n = r_u32_wire(&mut cursor).ok()? as usize;
                        let mut diags = Vec::with_capacity(n);
                        for _ in 0..n {
                            diags.push(read_diagnostic(&mut cursor, &mut resolve_file).ok()?);
                        }
                        if i < diagnostics.len() {
                            diagnostics[i] = diags;
                        }
                    }
                    Some(())
                })();
                if parsed.is_some() {
                    continue;
                }
            }
            // Re-run this group in the parent (empty/corrupt/unresolvable
            // blob or a crashed child) — diagnostics must not be lost.
            for &(i, file) in &groups[g] {
                diagnostics[i] = collect(ctx.clone(), &checkers[g], file);
            }
        }

        Some(diagnostics)
    }

    /// PORT(addition): fused check+emit fork wave for `tsc` emit runs.
    /// Same orchestration as `try_fork_collect`, but each child *also*
    /// emits its group's emit-plan files after collecting the file's
    /// checker diagnostics — the child's COW checker state is already
    /// warm, so the whole serial emit wave plus a second round of cold
    /// caches disappears. Returns `(per-file diagnostics, EmitResult)`.
    ///
    /// `None` means "not applicable": same gates as `try_fork_collect`,
    /// plus every `plan.emit_files` entry must be in `files` (emit files
    /// ride along on the check group that checked them).
    ///
    /// Per-file wire record: `[u32 file_idx][u32 ndiag][diags][u8 did_emit]
    /// [emit_result?]`; same trailer flag as `try_fork_collect`. A group
    /// that fails or carries unresolvable data re-runs in the parent —
    /// the re-emit rewrites identical outputs (see `try_fork_emit`).
    #[cfg(unix)]
    #[allow(unsafe_code)]
    pub fn try_fork_check_and_emit(
        &self,
        ctx: Context,
        files: &[NodeId],
        single_threaded: bool,
        collect: &mut dyn FnMut(Context, &Rc<RefCell<Checker>>, NodeId) -> Vec<DiagnosticRef>,
        plan: &ForkEmitPlan,
    ) -> Option<(Vec<Vec<DiagnosticRef>>, crate::emit_host::EmitResult)> {
        use crate::emit_host::{EmitResult, read_emit_result, write_emit_result};
        use tsc_ast::diagnostic::{DiagnosticFile, has_unresolvable_files, read_diagnostic, write_diagnostic};

        if single_threaded
            || std::env::var("TSC_NO_FORK_CHECK").is_ok()
            || std::env::var("TSC_NO_FORK_EMIT").is_ok()
            || std::env::var("TSC_FILE_TIME").is_ok()
        {
            return None;
        }
        self.create_checkers();
        let checkers = self.checkers.borrow().clone();
        if checkers.len() <= 1 || files.len() <= 1 {
            return None;
        }
        let program = self.program.upgrade()?;
        if !program.options().pprof_dir.as_string().is_empty() {
            return None;
        }
        let emit_set: rustc_hash::FxHashSet<NodeId> =
            plan.emit_files.iter().copied().collect();
        if emit_set.is_empty() {
            return None;
        }
        {
            let check_set: rustc_hash::FxHashSet<NodeId> = files.iter().copied().collect();
            if plan.emit_files.iter().any(|f| !check_set.contains(f)) {
                return None;
            }
        }
        let arena_lens = program.arena_lengths();

        // Same LPT grouping as `try_fork_collect`.
        let mut by_cost: Vec<(usize, NodeId, u64)> = files
            .iter()
            .enumerate()
            .map(|(i, &f)| {
                let cost = program.nodes(f.file_index()).len() as u64;
                (i, f, cost)
            })
            .collect();
        by_cost.sort_unstable_by(|a, b| b.2.cmp(&a.2));
        let mut loads = vec![0u64; checkers.len()];
        let mut groups: Vec<Vec<(usize, NodeId)>> = vec![Vec::new(); checkers.len()];
        for (i, file, cost) in by_cost {
            let g = loads
                .iter()
                .enumerate()
                .min_by_key(|&(_, &l)| l)
                .map(|(gi, _)| gi)
                .unwrap_or(0);
            groups[g].push((i, file));
            loads[g] += cost;
        }
        for group in &mut groups {
            group.sort_unstable_by_key(|&(i, _)| i);
        }

        let emit_one = |file: NodeId| -> EmitResult {
            program.emit_one_forked(
                ctx.clone(),
                file,
                plan.emit_only,
                plan.force_emit,
                plan.force_dts_emit,
                plan.force_js_emit,
            )
        };

        let mut diagnostics: Vec<Vec<DiagnosticRef>> = vec![Vec::new(); files.len()];
        let mut emit_results: FxHashMap<NodeId, EmitResult> = FxHashMap::default();
        let mut children: Vec<(libc::pid_t, libc::c_int, usize)> = Vec::new();

        for (g, group) in groups.iter().enumerate().skip(1) {
            if group.is_empty() {
                continue;
            }
            let mut fds = [0 as libc::c_int; 2];
            // SAFETY: `fds` points at valid storage.
            if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
                return None;
            }
            // SAFETY: fork contract identical to `try_fork_collect`.
            let pid = unsafe { libc::fork() };
            if pid < 0 {
                unsafe {
                    libc::close(fds[0]);
                    libc::close(fds[1]);
                }
                continue;
            }
            if pid == 0 {
                // ------- CHILD -------
                // SAFETY: the read end is never used here.
                unsafe { libc::close(fds[0]) };
                let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut buf = Vec::new();
                    let checker = &checkers[g];
                    buf.extend_from_slice(&(group.len() as u32).to_le_bytes());
                    let mut unresolvable = false;
                    for &(i, file) in group {
                        let diags = collect(ctx.clone(), checker, file);
                        if !unresolvable
                            && diags.iter().any(|d| {
                                has_unresolvable_files(d)
                                    || has_foreign_nodes(d, &arena_lens)
                            })
                        {
                            unresolvable = true;
                        }
                        buf.extend_from_slice(&(i as u32).to_le_bytes());
                        buf.extend_from_slice(&(diags.len() as u32).to_le_bytes());
                        for d in &diags {
                            let _ = write_diagnostic(d, &mut buf);
                        }
                        if emit_set.contains(&file) {
                            let r = emit_one(file);
                            if !unresolvable
                                && r.diagnostics.iter().any(|d| {
                                    has_unresolvable_files(d)
                                        || has_foreign_nodes(d, &arena_lens)
                                })
                            {
                                unresolvable = true;
                            }
                            buf.push(1);
                            let _ = write_emit_result(&r, &mut buf);
                        } else {
                            buf.push(0);
                        }
                    }
                    buf.push(if unresolvable { 0 } else { 1 });
                    let mut off = 0;
                    while off < buf.len() {
                        // SAFETY: `buf[off..]` valid; `fds[1]` is the live
                        // write end of this child's pipe.
                        let n = unsafe {
                            libc::write(
                                fds[1],
                                buf.as_ptr().add(off) as *const libc::c_void,
                                buf.len() - off,
                            )
                        };
                        if n <= 0 {
                            break;
                        }
                        off += n as usize;
                    }
                }));
                // SAFETY: `_exit` — no destructors/atexit in a forked child.
                unsafe { libc::_exit(0) };
            }
            unsafe { libc::close(fds[1]) };
            children.push((pid, fds[0], g));
        }

        // Group 0 in the parent.
        for &(i, file) in &groups[0] {
            diagnostics[i] = collect(ctx.clone(), &checkers[0], file);
            if emit_set.contains(&file) {
                emit_results.insert(file, emit_one(file));
            }
        }

        let read_all = |fd: libc::c_int| -> Vec<u8> {
            let mut out = Vec::new();
            let mut chunk = [0u8; 1 << 16];
            loop {
                // SAFETY: valid buffer, live read end.
                let n = unsafe {
                    libc::read(fd, chunk.as_mut_ptr() as *mut libc::c_void, chunk.len())
                };
                if n <= 0 {
                    break;
                }
                out.extend_from_slice(&chunk[..n as usize]);
            }
            unsafe { libc::close(fd) };
            out
        };

        let mut blobs: Vec<(usize, Option<Vec<u8>>)> = Vec::new();
        for (pid, fd, g) in children {
            let buf = read_all(fd);
            let mut status: libc::c_int = 0;
            // SAFETY: `status` valid; `pid` is our child.
            let rc = unsafe { libc::waitpid(pid, &mut status, 0) };
            let clean =
                rc == pid && libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0;
            let blob = if clean && !buf.is_empty() { Some(buf) } else { None };
            blobs.push((g, blob));
        }

        let mut resolve_file = |node: NodeId| -> Option<DiagnosticFile> {
            let len = arena_lens
                .get(node.file_index() as usize)
                .copied()
                .flatten()?;
            if node.local_index() as usize >= len {
                return None;
            }
            Some(DiagnosticFile::from_node(
                node,
                &program.nodes(node.file_index()),
            ))
        };

        for (g, blob) in blobs {
            let ok = blob
                .as_ref()
                .is_some_and(|b| *b.last().unwrap_or(&0) == 1);
            if let Some(mut b) = blob.filter(|_| ok) {
                b.pop(); // trailer byte
                let mut cursor = std::io::Cursor::new(b);
                let parsed: Option<()> = (|| {
                    let count = r_u32_wire(&mut cursor).ok()? as usize;
                    for _ in 0..count {
                        let i = r_u32_wire(&mut cursor).ok()? as usize;
                        let n = r_u32_wire(&mut cursor).ok()? as usize;
                        let mut diags = Vec::with_capacity(n);
                        for _ in 0..n {
                            diags.push(read_diagnostic(&mut cursor, &mut resolve_file).ok()?);
                        }
                        let emitted = {
                            let mut b1 = [0u8; 1];
                            std::io::Read::read_exact(&mut cursor, &mut b1).ok()?;
                            b1[0]
                        };
                        if i < diagnostics.len() {
                            diagnostics[i] = diags;
                        }
                        if emitted == 1 {
                            let r = read_emit_result(&mut cursor, &mut resolve_file).ok()?;
                            if i < files.len() {
                                emit_results.insert(files[i], r);
                            }
                        }
                    }
                    Some(())
                })();
                if parsed.is_some() {
                    continue;
                }
            }
            // Re-run this group in the parent — see `try_fork_collect`.
            for &(i, file) in &groups[g] {
                diagnostics[i] = collect(ctx.clone(), &checkers[g], file);
                if emit_set.contains(&file) {
                    emit_results.insert(file, emit_one(file));
                }
            }
        }

        // Merge emit results in `plan.emit_files` order.
        let merged = crate::program::combine_emit_results(
            plan.emit_files
                .iter()
                .map(|f| emit_results.remove(f).unwrap_or_default()),
        );
        Some((diagnostics, merged))
    }
}

/// Recursive walk: does any `DiagnosticFile::node` in `d` point outside
/// the pre-fork arena snapshot (`arena_lens`)? Such nodes were minted in
/// the child post-fork and cannot be resolved in the parent.
#[cfg(unix)]
pub(crate) fn has_foreign_nodes(d: &DiagnosticRef, arena_lens: &[Option<usize>]) -> bool {
    let d = lock_diagnostic(d);
    if let Some(node) = d.file().as_ref().and_then(|f| f.node) {
        let in_snapshot = arena_lens
            .get(node.file_index() as usize)
            .copied()
            .flatten()
            .is_some_and(|len| (node.local_index() as usize) < len);
        if !in_snapshot {
            return true;
        }
    }
    d.message_chain()
        .iter()
        .chain(d.related_information().iter())
        .any(|n| has_foreign_nodes(n, arena_lens))
}

/// Read a wire-format u32 used by the diagnostic pipe protocol.
#[cfg(unix)]
fn r_u32_wire(r: &mut impl std::io::Read) -> std::io::Result<u32> {
    let mut b = [0u8; 4];
    r.read_exact(&mut b)?;
    Ok(u32::from_le_bytes(b))
}

impl<P: CheckerPoolProgram> CheckerPool for CompilerCheckerPool<P> {
    /// `GetChecker` — with a file, returns the checker associated with it;
    /// without, returns the first checker.
    fn get_checker(&self, ctx: Context, file: Option<NodeId>) -> (Rc<RefCell<Checker>>, DoneFn) {
        match file {
            Some(file) => self.get_checker_for_file_exclusive(ctx, file),
            None => {
                self.create_checkers();
                (self.checkers.borrow()[0].clone(), noop_done())
            }
        }
    }
}

// Ported from checkerpool_test.go @ ec47d33c.
//
// `TestGetSourceFileForResolvedModuleUsesResolvedPath` is not ported: it
// constructs a bare `&Program{filesByPath: ...}`, which the Rust `Program`
// cannot express without a full program build.
#[cfg(test)]
mod tests {
    use super::*;

    /// `TestGetCheckerAssociationBaseWeight`.
    #[test]
    fn test_get_checker_association_base_weight() {
        assert_eq!(get_checker_association_base_weight(100, 2500), 125);
    }

    /// `TestShouldPrioritizeSourceFiles`.
    #[test]
    fn test_should_prioritize_source_files() {
        assert!(should_prioritize_source_files(1000, 100, 4));
        // Boundary.
        assert!(should_prioritize_source_files(1000, 125, 4));
        assert!(!should_prioritize_source_files(1000, 126, 4));
    }

    /// `TestGetCheckerAssociationPolicy`.
    #[test]
    fn test_get_checker_association_policy() {
        struct Case {
            name: &'static str,
            total_weight: i64,
            declaration_weight: i64,
            checker_count: usize,
            want: CheckerAssociationPolicy,
        }
        let tests = [
            Case {
                name: "source dominated at any checker count",
                total_weight: 1000,
                declaration_weight: 100,
                checker_count: 2,
                want: CheckerAssociationPolicy {
                    prioritize_source_files: true,
                    source_file_weight_multiplier: 1,
                    balance_penalty_multiplier: CHECKER_ASSOCIATION_PRIORITIZED_SOURCE_PENALTY,
                },
            },
            Case {
                name: "declaration heavy with few checkers",
                total_weight: 1000,
                declaration_weight: 400,
                checker_count: 2,
                want: CheckerAssociationPolicy {
                    prioritize_source_files: false,
                    source_file_weight_multiplier: 1,
                    balance_penalty_multiplier: 1,
                },
            },
            Case {
                name: "source dominated with many checkers",
                total_weight: 1000,
                declaration_weight: 50,
                checker_count: 8,
                want: CheckerAssociationPolicy {
                    prioritize_source_files: true,
                    source_file_weight_multiplier: 1,
                    balance_penalty_multiplier: CHECKER_ASSOCIATION_PRIORITIZED_SOURCE_PENALTY,
                },
            },
            Case {
                name: "declaration heavy with many checkers",
                total_weight: 1000,
                declaration_weight: 400,
                checker_count: 4,
                want: CheckerAssociationPolicy {
                    prioritize_source_files: false,
                    source_file_weight_multiplier:
                        CHECKER_ASSOCIATION_SOURCE_FILE_WEIGHT_MULTIPLIER,
                    balance_penalty_multiplier: CHECKER_ASSOCIATION_BALANCE_PENALTY_MULTIPLIER,
                },
            },
        ];
        for test in &tests {
            let got = get_checker_association_policy(
                test.total_weight,
                test.declaration_weight,
                test.checker_count,
            );
            assert_eq!(got, test.want, "{}", test.name);
        }
    }

    /// `TestGetCheckerAssociationOrder`.
    #[test]
    fn test_get_checker_association_order() {
        let got = get_checker_association_order(&[5, 10, 7, 2], &[true, false, false, true], true);
        assert_eq!(got, Some(vec![1, 2, 0, 3]));
        assert_eq!(get_checker_association_order(&[5], &[false], false), None);
    }

    /// `TestGetCheckerAssociationWeights`.
    #[test]
    fn test_get_checker_association_weights() {
        struct Case {
            name: &'static str,
            base_weights: &'static [i64],
            import_counts: &'static [i64],
            want: &'static [i64],
        }
        let tests = [
            Case {
                name: "normalizes import work to syntax work",
                base_weights: &[100, 50, 25],
                import_counts: &[0, 1, 3],
                want: &[100, 93, 154],
            },
            Case {
                name: "no imports preserves base weights",
                base_weights: &[100, 50, 25],
                import_counts: &[0, 0, 0],
                want: &[100, 50, 25],
            },
        ];
        for test in &tests {
            let got = get_checker_association_weights(test.base_weights, test.import_counts);
            assert_eq!(
                got.as_slice(),
                test.want,
                "{}: getCheckerAssociationWeights({:?}, {:?})",
                test.name,
                test.base_weights,
                test.import_counts
            );
        }
    }

    /// `TestGetCheckerAssociations`/`"empty"`.
    #[test]
    fn test_get_checker_associations_empty() {
        let got = get_checker_associations_in_order(
            &[],
            &[],
            None,
            4,
            CHECKER_ASSOCIATION_BALANCE_PENALTY_MULTIPLIER,
        );
        assert!(got.is_empty());
    }

    /// `TestGetCheckerAssociations`/`"balances disconnected files"`.
    #[test]
    fn test_get_checker_associations_balances_disconnected_files() {
        let got = get_checker_associations_in_order(
            &[1, 1, 1, 1, 1, 1],
            &[vec![], vec![], vec![], vec![], vec![], vec![]],
            None,
            3,
            1,
        );
        assert_eq!(got, vec![0, 1, 2, 0, 1, 2]);
    }

    /// `TestGetCheckerAssociations`/`"uses program order"`.
    #[test]
    fn test_get_checker_associations_uses_program_order() {
        let got =
            get_checker_associations_in_order(&[1, 3, 2], &[vec![], vec![], vec![]], None, 2, 1);
        assert_eq!(got, vec![0, 1, 0]);
    }

    /// `TestGetCheckerAssociations`/`"keeps dense components together"`.
    #[test]
    fn test_get_checker_associations_keeps_dense_components_together() {
        let adjacent: Vec<Vec<usize>> = vec![
            vec![1, 2],
            vec![0, 2],
            vec![0, 1],
            vec![4, 5],
            vec![3, 5],
            vec![3, 4],
        ];
        let got = get_checker_associations_in_order(&[1, 1, 1, 1, 1, 1], &adjacent, None, 2, 1);
        assert_eq!(got, vec![0, 0, 0, 1, 1, 1]);
    }

    /// `TestGetCheckerAssociations`/`"respects weighted balance cap"`.
    #[test]
    fn test_get_checker_associations_respects_weighted_balance_cap() {
        let weights: Vec<i64> = vec![8, 7, 6, 5, 4, 3, 2, 1];
        let adjacent: Vec<Vec<usize>> = vec![Vec::new(); weights.len()];
        let got = get_checker_associations_in_order(&weights, &adjacent, None, 3, 1);
        let mut loads = vec![0i64; 3];
        for (i, &checker_index) in got.iter().enumerate() {
            loads[checker_index as usize] += weights[i];
        }
        for (checker_index, load) in loads.iter().enumerate() {
            assert!(
                *load <= 13,
                "checker {} load = {}, want at most 13; associations = {:?}",
                checker_index,
                load,
                got
            );
        }
    }
}
