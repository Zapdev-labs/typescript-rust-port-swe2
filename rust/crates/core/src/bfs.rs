// Ported from tsc/internal/core/bfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's goroutine-per-job + sync.WaitGroup becomes
// `std::thread::scope` with a scoped thread per job; workers return their
// child nodes via their JoinHandle instead of writing `next[i]` in place
// (equivalent — slots stay index-ordered). `*breadthFirstSearchJob` becomes
// an index into a `Vec<BreadthFirstSearchJob>` arena so the parent chain can
// be walked without shared pointers. Go's nil-able `[]N` path becomes
// `Option<Vec<N>>`; nil-able `*SyncSet`/`func` options become `Option`s.
// `atomic.Int64` minimum tracking is preserved via AtomicI64::fetch_min.

use std::sync::atomic::{AtomicI64, Ordering};
use std::thread;

use tsc_collections::{MapEntry, OrderedMap, SyncSet};

pub struct BreadthFirstSearchResult<N> {
    pub stopped: bool,
    /// PORT: Go's nil-able `[]N` — `None` == nil (no path).
    pub path: Option<Vec<N>>,
}

struct BreadthFirstSearchJob<N> {
    node: N,
    /// Index into the job arena; `None` for the start job.
    parent: Option<u32>,
}

pub struct BreadthFirstSearchLevel<'a, K, N> {
    jobs: &'a mut OrderedMap<K, u32>,
    arena: &'a [BreadthFirstSearchJob<N>],
}

impl<K: Eq + std::hash::Hash, N> BreadthFirstSearchLevel<'_, K, N> {
    pub fn has(&self, key: &K) -> bool {
        self.jobs.has(key)
    }

    pub fn delete(&mut self, key: &K) {
        self.jobs.delete(key);
    }

    // PORT: `Range(f func(node N) bool)` — f borrows each job's node; false
    // stops iteration.
    pub fn range(&self, mut f: impl FnMut(&N) -> bool) {
        for job in self.jobs.values() {
            if !f(&self.arena[*job as usize].node) {
                return;
            }
        }
    }
}

// PORT: `*collections.SyncSet` and `func(...)` fields become `Option`s.
pub struct BreadthFirstSearchOptions<'a, K, N> {
    /// Visited is a set of nodes that have already been visited.
    /// If nil, a new set will be created.
    pub visited: Option<&'a SyncSet<K>>,
    /// PreprocessLevel is a function that, if provided, will be called
    /// before each level, giving the caller an opportunity to remove nodes.
    #[allow(clippy::type_complexity)]
    pub preprocess_level: Option<&'a dyn Fn(&mut BreadthFirstSearchLevel<'_, K, N>)>,
}

impl<K, N> Default for BreadthFirstSearchOptions<'_, K, N> {
    fn default() -> Self {
        BreadthFirstSearchOptions {
            visited: None,
            preprocess_level: None,
        }
    }
}

// BreadthFirstSearchParallel performs a breadth-first search on a graph
// starting from the given node. It processes nodes in parallel and returns the path
// from the first node that satisfies the `visit` function back to the start node.
pub fn breadth_first_search_parallel<N>(
    start: N,
    neighbors: impl Fn(N) -> Vec<N> + Sync,
    visit: impl Fn(N) -> (bool, bool) + Sync,
) -> BreadthFirstSearchResult<N>
where
    N: Eq + std::hash::Hash + Clone + Send + Sync,
{
    breadth_first_search_parallel_ex(
        start,
        &neighbors,
        &visit,
        BreadthFirstSearchOptions::<N, N>::default(),
        &|n: &N| n.clone(),
    )
}

// PORT: Go's `result{stop, job, next}` struct becomes a tuple
// `(bool, Option<u32>, OrderedMap<K, u32>)` where the job is an arena index.

// BreadthFirstSearchParallelEx is an extension of BreadthFirstSearchParallel that allows
// the caller to pass a pre-seeded set of already-visited nodes and a preprocessing function
// that can be used to remove nodes from each level before parallel processing.
#[allow(clippy::too_many_arguments)]
pub fn breadth_first_search_parallel_ex<K, N>(
    start: N,
    neighbors: &(impl Fn(N) -> Vec<N> + Sync),
    visit: &(impl Fn(N) -> (bool, bool) + Sync),
    options: BreadthFirstSearchOptions<'_, K, N>,
    get_key: &(impl Fn(&N) -> K + Sync),
) -> BreadthFirstSearchResult<N>
where
    K: Eq + std::hash::Hash + Send + Sync,
    N: Clone + Send + Sync,
{
    let owned_visited;
    let visited = match options.visited {
        Some(v) => v,
        None => {
            owned_visited = SyncSet::new();
            &owned_visited
        }
    };

    // The job arena; `u32` indices replace Go's `*breadthFirstSearchJob`.
    let mut arena: Vec<BreadthFirstSearchJob<N>> = Vec::new();
    let mut fallback: Option<u32> = None;

    // processLevel processes each node at the current level in parallel.
    // It produces either a list of jobs to be processed in the next level,
    // or a result if the visit function returns true for any node.
    let process_level = |_index: usize,
                         jobs: &mut OrderedMap<K, u32>,
                         arena: &mut Vec<BreadthFirstSearchJob<N>>,
                         fallback: &mut Option<u32>| {
        let lowest_fallback = AtomicI64::new(i64::MAX);
        let lowest_goal = AtomicI64::new(i64::MAX);
        let next_job_count = AtomicI64::new(0);
        if let Some(preprocess_level) = options.preprocess_level {
            preprocess_level(&mut BreadthFirstSearchLevel { jobs, arena });
        }
        let job_ids: Vec<u32> = jobs.values().copied().collect();
        let fallback_is_none = fallback.is_none();
        let next: Vec<Vec<N>> = thread::scope(|s| {
            let mut handles = Vec::with_capacity(job_ids.len());
            for (i, &j) in job_ids.iter().enumerate() {
                let lowest_goal = &lowest_goal;
                let lowest_fallback = &lowest_fallback;
                let next_job_count = &next_job_count;
                let arena = &*arena;
                handles.push(s.spawn(move || {
                    if i as i64 >= lowest_goal.load(Ordering::Relaxed) {
                        return Vec::new(); // Stop processing if we already found a lower result
                    }

                    // If we have already visited this node, skip it.
                    if !visited.add_if_absent(get_key(&arena[j as usize].node)) {
                        // Note that if we are here, we already visited this node at a
                        // previous *level*, which means `visit` must have returned false,
                        // so we don't need to update our result indices. This holds true
                        // because we deduplicated jobs before queuing the level.
                        return Vec::new();
                    }

                    let (is_result, stop) = visit(arena[j as usize].node.clone());
                    if is_result {
                        // We found a result, so we will stop at this level, but an
                        // earlier job may still find a true result at a lower index.
                        if stop {
                            update_min(lowest_goal, i as i64);
                            return Vec::new();
                        }
                        if fallback_is_none {
                            update_min(lowest_fallback, i as i64);
                        }
                    }

                    if i as i64 >= lowest_goal.load(Ordering::Relaxed) {
                        // If `visit` is expensive, it's likely that by the time we get here,
                        // a different job has already found a lower index result, so we
                        // don't even need to collect the next jobs.
                        return Vec::new();
                    }
                    // Add the next level jobs
                    let neighbor_nodes = neighbors(arena[j as usize].node.clone());
                    next_job_count.fetch_add(neighbor_nodes.len() as i64, Ordering::Relaxed);
                    neighbor_nodes
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
                .collect()
        });
        if lowest_goal.load(Ordering::Relaxed) != i64::MAX {
            // If we found a result, return it immediately.
            let index = lowest_goal.load(Ordering::Relaxed) as usize;
            let (_, &job) = jobs.entry_at(index).unwrap();
            return (true, Some(job), OrderedMap::new());
        }
        if fallback.is_none() {
            let index = lowest_fallback.load(Ordering::Relaxed);
            if index != i64::MAX {
                let (_, &job) = jobs.entry_at(index as usize).unwrap();
                *fallback = Some(job);
            }
        }
        let mut next_jobs =
            OrderedMap::with_size_hint(next_job_count.load(Ordering::Relaxed) as usize);
        for (slot, children) in next.into_iter().enumerate() {
            for child in children {
                let key = get_key(&child);
                if !next_jobs.has(&key) {
                    // Deduplicate synchronously to avoid messy locks and spawning
                    // unnecessary goroutines.
                    let job_id = arena.len() as u32;
                    arena.push(BreadthFirstSearchJob {
                        node: child,
                        parent: Some(job_ids[slot]),
                    });
                    next_jobs.set(key, job_id);
                }
            }
        }
        (false, None, next_jobs)
    };

    let create_path = |job: Option<u32>, arena: &[BreadthFirstSearchJob<N>]| {
        let mut path = Vec::new();
        let mut job = Some(job?);
        while let Some(j) = job {
            let job_ref = &arena[j as usize];
            path.push(job_ref.node.clone());
            job = job_ref.parent;
        }
        Some(path)
    };

    let mut level_index = 0usize;
    arena.push(BreadthFirstSearchJob {
        node: start,
        parent: None,
    });
    let mut level = OrderedMap::from_list([MapEntry {
        key: get_key(&arena[0].node),
        value: 0,
    }]);
    while level.size() > 0 {
        let (stop, job, next) = process_level(level_index, &mut level, &mut arena, &mut fallback);
        if stop {
            return BreadthFirstSearchResult {
                stopped: true,
                path: create_path(job, &arena),
            };
        } else if job.is_some() && fallback.is_none() {
            fallback = job;
        }
        level = next;
        level_index += 1;
    }
    BreadthFirstSearchResult {
        stopped: false,
        path: create_path(fallback, &arena),
    }
}

// updateMin updates the atomic integer `a` to the candidate value if it is less than the current value.
fn update_min(a: &AtomicI64, candidate: i64) -> bool {
    // PORT: fetch_min returns the previous value; the atomic CAS loop in Go
    // collapses to a single fetch_min whose previous value > candidate iff the
    // update was applied.
    a.fetch_min(candidate, Ordering::Relaxed) > candidate
}

// Ported from tsc/internal/core/bfs_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
#[cfg(test)]
mod tests {
    use super::*;
    use rustc_hash::FxHashMap;
    use std::sync::Mutex;

    #[test]
    fn test_breadth_first_search_parallel() {
        // basic functionality

        // Test basic functionality with a simple DAG
        // Graph: A -> B, A -> C, B -> D, C -> D
        let graph: FxHashMap<&'static str, &'static [&'static str]> = FxHashMap::from_iter([
            ("A", &["B", "C"][..]),
            ("B", &["D"][..]),
            ("C", &["D"][..]),
            ("D", &[][..]),
        ]);

        let children = |node: &'static str| -> Vec<&'static str> { graph[node].to_vec() };

        // find specific node
        {
            let result = breadth_first_search_parallel("A", children, |node| (node == "D", true));
            assert!(result.stopped, "Expected search to stop at D");
            assert_eq!(result.path, Some(vec!["D", "B", "A"]));
        }

        // visit all nodes
        {
            let visited_nodes = Mutex::new(Vec::new());
            let result = breadth_first_search_parallel("A", children, |node| {
                visited_nodes.lock().unwrap().push(node);
                (false, false) // Never stop early
            });

            // Should return nil since we never return true
            assert!(!result.stopped, "Expected search to not stop early");
            assert!(
                result.path.is_none(),
                "Expected nil path when visit function never returns true"
            );

            // Should visit all nodes exactly once
            let mut visited_nodes = visited_nodes.into_inner().unwrap();
            visited_nodes.sort_unstable();
            assert_eq!(visited_nodes, ["A", "B", "C", "D"]);
        }
    }

    #[test]
    fn test_breadth_first_search_parallel_early_termination() {
        // Test that nodes below the target level are not visited
        let graph: FxHashMap<&'static str, &'static [&'static str]> = FxHashMap::from_iter([
            ("Root", &["L1A", "L1B"][..]),
            ("L1A", &["L2A", "L2B"][..]),
            ("L1B", &["L2C"][..]),
            ("L2A", &["L3A"][..]),
            ("L2B", &[][..]),
            ("L2C", &[][..]),
            ("L3A", &[][..]),
        ]);

        let children = |node: &'static str| -> Vec<&'static str> { graph[node].to_vec() };

        let visited = SyncSet::new();
        breadth_first_search_parallel_ex(
            "Root",
            &children,
            &|node| (node == "L2B", true), // Stop at level 2
            BreadthFirstSearchOptions {
                visited: Some(&visited),
                preprocess_level: None,
            },
            &|s: &&'static str| *s,
        );

        assert!(visited.has("Root"), "Expected to visit Root");
        assert!(visited.has("L1A"), "Expected to visit L1A");
        assert!(visited.has("L1B"), "Expected to visit L1B");
        assert!(visited.has("L2A"), "Expected to visit L2A");
        assert!(visited.has("L2B"), "Expected to visit L2B");
        // L2C is non-deterministic
        assert!(!visited.has("L3A"), "Expected not to visit L3A");
    }

    #[test]
    fn test_breadth_first_search_parallel_fallback() {
        // Test that fallback behavior works correctly
        let graph: FxHashMap<&'static str, &'static [&'static str]> = FxHashMap::from_iter([
            ("A", &["B", "C"][..]),
            ("B", &["D"][..]),
            ("C", &["D"][..]),
            ("D", &[][..]),
        ]);

        let children = |node: &'static str| -> Vec<&'static str> { graph[node].to_vec() };

        let visited = SyncSet::new();
        let result = breadth_first_search_parallel_ex(
            "A",
            &children,
            &|node| (node == "A", false), // Record A as a fallback, but do not stop
            BreadthFirstSearchOptions {
                visited: Some(&visited),
                preprocess_level: None,
            },
            &|s: &&'static str| *s,
        );

        assert!(!result.stopped, "Expected search to not stop early");
        assert_eq!(result.path, Some(vec!["A"]));
        assert!(visited.has("B"), "Expected to visit B");
        assert!(visited.has("C"), "Expected to visit C");
        assert!(visited.has("D"), "Expected to visit D");
    }

    #[test]
    fn test_breadth_first_search_parallel_stop_over_fallback() {
        // Test that a stop result is preferred over a fallback
        let graph: FxHashMap<&'static str, &'static [&'static str]> = FxHashMap::from_iter([
            ("A", &["B", "C"][..]),
            ("B", &["D"][..]),
            ("C", &["D"][..]),
            ("D", &[][..]),
        ]);

        let children = |node: &'static str| -> Vec<&'static str> { graph[node].to_vec() };

        let result = breadth_first_search_parallel("A", children, |node| match node {
            "A" => (true, false), // Record fallback
            "D" => (true, true),  // Stop at D
            _ => (false, false),
        });

        assert!(result.stopped, "Expected search to stop at D");
        assert_eq!(result.path, Some(vec!["D", "B", "A"]));
    }
}
