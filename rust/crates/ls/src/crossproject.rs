// Ported from tsc/internal/ls/crossproject.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(location): the bulk of crossproject.go was ported into
// `findallreferences.rs`, where all of its callers live (Go's package-level
// declarations are shared by every file in package `ls`):
//
//   - `Project`                        → `crate::findallreferences::Project`
//   - `CrossProjectOrchestrator`       → `crate::findallreferences::CrossProjectOrchestrator`
//   - `projectAndTextDocumentPosition` → inlined into `handle_cross_project`'s
//                                        FIFO work queue (a tuple, since each
//                                        item is processed synchronously)
//   - `response[Resp]`                 → `crate::findallreferences::CrossProjectResponse`
//   - `handleCrossProject`             → `LanguageService::handle_cross_project`
//   - `combineLocationArray`           → `crate::findallreferences::combine_location_array`
//                                        (+ `combine_location_link_array` for
//                                        `LocationLink`'s `{targetUri,targetRange}`
//                                        dedup key)
//   - `combineResponseLocations`       → `crate::findallreferences::combine_response_locations`
//   - `combineReferences`              → `crate::findallreferences::combine_references`
//   - `combineVSReferences`            → `crate::findallreferences::combine_vsreferences`
//   - `combineImplementations`         → `crate::findallreferences::combine_implementations`
//   - `combineRenameResponse`          → `crate::findallreferences::combine_rename_response`
//
// Two Go behaviors are adapted in `handle_cross_project`:
//   - `core.NewWorkGroup(false)` (parallel goroutines) becomes a sequential
//     FIFO queue: queued work captures `Rc<Program>`/`&LanguageService` state
//     that is neither `Send` nor `'static`, so it cannot be moved into the
//     `Send + 'static` closures `WorkGroup::queue` requires. Result ordering
//     is unaffected — `getResultsIterator` re-orders responses before
//     combining — and each project is still searched exactly once thanks to
//     the `LoadOrStore`-style dedupe on project id.
//   - The per-worker `recover()`/`panicsOccurred` repanic is dropped with
//     parallelism; a panic in synchronous processing simply propagates.
//
// `combineIncomingCalls` is ported below (its only Go caller,
// `getIncomingCalls` in callhierarchy.go, is still a skeleton).

use tsc_lsproto::{self as lsproto};

/// `combineIncomingCalls` — union of per-project incoming-call lists, deduped
/// by the caller location (`call.From.GetLocation()`).
///
/// PORT: `seenCalls` is a `Vec` scanned linearly because `lsproto::Location`
/// is `PartialEq` but not `Hash` (same adaptation as
/// `combine_location_array`). `#[allow(dead_code)]` until
/// `callhierarchy.rs`'s `get_incoming_calls` is ported.
#[allow(dead_code)]
pub(crate) fn combine_incoming_calls(
    results: Vec<lsproto::CallHierarchyIncomingCallsResponse>,
) -> lsproto::CallHierarchyIncomingCallsResponse {
    let mut combined: Vec<lsproto::CallHierarchyIncomingCall> = Vec::new();
    let mut seen_calls: Vec<lsproto::Location> = Vec::new();
    for resp in results {
        if let Some(calls) = &resp.call_hierarchy_incoming_calls {
            for call in calls {
                if let Some(from) = &call.from {
                    let location = from.get_location();
                    if !seen_calls.contains(&location) {
                        seen_calls.push(location);
                        combined.push(call.clone());
                    }
                }
            }
        }
    }
    lsproto::CallHierarchyIncomingCallsOrNull {
        call_hierarchy_incoming_calls: Some(combined),
    }
}
