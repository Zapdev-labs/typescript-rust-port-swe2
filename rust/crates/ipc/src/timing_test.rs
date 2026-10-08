// Ported from tsc/internal/ipc/timing_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `time.Duration` literals become `Duration`s for `record`, or raw
// nanoseconds for `record_signed` (the negative-duration cases — Go
// `time.Duration` is signed). `t.Run` subtests become separate #[test] fns.

use std::time::Duration;

use crate::timing::{
    SERVER_RECENT_REQUEST_CAPACITY, duration_to_millis, new_timing_collector,
    server_timing_snapshot,
};

/// `TestTimingCollector/accumulates totals and records recent requests`
#[test]
fn timing_collector_accumulates() {
    let c = new_timing_collector();
    c.record("getSourceFile", Duration::from_millis(2));
    c.record("getSymbolAtPosition", Duration::from_micros(500));

    let snap = c.snapshot();
    assert!(snap.enabled);
    assert_eq!(snap.totals.request_count, 2);
    assert_eq!(snap.totals.total_processing_time_ms, 2.5);
    assert_eq!(snap.recent_requests.len(), 2);
    assert_eq!(snap.recent_requests[0].method, "getSourceFile");
    assert_eq!(snap.recent_requests[0].processing_time_ms, 2.0);
    assert_eq!(snap.recent_requests[1].method, "getSymbolAtPosition");
    assert_eq!(snap.recent_requests[1].processing_time_ms, 0.5);
}

/// `TestTimingCollector/ring buffer retains only the most recent requests`
#[test]
fn timing_collector_ring_buffer() {
    let c = new_timing_collector();
    let methods = ["a", "b", "c", "d", "e", "f", "g"];
    for m in methods {
        c.record(m, Duration::from_millis(1));
    }

    let snap = c.snapshot();
    assert_eq!(snap.totals.request_count, 7);
    assert_eq!(snap.recent_requests.len(), SERVER_RECENT_REQUEST_CAPACITY);

    // Expect the last 5 methods, oldest to newest.
    for (i, w) in methods[methods.len() - SERVER_RECENT_REQUEST_CAPACITY..]
        .iter()
        .enumerate()
    {
        assert_eq!(snap.recent_requests[i].method, *w);
    }
}

/// `TestTimingCollector/negative durations clamp to zero` — via
/// `record_signed` since `Duration` cannot be negative.
#[test]
fn timing_collector_negative_durations_clamp() {
    let c = new_timing_collector();
    c.record_signed("x", -5 * 1_000_000_000); // -5*time.Second
    let snap = c.snapshot();
    assert_eq!(snap.totals.total_processing_time_ms, 0.0);
    assert_eq!(snap.recent_requests[0].processing_time_ms, 0.0);
}

/// `TestServerTimingSnapshotDisabled`
#[test]
fn server_timing_snapshot_disabled() {
    let snap = server_timing_snapshot(None);
    assert!(!snap.enabled);
    assert_eq!(snap.totals.request_count, 0);
    assert_eq!(snap.recent_requests.len(), 0);
}

/// `TestTimingCollectorReset`
#[test]
fn timing_collector_reset() {
    let c = new_timing_collector();
    c.record("a", Duration::from_millis(1));
    c.record("b", Duration::from_millis(1));
    c.reset();

    let snap = c.snapshot();
    assert!(snap.enabled);
    assert_eq!(snap.totals.request_count, 0);
    assert_eq!(snap.totals.total_processing_time_ms, 0.0);
    assert_eq!(snap.recent_requests.len(), 0);

    // The collector remains usable after a reset.
    c.record("c", Duration::from_millis(2));
    let snap = c.snapshot();
    assert_eq!(snap.totals.request_count, 1);
    assert_eq!(snap.recent_requests[0].method, "c");
}

/// `TestDurationToMillis` — arguments are `time.Duration` nanoseconds.
#[test]
fn duration_to_millis_values() {
    assert_eq!(duration_to_millis(1_500_000), 1.5); // 1500*time.Microsecond
    assert_eq!(duration_to_millis(0), 0.0);
    assert_eq!(duration_to_millis(-5 * 1_000_000_000), 0.0);
    // Sub-microsecond durations retain precision rather than truncating to 0.
    assert_eq!(duration_to_millis(500), 0.0005);
    assert_eq!(duration_to_millis(1234), 0.001234);
}
