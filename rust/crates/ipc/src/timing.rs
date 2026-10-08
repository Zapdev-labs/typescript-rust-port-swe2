// Ported from tsc/internal/ipc/timing.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `time.Duration` is signed int64 nanoseconds in Go — `record` takes a
// std `Duration` for callers, while `record_signed`/`duration_to_millis`
// keep the raw-nanosecond form so the observable negative-duration clamp
// (`durationToMillis(d) → 0` for `d < 0`) survives the port.

use std::sync::Mutex;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use serde::Serialize;

/// `MethodGetServerTiming` — handled by the connection itself, not the
/// handler, when timing collection is enabled.
pub const METHOD_GET_SERVER_TIMING: &str = "getServerTiming";
/// `MethodResetServerTiming`
pub const METHOD_RESET_SERVER_TIMING: &str = "resetServerTiming";

/// `serverRecentRequestCapacity` — ring-buffer size for recent requests.
pub(crate) const SERVER_RECENT_REQUEST_CAPACITY: usize = 5;

/// `serverRequestTiming` — a single server-side request's processing-time
/// sample.
#[derive(Clone, Debug, Default, Serialize)]
pub(crate) struct ServerRequestTiming {
    /// `Method string json:"method"`
    #[serde(rename = "method")]
    pub method: String,
    /// `ProcessingTimeMs float64 json:"processingTimeMs"`
    #[serde(rename = "processingTimeMs")]
    pub processing_time_ms: f64,
    /// `Timestamp int64 json:"timestamp"` — Unix time in milliseconds when
    /// the request completed.
    #[serde(rename = "timestamp")]
    pub timestamp: i64,
}

/// `serverTimingTotals` — running totals accumulated across every handled
/// request.
#[derive(Clone, Copy, Debug, Default, Serialize)]
pub(crate) struct ServerTimingTotals {
    /// `RequestCount uint64 json:"requestCount"`
    #[serde(rename = "requestCount")]
    pub request_count: u64,
    /// `TotalProcessingTimeMs float64 json:"totalProcessingTimeMs"`
    #[serde(rename = "totalProcessingTimeMs")]
    pub total_processing_time_ms: f64,
}

/// `serverTimingInfo` — a point-in-time snapshot of collected server timing,
/// returned to clients in response to a `getServerTiming` request.
#[derive(Clone, Debug, Default, Serialize)]
pub(crate) struct ServerTimingInfo {
    /// `Enabled bool json:"enabled"`
    #[serde(rename = "enabled")]
    pub enabled: bool,
    /// `Totals serverTimingTotals json:"totals"`
    #[serde(rename = "totals")]
    pub totals: ServerTimingTotals,
    /// `RecentRequests []serverRequestTiming json:"recentRequests"` — most
    /// recent requests, oldest to newest, up to `SERVER_RECENT_REQUEST_CAPACITY`.
    #[serde(rename = "recentRequests")]
    pub recent_requests: Vec<ServerRequestTiming>,
}

/// `timingCollector` — accumulates per-request server processing times into
/// running totals and a fixed-size ring buffer of the most recent requests.
/// Safe for concurrent use so the async connection can record from multiple
/// request threads.
pub(crate) struct TimingCollector {
    /// `mu sync.Mutex` guarding `totals`, `ring`, `head`.
    inner: Mutex<TimingInner>,
}

#[derive(Default)]
struct TimingInner {
    totals: ServerTimingTotals,
    /// `ring` holds up to `SERVER_RECENT_REQUEST_CAPACITY` entries; once
    /// full, `head` marks the oldest entry.
    ring: Vec<ServerRequestTiming>,
    head: usize,
}

/// `newTimingCollector`
pub(crate) fn new_timing_collector() -> TimingCollector {
    TimingCollector {
        inner: Mutex::new(TimingInner::default()),
    }
}

impl TimingCollector {
    /// `record(method, d)` — adds a single request's processing time to the
    /// totals and ring buffer.
    pub(crate) fn record(&self, method: &str, d: Duration) {
        self.record_signed(method, duration_nanos(d));
    }

    /// `record` with a raw signed-nanosecond duration — Go's `time.Duration`
    /// is `int64`, and a negative value must clamp to zero via
    /// [`duration_to_millis`]. Kept crate-visible for the ported tests.
    pub(crate) fn record_signed(&self, method: &str, d_ns: i64) {
        let processing_ms = duration_to_millis(d_ns);

        let mut inner = self.inner.lock().unwrap();

        inner.totals.request_count += 1;
        inner.totals.total_processing_time_ms += processing_ms;

        let entry = ServerRequestTiming {
            method: method.to_string(),
            processing_time_ms: processing_ms,
            // `time.Now().UnixMilli()`
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as i64,
        };
        if inner.ring.len() < SERVER_RECENT_REQUEST_CAPACITY {
            inner.ring.push(entry);
        } else {
            let head = inner.head;
            inner.ring[head] = entry;
            inner.head = (head + 1) % SERVER_RECENT_REQUEST_CAPACITY;
        }
    }

    /// `snapshot()` — a copy of the currently collected timing, with recent
    /// requests ordered oldest to newest.
    pub(crate) fn snapshot(&self) -> ServerTimingInfo {
        let inner = self.inner.lock().unwrap();

        let mut recent = Vec::with_capacity(inner.ring.len());
        for i in 0..inner.ring.len() {
            recent.push(inner.ring[(inner.head + i) % inner.ring.len()].clone());
        }
        ServerTimingInfo {
            enabled: true,
            totals: inner.totals,
            recent_requests: recent,
        }
    }

    /// `reset()` — clears all accumulated totals and recent-request history.
    pub(crate) fn reset(&self) {
        let mut inner = self.inner.lock().unwrap();
        inner.totals = ServerTimingTotals::default();
        inner.ring.clear();
        inner.head = 0;
    }
}

/// `serverTimingSnapshot(c)` — the collector's snapshot, or a disabled
/// snapshot when timing collection is not enabled (`None`, Go's nil).
pub(crate) fn server_timing_snapshot(c: Option<&TimingCollector>) -> ServerTimingInfo {
    match c {
        None => disabled_server_timing_info(),
        Some(c) => c.snapshot(),
    }
}

/// `disabledServerTimingInfo` — the snapshot returned when timing collection
/// is not enabled.
pub(crate) fn disabled_server_timing_info() -> ServerTimingInfo {
    ServerTimingInfo {
        enabled: false,
        recent_requests: Vec::new(),
        ..Default::default()
    }
}

/// `durationToMillis` — fractional milliseconds, clamped non-negative,
/// preserving sub-microsecond precision from the full nanosecond duration.
/// `d_ns` is a `time.Duration` (int64 nanoseconds).
pub(crate) fn duration_to_millis(d_ns: i64) -> f64 {
    if d_ns < 0 {
        return 0.0;
    }
    // `float64(d) / float64(time.Millisecond)`
    d_ns as f64 / 1e6
}

/// Saturating `Duration` → `time.Duration` nanoseconds for
/// [`TimingCollector::record`].
pub(crate) fn duration_nanos(d: Duration) -> i64 {
    d.as_nanos().min(i64::MAX as u128) as i64
}
