// Ported from tsc/internal/project/logging/logger.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::time::{SystemTime, UNIX_EPOCH};

/// `formatTime(t)` — `[15:04:05.000]` (HH:MM:SS.mmm).
///
/// PORT: Go formats in the local timezone; Rust std has no local-timezone
/// database access, so this renders the UTC wall clock instead. The
/// timestamp text is only consumed by logs/tests (the test logger pins a
/// fixed instant), so the offset is cosmetic.
pub(crate) fn format_time(t: SystemTime) -> String {
    let (secs, millis) = match t.duration_since(UNIX_EPOCH) {
        Ok(d) => (d.as_secs() as i64, d.subsec_millis() as i64),
        Err(e) => {
            // Pre-epoch instant: round toward -inf like Go's civil math.
            let d = e.duration();
            let mut secs = -(d.as_secs() as i64);
            let mut millis = -(d.subsec_millis() as i64);
            if millis != 0 {
                secs -= 1;
                millis += 1000;
            }
            (secs, millis)
        }
    };
    let day = secs.rem_euclid(86_400);
    let (h, m, s) = (day / 3600, (day % 3600) / 60, day % 60);
    format!("[{h:02}:{m:02}:{s:02}.{millis:03}]")
}
