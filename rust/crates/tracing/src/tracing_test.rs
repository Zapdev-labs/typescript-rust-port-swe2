// Ported from tsc/internal/tracing/tracing_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `vfstest.FromMap`/`fstest.MapFS` map directly onto
// `tsc_vfs::vfstest::from_map`/`MapFile`; `json.Unmarshal` of the trace file
// back into `[]traceEvent` is `tsc_json::unmarshal::<Vec<TraceEvent>>`.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::SystemTime;

use serde_json::Value;
use tsc_tspath::{CaseSensitivity, RootedFilePath};
use tsc_vfs::Vfs;
use tsc_vfs::fs::{FileMode, MODE_DIR};
use tsc_vfs::vfstest::from_map;
use tsc_vfs::vfstest::fstest::MapFile;

use crate::tracing::*;

fn test_fs() -> Arc<dyn Vfs> {
    from_map(
        [(
            "/trace".to_string(),
            MapFile {
                data: Arc::from(&b""[..]),
                mode: MODE_DIR | FileMode(0o555),
                mod_time: SystemTime::UNIX_EPOCH,
                sys: None,
            },
        )],
        CaseSensitivity::CaseSensitive,
    )
}

#[test]
fn test_concurrent_duration_events_use_separate_thread_ids() {
    let fsys = test_fs();

    let tr = start_tracing(
        fsys.clone(),
        "/trace".into(),
        "",
        true, /* deterministic */
    )
    .unwrap();

    let end_a = tr.push(
        PHASE_PARSE,
        "createSourceFile",
        trace_args(&[("path", Value::from("/a.ts"))]),
        true,
    );
    let end_b = tr.push(
        PHASE_PARSE,
        "createSourceFile",
        trace_args(&[("path", Value::from("/b.ts"))]),
        true,
    );
    end_a();
    end_b();

    let end_check = tr.push(
        PHASE_CHECK,
        "checkSourceFile",
        trace_args(&[
            ("checkerId", Value::from(0)),
            ("path", Value::from("/a.ts")),
        ]),
        true,
    );
    let end_variance = tr.push(
        PHASE_CHECK_TYPES,
        "getVariancesWorker",
        trace_args(&[("checkerId", Value::from(0)), ("id", Value::from(1))]),
        true,
    );
    end_variance();
    end_check();

    tr.stop_tracing(|_| Ok(())).unwrap();

    let trace_text = fsys
        .read_file(&RootedFilePath::from("/trace/trace.json"))
        .expect("trace.json should exist");

    let events: Vec<TraceEvent> = tsc_json::unmarshal(trace_text.as_bytes(), &[]).unwrap();

    let a_begin = find_event(&events, "B", "createSourceFile", "path", "/a.ts");
    let a_end = find_event(&events, "E", "createSourceFile", "path", "/a.ts");
    let b_begin = find_event(&events, "B", "createSourceFile", "path", "/b.ts");
    let b_end = find_event(&events, "E", "createSourceFile", "path", "/b.ts");
    assert_eq!(a_begin.tid, a_end.tid);
    assert_eq!(b_begin.tid, b_end.tid);
    assert_ne!(a_begin.tid, b_begin.tid);
    assert_thread_name(&events, a_begin.tid, "file:/a.ts");
    assert_thread_name(&events, b_begin.tid, "file:/b.ts");

    let check_begin = find_event(&events, "B", "checkSourceFile", "path", "/a.ts");
    let variance_begin = find_event(&events, "B", "getVariancesWorker", "id", "1");
    assert_eq!(check_begin.tid, variance_begin.tid);
    assert_thread_name(&events, check_begin.tid, "checker:0");

    assert_duration_events_are_well_nested_by_thread(&events);
}

#[test]
fn test_thread_ids_are_stable_across_first_seen_order() {
    let first = trace_thread_ids_for_paths(&["/a.ts", "/b.ts"]);
    let second = trace_thread_ids_for_paths(&["/b.ts", "/a.ts"]);

    assert_eq!(first, second);
}

fn trace_thread_ids_for_paths(paths: &[&str]) -> HashMap<String, i64> {
    let fsys = test_fs();

    let tr = start_tracing(
        fsys.clone(),
        "/trace".into(),
        "",
        true, /* deterministic */
    )
    .unwrap();

    for path in paths {
        let end = tr.push(
            PHASE_PARSE,
            "createSourceFile",
            trace_args(&[("path", Value::from(*path))]),
            true,
        );
        end();
    }

    tr.stop_tracing(|_| Ok(())).unwrap();

    let trace_text = fsys
        .read_file(&RootedFilePath::from("/trace/trace.json"))
        .expect("trace.json should exist");

    let events: Vec<TraceEvent> = tsc_json::unmarshal(trace_text.as_bytes(), &[]).unwrap();

    let mut thread_ids = HashMap::new();
    for path in paths {
        thread_ids.insert(
            path.to_string(),
            find_event(&events, "B", "createSourceFile", "path", path).tid,
        );
    }
    thread_ids
}

fn find_event<'e>(
    events: &'e [TraceEvent],
    phase: &str,
    name: &str,
    arg_name: &str,
    arg_value: &str,
) -> &'e TraceEvent {
    for event in events {
        if event.ph == phase
            && event.name == name
            && event
                .args
                .get(arg_name)
                .is_some_and(|v| *v == Value::from(arg_value) || v.to_string() == arg_value)
        {
            return event;
        }
    }
    panic!("failed to find {phase} event {name:?} with {arg_name}={arg_value}");
}

fn assert_thread_name(events: &[TraceEvent], tid: i64, name: &str) {
    for event in events {
        if event.ph == "M"
            && event.name == "thread_name"
            && event.tid == tid
            && event.args.get("name") == Some(&Value::from(name))
        {
            return;
        }
    }
    panic!("failed to find thread_name metadata for thread {tid} named {name:?}");
}

fn assert_duration_events_are_well_nested_by_thread(events: &[TraceEvent]) {
    let mut stacks: HashMap<i64, Vec<&TraceEvent>> = HashMap::new();
    for event in events {
        match event.ph.as_str() {
            "B" => stacks.entry(event.tid).or_default().push(event),
            "E" => {
                let stack = stacks.entry(event.tid).or_default();
                assert!(
                    !stack.is_empty(),
                    "unmatched end event {:?} on thread {}",
                    event.name,
                    event.tid
                );
                let begin = stack.pop().unwrap();
                assert_eq!(begin.cat, event.cat);
                assert_eq!(begin.name, event.name);
            }
            _ => {}
        }
    }

    for (tid, stack) in &stacks {
        assert!(
            stack.is_empty(),
            "thread {tid} has {} unterminated events",
            stack.len()
        );
    }
}
