// Ported from tsc/internal/tracing/tracing.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `map[string]any` event args are `TraceArgs` (`BTreeMap<String,
//   serde_json::Value>`). Go marshals events with
//   `json.Deterministic(true)`, which sorts *map* keys only — struct fields
//   keep declaration order. Plain `marshal_write` reproduces that exactly:
//   serde derives fields in declaration order and `BTreeMap` sorts arg keys.
//   The facade's `deterministic(true)` option must NOT be used here — it
//   routes through `serde_json::Value`, sorting the struct fields too.
// - Go `float64` `ts`/`dur` are marshaled per ECMAScript `Number::toString`
//   (integral floats print as "1"); `serialize_ecma_f64` folds integral
//   finite values to integers — the delta the `tsc-json` facade documents
//   for bare serde_json floats.
// - `*ast.Node` is `NodeId` and `*ast.Symbol` is `SymbolId`; both are
//   arena-relative. Go's `DumpTypes()`/`getLocation` reach the checker's
//   arenas through pointers, so `dump_types`/`build_type_descriptor` take
//   `nodes: &[Node]`/`symbols: &SymbolArena` and `stop_tracing` takes a `dump`
//   callback supplying them (Go's `StopTracing` calls `tracer.DumpTypes()`
//   with no arguments).
// - `TracedType.RecursionIdentity() any` (a `map[any]int` key in Go) becomes
//   the hashable `RecursionIdentity` enum.
// - `xxh3.New().WriteString(...).Sum64()` is `xxh3::xxh3_64` — the standard
//   XXH3-64 implemented in `xxh3.rs` (no dependency).

use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use tsc_ast::symbol::escape_all_internal_symbol_names;
use tsc_ast::utilities::get_source_file_of_node;
use tsc_ast::{Node, NodeId, SymbolArena, SymbolId};
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

use crate::xxh3::xxh3_64;

/// `Tracer` is an interface for recording types during type checking.
/// Each checker should have its own `Tracer` instance to avoid sharing types
/// between checkers.
///
/// PORT: no `Send + Sync` — the checker's type arena is `Rc<RefCell<..>>`
/// (Go's checker is single-threaded), so recorded types are `Rc` handles.
pub trait Tracer {
    /// `RecordType` records a type for later dumping.
    fn record_type(&self, t: Rc<dyn TracedType>);
    /// `DumpTypes` writes all recorded types to disk. `nodes`/`symbols` are
    /// the checker's arenas — Go's `*ast.Node`/`*ast.Symbol` pointers carry
    /// their arena implicitly.
    fn dump_types(&self, nodes: &[Node], symbols: &SymbolArena) -> Result<(), Error>;
}

/// `TracedType` is an interface that represents a type that can be traced.
/// This allows the tracing package to work with types from the checker
/// package without creating a circular dependency.
///
/// Go's `TracedType` accessor results are interface values (nil-able), so
/// type-returning accessors are `Option<Rc<dyn TracedType>>`. `*ast.Node`
/// results are `Option<NodeId>` into the `nodes` arena passed to
/// `dump_types`; `*ast.Symbol` results are `Option<SymbolId>` into `symbols`.
///
/// PORT: no `Send + Sync` — recorded types hold `Rc` arena handles
/// (single-threaded checker, like Go).
pub trait TracedType {
    /// `Id()`.
    fn id(&self) -> u32;
    /// `FormatFlags()`.
    fn format_flags(&self) -> Vec<String>;
    /// `IsConditional()`.
    fn is_conditional(&self) -> bool;
    /// `Symbol()`.
    fn symbol(&self) -> Option<SymbolId>;
    /// `AliasSymbol()`.
    fn alias_symbol(&self) -> Option<SymbolId>;
    /// `AliasTypeArguments()` — elements are nil-able in Go.
    fn alias_type_arguments(&self) -> Vec<Option<Rc<dyn TracedType>>>;

    // Type-specific data accessors
    /// `IntrinsicName()`.
    fn intrinsic_name(&self) -> String;
    /// `UnionTypes()`.
    fn union_types(&self) -> Vec<Option<Rc<dyn TracedType>>>;
    /// `IntersectionTypes()`.
    fn intersection_types(&self) -> Vec<Option<Rc<dyn TracedType>>>;
    /// `IndexType()`.
    fn index_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `IndexedAccessObjectType()`.
    fn indexed_access_object_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `IndexedAccessIndexType()`.
    fn indexed_access_index_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `ConditionalCheckType()`.
    fn conditional_check_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `ConditionalExtendsType()`.
    fn conditional_extends_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `ConditionalTrueType()`.
    fn conditional_true_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `ConditionalFalseType()`.
    fn conditional_false_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `SubstitutionBaseType()`.
    fn substitution_base_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `SubstitutionConstraintType()`.
    fn substitution_constraint_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `ReferenceTarget()`.
    fn reference_target(&self) -> Option<Rc<dyn TracedType>>;
    /// `ReferenceTypeArguments()`.
    fn reference_type_arguments(&self) -> Vec<Option<Rc<dyn TracedType>>>;
    /// `ReferenceNode()` — a `NodeId` in `nodes`.
    fn reference_node(&self) -> Option<NodeId>;
    /// `ReverseMappedSourceType()`.
    fn reverse_mapped_source_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `ReverseMappedMappedType()`.
    fn reverse_mapped_mapped_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `ReverseMappedConstraintType()`.
    fn reverse_mapped_constraint_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `EvolvingArrayElementType()`.
    fn evolving_array_element_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `EvolvingArrayFinalType()`.
    fn evolving_array_final_type(&self) -> Option<Rc<dyn TracedType>>;
    /// `IsTuple()`.
    fn is_tuple(&self) -> bool;
    /// `Pattern()` — a `NodeId` in `nodes`.
    fn pattern(&self) -> Option<NodeId>;
    /// `RecursionIdentity()` — Go's `any` map key.
    fn recursion_identity(&self) -> Option<RecursionIdentity>;

    /// `Display()` is an optional string representation of the type.
    fn display(&self) -> String;
}

/// `RecursionIdentity() any` — Go uses the value as a `map[any]int` key;
/// implementors return any hashable token. `Object` covers Go's pointer/
/// object identities (e.g. an index or address); `Text` covers Go's string
/// identities (e.g. "emptyObject").
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum RecursionIdentity {
    Object(u64),
    Text(String),
}

/// `TraceRecord` represents metadata about a single trace file.
///
/// `omitzero` on the path fields becomes `skip_serializing_if` on empty
/// strings; `checkerId` is always emitted.
#[derive(Clone, Serialize, Deserialize)]
pub struct TraceRecord {
    #[serde(rename = "configFilePath", skip_serializing_if = "String::is_empty")]
    pub config_file_path: String,
    #[serde(rename = "tracePath", skip_serializing_if = "String::is_empty")]
    pub trace_path: String,
    #[serde(rename = "typesPath", skip_serializing_if = "String::is_empty")]
    pub types_path: String,
    #[serde(rename = "checkerId")]
    pub checker_id: i64,
}

/// `map[string]any` — JSON object member order is the Go map iteration order
/// made deterministic: `json.Deterministic(true)` sorts keys, and `BTreeMap`
/// gives serde_json the same order.
pub type TraceArgs = BTreeMap<String, serde_json::Value>;

/// `traceEvent` — the field order and `,omitzero` elision mirror the Go
/// struct's `encoding/json` tags exactly (empty `name`/`s`/`args`, nil `dur`
/// are omitted).
#[derive(Clone, Serialize, Deserialize)]
pub struct TraceEvent {
    pub pid: i64,
    pub tid: i64,
    pub ph: String,
    pub cat: String,
    #[serde(serialize_with = "serialize_ecma_f64")]
    pub ts: f64,
    #[serde(skip_serializing_if = "String::is_empty", default)]
    pub name: String,
    /// scope — only set for instant events ("g" = global)
    #[serde(skip_serializing_if = "String::is_empty", default)]
    pub s: String,
    #[serde(
        skip_serializing_if = "Option::is_none",
        serialize_with = "serialize_opt_ecma_f64",
        default
    )]
    pub dur: Option<f64>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty", default)]
    pub args: TraceArgs,
}

/// Go's `encoding/json`/jsontext writes `float64` per ECMAScript
/// `Number::toString` — integral floats print without a fraction ("1", not
/// "1.0"). serde_json's ryu always prints "1.0", so integral finite values
/// within the safe-integer range are folded to integers here.
fn serialize_ecma_f64<S: serde::Serializer>(v: &f64, s: S) -> Result<S::Ok, S::Error> {
    const MAX_SAFE_INT_F64: f64 = 9_007_199_254_740_992.0; // 2^53
    if v.is_finite() && v.fract() == 0.0 && v.abs() < MAX_SAFE_INT_F64 {
        return s.serialize_i64(*v as i64);
    }
    s.serialize_f64(*v)
}

fn serialize_opt_ecma_f64<S: serde::Serializer>(v: &Option<f64>, s: S) -> Result<S::Ok, S::Error> {
    match v {
        Some(v) => serialize_ecma_f64(v, s),
        None => s.serialize_none(),
    }
}

/// `sampleInterval` matches TypeScript's 10ms sampling interval.
/// Events with `separate_begin_and_end=false` are only recorded if their
/// duration crosses a 10ms sampling boundary.
pub const SAMPLE_INTERVAL: Duration = Duration::from_millis(10);

/// `traceFileName`
pub const TRACE_FILE_NAME: &str = "trace.json";

pub const MAIN_THREAD_ID: i64 = 1;
pub const FIRST_SYNTHETIC_THREAD_ID: i64 = 2;
pub const FIRST_FILE_THREAD_ID: i64 = 1_000_000;
pub const FILE_THREAD_ID_HASH_RANGE: i64 = 1_000_000_000;

/// `var traceThreadArgKeys`
pub const TRACE_THREAD_ARG_KEYS: [&str; 5] = [
    "path",
    "fileName",
    "containingFileName",
    "jsFilePath",
    "declarationFilePath",
];

/// `flushThreshold` is the size at which buffered trace content is flushed to
/// disk via `AppendFile`. Keeps peak memory bounded for long-running
/// compilations while avoiding a syscall per event.
pub const FLUSH_THRESHOLD: usize = 256 * 1024;

/// `error` — Go wraps failures in `fmt.Errorf("failed to ...: %w", err)`;
/// callers only test `err != nil` and print, so the context text is carried
/// directly.
#[derive(Debug)]
pub struct Error(pub String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

/// `Tracing` manages the overall tracing session including all checkers.
pub struct Tracing {
    fs: Arc<dyn Vfs>,
    trace_dir: RootedDirectoryPath,
    trace_path: RootedFilePath,
    config_file_path: String,
    /// `traceStarted atomic.Bool` — checked outside `mu` on the fast path.
    trace_started: AtomicBool,
    deterministic: bool, // when true, use monotonic counter instead of real time
    start_time: Instant,
    /// `mu sync.Mutex` guards everything below (`TracingInner`).
    inner: Mutex<TracingInner>,
}

impl Default for Tracing {
    /// Go's `new(tracing.Tracing)` / `&Tracing{}` — an inert instance whose
    /// `trace_started` flag is false, so every recording method is a no-op.
    /// Used by tests that only need a comparable `*Tracing` identity.
    fn default() -> Self {
        Tracing {
            fs: tsc_vfs::vfstest::from_map(
                std::iter::empty::<(String, String)>(),
                CaseSensitivity::CaseSensitive,
            ),
            trace_dir: RootedDirectoryPath::default(),
            trace_path: RootedFilePath::default(),
            config_file_path: String::new(),
            trace_started: AtomicBool::new(false),
            deterministic: false,
            start_time: Instant::now(),
            inner: Mutex::new(TracingInner {
                legend: Vec::new(),
                tracers: Vec::new(),
                trace_content: Vec::new(),
                thread_ids: HashMap::new(),
                thread_keys: HashMap::new(),
                metadata_ts: 0.0,
                timestamp_counter: 0,
                flush_err: None,
            }),
        }
    }
}

struct TracingInner {
    legend: Vec<TraceRecord>,
    tracers: Vec<Arc<TypeTracer>>,
    /// `traceContent strings.Builder` — buffered output bytes.
    trace_content: Vec<u8>,
    thread_ids: HashMap<TraceThreadKey, i64>,
    thread_keys: HashMap<i64, TraceThreadKey>,
    metadata_ts: f64,
    timestamp_counter: u64, // only used in deterministic mode
    /// `flushErr` holds the first error encountered while appending the trace
    /// buffer to disk. Once set, subsequent flushes become no-ops and the
    /// error is surfaced from `stop_tracing` so that transient I/O failures
    /// (disk full, permission denied, etc.) don't crash the compiler.
    flush_err: Option<Error>,
}

/// `Phase` represents a tracing phase (`type Phase string`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Phase(pub &'static str);

pub const PHASE_PARSE: Phase = Phase("parse");
pub const PHASE_PROGRAM: Phase = Phase("program");
pub const PHASE_BIND: Phase = Phase("bind");
pub const PHASE_CHECK: Phase = Phase("check");
pub const PHASE_CHECK_TYPES: Phase = Phase("checkTypes");
pub const PHASE_EMIT: Phase = Phase("emit");
pub const PHASE_SESSION: Phase = Phase("session");

/// `StartTracing` creates a new tracing session.
/// When `deterministic` is true, timestamps use a monotonic counter instead
/// of real wall-clock time, producing stable output for test baselines.
pub fn start_tracing(
    fs: Arc<dyn Vfs>,
    trace_dir: RootedDirectoryPath,
    config_file_path: &str,
    deterministic: bool,
) -> Result<Arc<Tracing>, Error> {
    let tr = Arc::new(Tracing {
        fs,
        trace_path: trace_dir.resolve_file(TRACE_FILE_NAME),
        trace_dir,
        config_file_path: config_file_path.to_string(),
        trace_started: AtomicBool::new(true),
        deterministic,
        start_time: Instant::now(),
        inner: Mutex::new(TracingInner {
            legend: Vec::new(),
            tracers: Vec::new(),
            trace_content: Vec::new(),
            thread_ids: HashMap::new(),
            thread_keys: HashMap::new(),
            metadata_ts: 0.0,
            timestamp_counter: 0,
            flush_err: None,
        }),
    });

    // Write the trace file header with metadata events
    let mut inner = tr.inner.lock().unwrap();
    inner.trace_content.extend_from_slice(b"[\n");

    // Write metadata events (matching TypeScript's format)
    let meta_ts = tr.timestamp(&mut inner);
    inner.metadata_ts = meta_ts;
    tr.write_event(
        &mut inner,
        &TraceEvent {
            pid: 1,
            tid: MAIN_THREAD_ID,
            ph: "M".to_string(),
            cat: "__metadata".to_string(),
            ts: meta_ts,
            name: "process_name".to_string(),
            s: String::new(),
            dur: None,
            args: trace_args(&[("name", serde_json::Value::from("tsgo"))]),
        },
    );
    inner.trace_content.extend_from_slice(b",\n");
    tr.write_event(
        &mut inner,
        &TraceEvent {
            pid: 1,
            tid: MAIN_THREAD_ID,
            ph: "M".to_string(),
            cat: "__metadata".to_string(),
            ts: meta_ts,
            name: "thread_name".to_string(),
            s: String::new(),
            dur: None,
            args: trace_args(&[("name", serde_json::Value::from("Main"))]),
        },
    );
    inner.trace_content.extend_from_slice(b",\n");
    tr.write_event(
        &mut inner,
        &TraceEvent {
            pid: 1,
            tid: MAIN_THREAD_ID,
            ph: "M".to_string(),
            cat: "disabled-by-default-devtools.timeline".to_string(),
            ts: meta_ts,
            name: "TracingStartedInBrowser".to_string(),
            s: String::new(),
            dur: None,
            args: TraceArgs::new(),
        },
    );

    // Truncate any existing trace file with the header so subsequent
    // `append_file` calls extend a clean file.
    if let Err(err) = tr
        .fs
        .write_file(&tr.trace_path, trace_content_str(&inner.trace_content))
    {
        return Err(Error(format!("failed to write trace file header: {err}")));
    }
    inner.trace_content.clear();
    drop(inner);

    Ok(tr)
}

/// `map[string]any{...}` — a `TraceArgs` literal.
pub fn trace_args(pairs: &[(&str, serde_json::Value)]) -> TraceArgs {
    pairs
        .iter()
        .map(|(k, v)| (k.to_string(), v.clone()))
        .collect()
}

/// `trace_content` is always valid UTF-8 (JSON + ",\n" separators).
fn trace_content_str(content: &[u8]) -> &str {
    std::str::from_utf8(content).expect("trace content is JSON")
}

impl Tracing {
    /// `tr.timestamp()` returns the current timestamp in microseconds.
    /// In deterministic mode it returns a monotonically increasing counter;
    /// otherwise it returns the real elapsed wall-clock time since tracing
    /// started, matching TypeScript's `1000 * timestamp()` (microseconds).
    fn timestamp(&self, inner: &mut TracingInner) -> f64 {
        if self.deterministic {
            inner.timestamp_counter += 1;
            return inner.timestamp_counter as f64;
        }
        self.start_time.elapsed().as_nanos() as f64 / 1000.0
    }

    fn write_event(&self, inner: &mut TracingInner, event: &TraceEvent) {
        write_event_to(&mut inner.trace_content, event);
    }

    /// `maybeFlushLocked` appends the buffered trace content to disk if it
    /// has grown past the flush threshold. Caller must hold `inner`. If a
    /// previous flush failed, or this flush fails, the error is recorded in
    /// `flush_err` and subsequent writes become no-ops; the error is
    /// surfaced from `stop_tracing`.
    fn maybe_flush_locked(&self, inner: &mut TracingInner) {
        if inner.flush_err.is_some() {
            inner.trace_content.clear();
            return;
        }
        if inner.trace_content.len() < FLUSH_THRESHOLD {
            return;
        }
        if let Err(err) = self
            .fs
            .append_file(&self.trace_path, trace_content_str(&inner.trace_content))
        {
            inner.flush_err = Some(Error(format!("failed to flush trace file: {err}")));
        }
        inner.trace_content.clear();
    }

    /// `Instant` records an instant event in the trace.
    /// Safe to call on nil receiver — see `instant`.
    pub fn instant(&self, phase: Phase, name: &str, args: TraceArgs) {
        if !self.trace_started.load(Ordering::SeqCst) {
            return;
        }

        let mut inner = self.inner.lock().unwrap();

        // Re-check under the lock: `stop_tracing` may have run between the
        // load above and acquiring the lock. Once stopped, further writes
        // would land in a buffer that has already been flushed and the
        // closing "]" written.
        if !self.trace_started.load(Ordering::SeqCst) {
            return;
        }

        let ts = self.timestamp(&mut inner);
        let tid = thread_id_locked(self, &mut inner, &args);
        inner.trace_content.extend_from_slice(b",\n");
        self.write_event(
            &mut inner,
            &TraceEvent {
                pid: 1,
                tid,
                ph: "I".to_string(),
                cat: phase.0.to_string(),
                ts,
                name: name.to_string(),
                s: "g".to_string(),
                dur: None,
                args,
            },
        );
        self.maybe_flush_locked(&mut inner);
    }

    /// `Push` starts a trace event block on the shared trace buffer.
    /// Safe to call from multiple threads.
    ///
    /// When `separate_begin_and_end` is true, a "B" (begin) event is written
    /// immediately and the returned function writes a matching "E" (end)
    /// event. This is used for events that must always appear in the trace
    /// (e.g. `checkSourceFile`, `createProgram`, `emit`).
    ///
    /// When `separate_begin_and_end` is false (the default in TypeScript),
    /// the event is only recorded if its duration crosses a 10ms sampling
    /// boundary, matching TypeScript's behavior of sampling short-lived
    /// events to avoid trace bloat.
    ///
    /// Returns a function that should be called (typically deferred) to end
    /// the event. Each returned function is self-contained and does not
    /// depend on a shared stack.
    pub fn push(
        self: &Arc<Tracing>,
        phase: Phase,
        name: &str,
        args: TraceArgs,
        separate_begin_and_end: bool,
    ) -> Box<dyn FnOnce()> {
        if !self.trace_started.load(Ordering::SeqCst) {
            return Box::new(|| {});
        }

        if separate_begin_and_end {
            let (tid, ts);
            {
                let mut inner = self.inner.lock().unwrap();
                if !self.trace_started.load(Ordering::SeqCst) {
                    return Box::new(|| {});
                }
                ts = self.timestamp(&mut inner);
                tid = thread_id_locked(self, &mut inner, &args);
                inner.trace_content.extend_from_slice(b",\n");
                self.write_event(
                    &mut inner,
                    &TraceEvent {
                        pid: 1,
                        tid,
                        ph: "B".to_string(),
                        cat: phase.0.to_string(),
                        ts,
                        name: name.to_string(),
                        s: String::new(),
                        dur: None,
                        args: args.clone(),
                    },
                );
                self.maybe_flush_locked(&mut inner);
            }

            let tr = self.clone();
            let name = name.to_string();
            return Box::new(move || {
                let mut inner = tr.inner.lock().unwrap();
                if !tr.trace_started.load(Ordering::SeqCst) {
                    return;
                }
                let end_ts = tr.timestamp(&mut inner);
                inner.trace_content.extend_from_slice(b",\n");
                tr.write_event(
                    &mut inner,
                    &TraceEvent {
                        pid: 1,
                        tid,
                        ph: "E".to_string(),
                        cat: phase.0.to_string(),
                        ts: end_ts,
                        name,
                        s: String::new(),
                        dur: None,
                        args,
                    },
                );
                tr.maybe_flush_locked(&mut inner);
            });
        }

        // Sampled event: only record if duration crosses a sampling boundary.
        // In deterministic mode, sampled events are skipped entirely to
        // avoid flaky baselines, so avoid the cost of cloning args /
        // capturing the start time.
        if self.deterministic {
            return Box::new(|| {});
        }
        let start = Instant::now();
        let tr = self.clone();
        let name = name.to_string();
        Box::new(move || {
            let dur = start.elapsed().as_nanos() as f64 / 1000.0;
            let start_micros = (start - tr.start_time).as_nanos() as f64 / 1000.0;
            let interval_micros = SAMPLE_INTERVAL.as_nanos() as f64 / 1000.0;
            // `math.Mod` — Rust's `%` on floats is fmod, same semantics.
            if interval_micros - (start_micros % interval_micros) > dur {
                return;
            }
            let mut inner = tr.inner.lock().unwrap();
            if !tr.trace_started.load(Ordering::SeqCst) {
                return;
            }
            let tid = thread_id_locked(&tr, &mut inner, &args);
            inner.trace_content.extend_from_slice(b",\n");
            tr.write_event(
                &mut inner,
                &TraceEvent {
                    pid: 1,
                    tid,
                    ph: "X".to_string(),
                    cat: phase.0.to_string(),
                    ts: start_micros,
                    name,
                    s: String::new(),
                    dur: Some(dur),
                    args,
                },
            );
            tr.maybe_flush_locked(&mut inner);
        })
    }

    /// `NewTypeTracer` creates a new tracer for a specific checker.
    /// The `checker_index` is used to create unique filenames for each
    /// checker's output.
    pub fn new_type_tracer(&self, checker_index: i32) -> Arc<TypeTracer> {
        let mut inner = self.inner.lock().unwrap();

        let types_path = self
            .trace_dir
            .resolve_file(&format!("types_{checker_index}.json"));
        let tracer = Arc::new(TypeTracer {
            fs: self.fs.clone(),
            checker_index,
            types_path: types_path.clone(),
            types: Mutex::new(Vec::new()),
        });
        inner.tracers.push(tracer.clone());
        inner.legend.push(TraceRecord {
            config_file_path: self.config_file_path.clone(),
            trace_path: self.trace_path.as_string().to_string(),
            types_path: types_path.as_string().to_string(),
            checker_id: checker_index as i64,
        });
        tracer
    }

    /// `StopTracing` finalizes the tracing session and writes all output
    /// files.
    ///
    /// Go calls `tracer.DumpTypes()` — which reaches the checker's arenas
    /// through `*ast.Node`/`*ast.Symbol` pointers — then closes the trace
    /// file and writes `legend.json`. Here `dump` is invoked for each
    /// checker tracer so the caller can supply that checker's arenas (e.g.
    /// `|tracer| tracer.dump_types(nodes, symbols)`).
    pub fn stop_tracing(
        &self,
        dump: impl Fn(&TypeTracer) -> Result<(), Error>,
    ) -> Result<(), Error> {
        // Dump types from all tracers BEFORE acquiring the lock, because
        // dump_types → build_type_descriptor → display() → TypeToString can
        // re-enter the checker which calls push/pop (which need the lock).
        {
            let tracers = self.inner.lock().unwrap().tracers.clone();
            for tracer in tracers {
                if let Err(err) = dump(&tracer) {
                    return Err(Error(format!(
                        "failed to dump types for checker {}: {err}",
                        tracer.checker_index
                    )));
                }
            }
        }

        let mut inner = self.inner.lock().unwrap();

        // Close the trace file(s)
        if self.trace_started.load(Ordering::SeqCst) {
            // Surface any buffered flush failure before attempting the
            // final write.
            if let Some(err) = inner.flush_err.take() {
                inner.trace_content.clear();
                self.trace_started.store(false, Ordering::SeqCst);
                return Err(err);
            }
            // Flush any remaining buffered content and close the JSON array.
            let mut trailer = inner.trace_content.clone();
            trailer.extend_from_slice(b"\n]\n");
            if let Err(err) = self
                .fs
                .append_file(&self.trace_path, trace_content_str(&trailer))
            {
                return Err(Error(format!("failed to write trace file: {err}")));
            }
            inner.trace_content.clear();
            self.trace_started.store(false, Ordering::SeqCst);
        }

        // Sort legend entries by typesPath for deterministic output
        inner.legend.sort_by(|a, b| a.types_path.cmp(&b.types_path));

        // Write the legend file
        let legend_path = self.trace_dir.resolve_file("legend.json");
        let legend_data = tsc_json::marshal_indent(&inner.legend, "", "  ")
            .map_err(|err| Error(format!("failed to marshal legend file: {err}")))?;
        if let Err(err) = self
            .fs
            .write_file(&legend_path, trace_content_str(&legend_data))
        {
            return Err(Error(format!("failed to write legend file: {err}")));
        }

        Ok(())
    }
}

/// `tr.Instant` — safe on a nil `*Tracing` in Go; `Option<Arc<Tracing>>` is
/// the port's nil-able handle.
pub fn instant(tr: Option<&Arc<Tracing>>, phase: Phase, name: &str, args: TraceArgs) {
    if let Some(tr) = tr {
        tr.instant(phase, name, args);
    }
}

/// `tr.Push` — safe on a nil `*Tracing` in Go.
pub fn push(
    tr: Option<&Arc<Tracing>>,
    phase: Phase,
    name: &str,
    args: TraceArgs,
    separate_begin_and_end: bool,
) -> Box<dyn FnOnce()> {
    match tr {
        Some(tr) => tr.push(phase, name, args, separate_begin_and_end),
        None => Box::new(|| {}),
    }
}

fn write_event_to(buf: &mut Vec<u8>, event: &TraceEvent) {
    if let Err(err) = tsc_json::marshal_write(&mut *buf, event, &[]) {
        panic!("failed to marshal trace event: {err}");
    }
}

/// `tr.threadIDLocked`
fn thread_id_locked(tr: &Tracing, inner: &mut TracingInner, args: &TraceArgs) -> i64 {
    let Some(key) = trace_thread_key_from_args(args) else {
        return MAIN_THREAD_ID;
    };

    if let Some(tid) = inner.thread_ids.get(&key) {
        return *tid;
    }

    let mut tid = key.default_thread_id();
    loop {
        match inner.thread_keys.get(&tid) {
            None => break,
            Some(existing_key) if *existing_key == key => break,
            _ => tid += 1,
        }
    }
    inner.thread_ids.insert(key.clone(), tid);
    inner.thread_keys.insert(tid, key.clone());
    write_thread_name_event_locked(tr, inner, tid, &key.display_name());
    tid
}

/// `tr.writeThreadNameEventLocked`
fn write_thread_name_event_locked(tr: &Tracing, inner: &mut TracingInner, tid: i64, name: &str) {
    inner.trace_content.extend_from_slice(b",\n");
    tr.write_event(
        inner,
        &TraceEvent {
            pid: 1,
            tid,
            ph: "M".to_string(),
            cat: "__metadata".to_string(),
            ts: inner.metadata_ts,
            name: "thread_name".to_string(),
            s: String::new(),
            dur: None,
            args: trace_args(&[("name", serde_json::Value::from(name))]),
        },
    );
}

/// `traceThreadKind`
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum TraceThreadKind {
    Checker,
    File,
}

impl TraceThreadKind {
    fn as_str(&self) -> &'static str {
        match self {
            TraceThreadKind::Checker => "checker",
            TraceThreadKind::File => "file",
        }
    }
}

/// `traceThreadKey`
#[derive(Clone, PartialEq, Eq, Hash)]
struct TraceThreadKey {
    kind: TraceThreadKind,
    text: String,
    index: i64,
    has_index: bool,
}

/// `traceThreadKeyFromArgs`
fn trace_thread_key_from_args(args: &TraceArgs) -> Option<TraceThreadKey> {
    if args.is_empty() {
        return None;
    }

    if let Some(checker_id) = args.get("checkerId").and_then(|v| v.as_i64()) {
        return Some(TraceThreadKey {
            kind: TraceThreadKind::Checker,
            text: String::new(),
            index: checker_id,
            has_index: true,
        });
    }

    for key in TRACE_THREAD_ARG_KEYS {
        if let Some(value) = args.get(key) {
            if let Some(path) = value.as_str() {
                if !path.is_empty() {
                    return Some(TraceThreadKey {
                        kind: TraceThreadKind::File,
                        text: path.to_string(),
                        index: 0,
                        has_index: false,
                    });
                }
            }
        }
    }

    None
}

impl TraceThreadKey {
    /// `key.defaultThreadID()`
    fn default_thread_id(&self) -> i64 {
        if self.kind == TraceThreadKind::Checker && self.has_index && self.index >= 0 {
            return FIRST_SYNTHETIC_THREAD_ID + self.index;
        }
        stable_trace_thread_id(self)
    }

    /// `key.displayName()`
    fn display_name(&self) -> String {
        if self.has_index {
            return format!("{}:{}", self.kind.as_str(), self.index);
        }
        format!("{}:{}", self.kind.as_str(), self.text)
    }
}

/// `stableTraceThreadID`
fn stable_trace_thread_id(key: &TraceThreadKey) -> i64 {
    // `xxh3.New(); WriteString(kind); WriteString(":"); WriteString(text|index)`
    // — the same bytes as hashing the concatenated string.
    let mut s = String::with_capacity(key.kind.as_str().len() + 1 + key.text.len().max(20));
    s.push_str(key.kind.as_str());
    s.push(':');
    if key.has_index {
        s.push_str(&key.index.to_string());
    } else {
        s.push_str(&key.text);
    }
    FIRST_FILE_THREAD_ID + (xxh3_64(s.as_bytes()) % (FILE_THREAD_ID_HASH_RANGE as u64)) as i64
}

/// `typeTracer` is the per-checker tracer implementation.
pub struct TypeTracer {
    fs: Arc<dyn Vfs>,
    /// `checkerIndex`
    pub checker_index: i32,
    types_path: RootedFilePath,
    /// `Rc` elements — the trait object is `!Send` now (the checker's arena
    /// is `Rc<RefCell<..>>`); the `Mutex` stays for the smallest diff.
    types: Mutex<Vec<Rc<dyn TracedType>>>,
}

impl TypeTracer {
    /// `typesPath` — the checker's `types_N.json` output path.
    pub fn types_path(&self) -> &RootedFilePath {
        &self.types_path
    }

    /// `t.DumpTypes()` — writes the recorded types as a JSON array, one
    /// `TypeDescriptor` per line, to `types_path`.
    ///
    /// `nodes`/`symbols` are the checker's arenas; Go's `DumpTypes` reaches
    /// them through the `*ast.Node`/`*ast.Symbol` pointers returned by
    /// `TracedType` accessors.
    pub fn dump_types(&self, nodes: &[Node], symbols: &SymbolArena) -> Result<(), Error> {
        // Copy the types slice under lock, then release so `display()` calls
        // during `build_type_descriptor` don't deadlock when they create new
        // types.
        let types = self.types.lock().unwrap().clone();

        if types.is_empty() {
            return Ok(());
        }

        // Write opening bracket (no newline so type ID matches line number)
        let mut sb = String::from("[");

        let mut recursion_identity_map: HashMap<RecursionIdentity, i32> = HashMap::new();

        for (i, typ) in types.iter().enumerate() {
            let descriptor =
                build_type_descriptor(typ.as_ref(), &mut recursion_identity_map, nodes, symbols);

            let bytes = tsc_json::marshal(&descriptor, &[])
                .map_err(|err| Error(format!("failed to marshal type {}: {err}", typ.id())))?;
            sb.push_str(std::str::from_utf8(&bytes).expect("descriptor JSON is UTF-8"));

            if i < types.len() - 1 {
                sb.push_str(",\n");
            }
        }

        sb.push_str("]\n");

        // Go returns the `WriteFile` error unwrapped.
        self.fs
            .write_file(&self.types_path, &sb)
            .map_err(|err| Error(err.to_string()))
    }
}

impl Tracer for TypeTracer {
    /// `t.RecordType(typ)`
    fn record_type(&self, typ: Rc<dyn TracedType>) {
        self.types.lock().unwrap().push(typ);
    }

    /// `t.DumpTypes()` — see `TypeTracer::dump_types`.
    fn dump_types(&self, nodes: &[Node], symbols: &SymbolArena) -> Result<(), Error> {
        TypeTracer::dump_types(self, nodes, symbols)
    }
}

/// `TypeDescriptor` represents a type in the output JSON.
///
/// `,omitzero` tags become `skip_serializing_if`. `conditional_true_type`/
/// `conditional_false_type` are `Option<i32>` (not `u32`) because unresolved
/// conditional branches are serialized as -1, matching TypeScript's
/// behavior. Go's `Flags []string` has no `omitzero`; a `Vec` emits `[]` —
/// Go emits `null` only if `FormatFlags()` returns nil, which `format_flags`
/// cannot express.
#[derive(Clone, Serialize)]
pub struct TypeDescriptor {
    pub id: u32,
    #[serde(rename = "intrinsicName", skip_serializing_if = "String::is_empty")]
    pub intrinsic_name: String,
    #[serde(rename = "symbolName", skip_serializing_if = "String::is_empty")]
    pub symbol_name: String,
    #[serde(rename = "recursionId", skip_serializing_if = "Option::is_none")]
    pub recursion_id: Option<i32>,
    #[serde(rename = "isTuple", skip_serializing_if = "is_false")]
    pub is_tuple: bool,
    #[serde(rename = "unionTypes", skip_serializing_if = "Vec::is_empty")]
    pub union_types: Vec<u32>,
    #[serde(rename = "intersectionTypes", skip_serializing_if = "Vec::is_empty")]
    pub intersection_types: Vec<u32>,
    #[serde(rename = "aliasTypeArguments", skip_serializing_if = "Vec::is_empty")]
    pub alias_type_arguments: Vec<u32>,
    #[serde(rename = "keyofType", skip_serializing_if = "Option::is_none")]
    pub keyof_type: Option<u32>,
    #[serde(
        rename = "indexedAccessObjectType",
        skip_serializing_if = "Option::is_none"
    )]
    pub indexed_access_object_type: Option<u32>,
    #[serde(
        rename = "indexedAccessIndexType",
        skip_serializing_if = "Option::is_none"
    )]
    pub indexed_access_index_type: Option<u32>,
    #[serde(
        rename = "conditionalCheckType",
        skip_serializing_if = "Option::is_none"
    )]
    pub conditional_check_type: Option<u32>,
    #[serde(
        rename = "conditionalExtendsType",
        skip_serializing_if = "Option::is_none"
    )]
    pub conditional_extends_type: Option<u32>,
    #[serde(
        rename = "conditionalTrueType",
        skip_serializing_if = "Option::is_none"
    )]
    pub conditional_true_type: Option<i32>,
    #[serde(
        rename = "conditionalFalseType",
        skip_serializing_if = "Option::is_none"
    )]
    pub conditional_false_type: Option<i32>,
    #[serde(
        rename = "substitutionBaseType",
        skip_serializing_if = "Option::is_none"
    )]
    pub substitution_base_type: Option<u32>,
    #[serde(rename = "constraintType", skip_serializing_if = "Option::is_none")]
    pub constraint_type: Option<u32>,
    #[serde(rename = "instantiatedType", skip_serializing_if = "Option::is_none")]
    pub instantiated_type: Option<u32>,
    #[serde(rename = "typeArguments", skip_serializing_if = "Vec::is_empty")]
    pub type_arguments: Vec<u32>,
    #[serde(rename = "referenceLocation", skip_serializing_if = "Option::is_none")]
    pub reference_location: Option<Location>,
    #[serde(
        rename = "reverseMappedSourceType",
        skip_serializing_if = "Option::is_none"
    )]
    pub reverse_mapped_source_type: Option<u32>,
    #[serde(
        rename = "reverseMappedMappedType",
        skip_serializing_if = "Option::is_none"
    )]
    pub reverse_mapped_mapped_type: Option<u32>,
    #[serde(
        rename = "reverseMappedConstraintType",
        skip_serializing_if = "Option::is_none"
    )]
    pub reverse_mapped_constraint_type: Option<u32>,
    #[serde(
        rename = "evolvingArrayElementType",
        skip_serializing_if = "Option::is_none"
    )]
    pub evolving_array_element_type: Option<u32>,
    #[serde(
        rename = "evolvingArrayFinalType",
        skip_serializing_if = "Option::is_none"
    )]
    pub evolving_array_final_type: Option<u32>,
    #[serde(
        rename = "destructuringPattern",
        skip_serializing_if = "Option::is_none"
    )]
    pub destructuring_pattern: Option<Location>,
    #[serde(rename = "firstDeclaration", skip_serializing_if = "Option::is_none")]
    pub first_declaration: Option<Location>,
    pub flags: Vec<String>,
    #[serde(rename = "display", skip_serializing_if = "String::is_empty")]
    pub display: String,
}

fn is_false(v: &bool) -> bool {
    !*v
}

impl Default for TypeDescriptor {
    /// `TypeDescriptor{ID: typ.Id(), Flags: typ.FormatFlags()}` — every other
    /// field starts at its zero value.
    fn default() -> Self {
        TypeDescriptor {
            id: 0,
            intrinsic_name: String::new(),
            symbol_name: String::new(),
            recursion_id: None,
            is_tuple: false,
            union_types: Vec::new(),
            intersection_types: Vec::new(),
            alias_type_arguments: Vec::new(),
            keyof_type: None,
            indexed_access_object_type: None,
            indexed_access_index_type: None,
            conditional_check_type: None,
            conditional_extends_type: None,
            conditional_true_type: None,
            conditional_false_type: None,
            substitution_base_type: None,
            constraint_type: None,
            instantiated_type: None,
            type_arguments: Vec::new(),
            reference_location: None,
            reverse_mapped_source_type: None,
            reverse_mapped_mapped_type: None,
            reverse_mapped_constraint_type: None,
            evolving_array_element_type: None,
            evolving_array_final_type: None,
            destructuring_pattern: None,
            first_declaration: None,
            flags: Vec::new(),
            display: String::new(),
        }
    }
}

/// `Location` represents a source code location.
#[derive(Clone, Serialize)]
pub struct Location {
    pub path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub start: Option<LineAndChar>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end: Option<LineAndChar>,
}

/// `LineAndChar` represents a line and character position (1-indexed).
#[derive(Clone, Serialize)]
pub struct LineAndChar {
    pub line: i64,
    pub character: i64,
}

/// `t.buildTypeDescriptor`
fn build_type_descriptor(
    typ: &dyn TracedType,
    recursion_identity_map: &mut HashMap<RecursionIdentity, i32>,
    nodes: &[Node],
    symbols: &SymbolArena,
) -> TypeDescriptor {
    let symbol = typ.symbol();
    let alias_symbol = typ.alias_symbol();

    let mut desc = TypeDescriptor {
        id: typ.id(),
        flags: typ.format_flags(),
        ..Default::default()
    };

    // Assign a unique integer token per recursion identity, matching
    // TypeScript's behavior. This lets trace analysis tools detect which
    // types share the same recursion identity.
    if let Some(identity) = typ.recursion_identity() {
        let token = match recursion_identity_map.get(&identity) {
            Some(token) => *token,
            None => {
                let token = recursion_identity_map.len() as i32;
                recursion_identity_map.insert(identity, token);
                token
            }
        };
        desc.recursion_id = Some(token);
    }

    // Intrinsic name
    let name = typ.intrinsic_name();
    if !name.is_empty() {
        desc.intrinsic_name = name;
    }

    // Symbol name - escape the internal symbol name prefix for valid JSON
    if let Some(sym) = alias_symbol.or(symbol) {
        desc.symbol_name = escape_all_internal_symbol_names(&symbols[sym.index()].name);
    }

    // Tuple flag
    if typ.is_tuple() {
        desc.is_tuple = true;
    }

    // Union types
    let types = typ.union_types();
    if !types.is_empty() {
        desc.union_types = map_type_ids(&types);
    }

    // Intersection types
    let types = typ.intersection_types();
    if !types.is_empty() {
        desc.intersection_types = map_type_ids(&types);
    }

    // Alias type arguments
    let args = typ.alias_type_arguments();
    if !args.is_empty() {
        desc.alias_type_arguments = map_type_ids(&args);
    }

    // Index type (keyof)
    if let Some(index_type) = typ.index_type() {
        desc.keyof_type = Some(index_type.id());
    }

    // Indexed access type
    if let Some(obj_type) = typ.indexed_access_object_type() {
        desc.indexed_access_object_type = Some(obj_type.id());
    }
    if let Some(idx_type) = typ.indexed_access_index_type() {
        desc.indexed_access_index_type = Some(idx_type.id());
    }

    // Conditional type
    if typ.is_conditional() {
        if let Some(check_type) = typ.conditional_check_type() {
            desc.conditional_check_type = Some(check_type.id());
        }
        if let Some(extends_type) = typ.conditional_extends_type() {
            desc.conditional_extends_type = Some(extends_type.id());
        }
        if let Some(true_type) = typ.conditional_true_type() {
            desc.conditional_true_type = Some(true_type.id() as i32);
        } else {
            desc.conditional_true_type = Some(-1);
        }
        if let Some(false_type) = typ.conditional_false_type() {
            desc.conditional_false_type = Some(false_type.id() as i32);
        } else {
            desc.conditional_false_type = Some(-1);
        }
    }

    // Substitution type
    if let Some(base_type) = typ.substitution_base_type() {
        desc.substitution_base_type = Some(base_type.id());
    }
    if let Some(constraint) = typ.substitution_constraint_type() {
        desc.constraint_type = Some(constraint.id());
    }

    // Reference type
    if let Some(target) = typ.reference_target() {
        desc.instantiated_type = Some(target.id());
    }
    let args = typ.reference_type_arguments();
    if !args.is_empty() {
        desc.type_arguments = map_type_ids(&args);
    }
    if let Some(node) = typ.reference_node() {
        desc.reference_location = get_location(node, nodes);
    }

    // Reverse mapped type
    if let Some(source_type) = typ.reverse_mapped_source_type() {
        desc.reverse_mapped_source_type = Some(source_type.id());
    }
    if let Some(mapped_type) = typ.reverse_mapped_mapped_type() {
        desc.reverse_mapped_mapped_type = Some(mapped_type.id());
    }
    if let Some(constraint_type) = typ.reverse_mapped_constraint_type() {
        desc.reverse_mapped_constraint_type = Some(constraint_type.id());
    }

    // Evolving array type
    if let Some(elem_type) = typ.evolving_array_element_type() {
        desc.evolving_array_element_type = Some(elem_type.id());
    }
    if let Some(final_type) = typ.evolving_array_final_type() {
        desc.evolving_array_final_type = Some(final_type.id());
    }

    // Pattern (destructuring)
    if let Some(pattern) = typ.pattern() {
        desc.destructuring_pattern = get_location(pattern, nodes);
    }

    // First declaration - prefer aliasSymbol, matching TypeScript's
    // `aliasSymbol ?? symbol`
    if let Some(first_decl_symbol) = alias_symbol.or(symbol) {
        if let Some(first_decl) = symbols[first_decl_symbol.index()].declarations.first() {
            desc.first_declaration = get_location(*first_decl, nodes);
        }
    }

    // Display text
    let display = typ.display();
    if !display.is_empty() {
        desc.display = display;
    }

    desc
}

/// `mapTypeIds`
fn map_type_ids(types: &[Option<Rc<dyn TracedType>>]) -> Vec<u32> {
    if types.is_empty() {
        return Vec::new();
    }
    types
        .iter()
        .map(|t| t.as_ref().map(|t| t.id()).unwrap_or(0))
        .collect()
}

/// `getLocation` — `nodes` is the AST arena `node`'s `NodeId` indexes into
/// (Go walks `*ast.Node` parent pointers instead).
fn get_location(node: NodeId, nodes: &[Node]) -> Option<Location> {
    let file_id = get_source_file_of_node(Some(node), nodes)?;
    let file = nodes[file_id].as_source_file();

    let start_pos = tsc_scanner::scanner::get_token_pos_of_node(node, file, false, nodes);
    let (start_line, start_char) =
        tsc_scanner::scanner::get_ecma_line_and_utf16_character_of_position(file, start_pos);
    let (end_line, end_char) = tsc_scanner::scanner::get_ecma_line_and_utf16_character_of_position(
        file,
        nodes[node].end(),
    );

    Some(Location {
        path: CaseSensitivity::CaseInsensitive
            .path_key(&file.file_name().as_path())
            .as_string()
            .to_string(),
        start: Some(LineAndChar {
            line: (start_line + 1) as i64,
            character: (start_char + 1) as i64,
        }),
        end: Some(LineAndChar {
            line: (end_line + 1) as i64,
            character: (end_char + 1) as i64,
        }),
    })
}
