// Ported from tsc/internal/execute/incremental @ ec47d33c23e464a17cdf2475632cba629bee8763

//! Incremental build support: `.tsbuildinfo` serialization, snapshot
//! state, change tracking and incremental emit.
//!
//! Module map (Go source → Rust file):
//! - `buildInfo.go` → `build_info.rs` — serialized `.tsbuildinfo` types and
//!   their custom JSON shapes.
//! - `snapshot.go` → `snapshot.rs` — in-memory incremental state.
//! - `referencemap.go` → `reference_map.rs` — file-reference and
//!   reverse-reference maps.
//! - `host.go` → `host.rs` — mtime access helpers.
//! - `incremental.go` → `incremental.rs` — build-info reader and
//!   `ReadBuildInfoProgram`.
//! - `buildinfotosnapshot.go` → `buildinfo_to_snapshot.rs`.
//! - `programtosnapshot.go` → `program_to_snapshot.rs`.
//! - `snapshottobuildinfo.go` → `snapshot_to_buildinfo.rs`.
//! - `affectedfileshandler.go` → `affected_files_handler.rs`.
//! - `emitfileshandler.go` → `emit_files_handler.rs`.
//! - `program.go` → `program.rs` — the incremental `Program` implementing
//!   `compiler.ProgramLike`.
//!
//! The `performIncrementalCompilation`/`NewProgram` wiring used by `tsc`
//! lives in `crate::tsc_main` (see `tsc.rs` for the porting note).

pub mod affected_files_handler;
pub mod build_info;
pub mod buildinfo_to_snapshot;
pub mod emit_files_handler;
pub mod host;
pub mod incremental;
pub mod program;
pub mod program_to_snapshot;
pub mod reference_map;
pub mod snapshot;
pub mod snapshot_to_buildinfo;
pub mod tsc;

pub use host::{Host, create_host, get_mtime};
pub use incremental::{BuildInfoReader, new_build_info_reader, read_build_info_program};
pub use program::{Program, SignatureUpdateKind, TestingData, new_program};
pub use snapshot::{
    BuildInfoDiagnosticWithFileName, DiagnosticsOrBuildInfoDiagnosticsWithFileName, EmitSignature,
    FILE_EMIT_KIND_ALL, FILE_EMIT_KIND_ALL_DTS, FILE_EMIT_KIND_ALL_DTS_EMIT, FILE_EMIT_KIND_ALL_JS,
    FILE_EMIT_KIND_DTS, FILE_EMIT_KIND_DTS_EMIT, FILE_EMIT_KIND_DTS_ERRORS, FILE_EMIT_KIND_DTS_MAP,
    FILE_EMIT_KIND_JS, FILE_EMIT_KIND_JS_INLINE_MAP, FILE_EMIT_KIND_JS_MAP, FILE_EMIT_KIND_NONE,
    FileEmitKind, FileInfo, Snapshot, compute_hash, get_file_emit_kind, get_pending_emit_kind,
    get_pending_emit_kind_with_options, get_text_handling_source_map_for_signature,
};
