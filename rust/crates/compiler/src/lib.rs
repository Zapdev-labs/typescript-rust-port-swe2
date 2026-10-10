// Ported from tsc/internal/compiler @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Package compiler implements the TypeScript compiler (Go `pkg.go`).
//
// Layout mirrors the Go files one-to-one:
//   - program.go                        -> program.rs
//   - fileloader.go                     -> file_loader.rs
//   - filesparser.go                    -> files_parser.rs
//   - emitter.go                        -> emitter.rs
//   - checkerpool.go                    -> checker_pool.rs
//   - fileInclude.go                    -> file_include.rs
//   - includeprocessor.go               -> include_processor.rs
//   - host.go                           -> host.rs
//   - emitHost.go                       -> emit_host.rs
//   - processingDiagnostic.go           -> processing_diagnostic.rs
//   - projectreferenceparser.go         -> project_reference_parser.rs
//   - projectreferencefilemapper.go     -> project_reference_file_mapper.rs
//   - projectreferencedtsfakinghost.go  -> project_reference_dts_faking_host.rs
//
// PORT(global): Go's `*ast.SourceFile` becomes a `NodeId` plus the owning
// per-file `Vec<ast::Node>` arena (see rust/PORTING-NOTES.md). `*ast.Node`
// is `NodeId` throughout; `Option<NodeId>` mirrors nil pointers.
//
// PORT(global): the Go implementation parallelizes program construction and
// checking with goroutine work groups. `tsc_core::WorkGroup::queue` requires
// `Send` closures, but `Rc`/`RefCell`/`Node` arenas are not `Send`, so all
// work groups here run through the single-threaded path (`WorkList` in
// files_parser.rs). Semantics are preserved; only parallelism is dropped —
// see PORTING-NOTES.md.
pub mod checker_pool;
pub mod emit_host;
pub mod emitter;
pub mod file_include;
pub mod file_loader;
pub mod files_parser;
pub mod host;
pub mod include_processor;
pub mod processing_diagnostic;
pub mod program;
pub mod project_reference_dts_faking_host;
pub mod project_reference_file_mapper;
pub mod project_reference_parser;
