//! `tsc-checker` — in-progress port of `tsc/internal/checker`.
//!
//! Foundation layer: `types.go`, `links.go`, `mapper.go`,
//! `nodebuilderscopes.go`, `symboltracker.go`, `tracer.go`, `jsdoc.go`,
//! `stringer_generated.go`, and the free functions of `services.go`.
//! `checker_core.rs` now carries the `Checker` state skeleton (Go
//! `checker.go` fields in declaration order) plus a faithful `new_checker`
//! initialization sequence; the per-domain modules `checker_types.rs`,
//! `relater.rs`, `flow.rs`, `inference.rs`, `emitresolver.rs`,
//! `symbolaccessibility.rs`, and `nodebuilder.rs` hold the auxiliary state
//! types those files define in Go. Method bodies for relation checking,
//! flow analysis, inference, and diagnostics remain `PORT(deferred)`.
//! See PORTING-NOTES.md.
//!
//! Baseline Go commit: `ec47d33c23e464a17cdf2475632cba629bee8763`.

pub mod checker_a;
pub mod checker_b;
pub mod checker_c;
pub mod checker_core;
pub mod checker_d;
pub mod checker_types;
pub mod emitresolver;
pub mod exports;
pub mod emitsupport;
pub mod flagdef;
pub mod flow;
pub mod grammarchecks;
pub mod inference;
pub mod jsdoc;
pub mod jsx;
pub mod links;
pub mod mapper;
pub mod nodebuilder;
pub mod nodebuilderimpl;
pub mod nodebuilderscopes;
pub mod printer_util;
pub mod relater;
pub mod services;
pub mod stringer_generated;
pub mod symbolaccessibility;
pub mod symboltracker;
pub mod tracer;
pub mod types;
pub mod utilities;
