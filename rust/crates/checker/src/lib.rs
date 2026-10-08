//! `tsc-checker` — in-progress port of `tsc/internal/checker`.
//!
//! FOUNDATION phase: printer-free data-model layer only — `types.go`,
//! `links.go`, `mapper.go`, `nodebuilderscopes.go`, `symboltracker.go`,
//! `tracer.go`, `jsdoc.go`, `stringer_generated.go`, and the free functions
//! of `services.go`. The full `Checker` (`checker.go`, `relater.go`,
//! `inference.go`, `flow.go`, `jsx.go`, `exports.go`, `grammarchecks.go`)
//! is deferred; `checker_core.rs` holds a `PORT(partial)` stub exposing only
//! what the ported foundation files reference. See PORTING-NOTES.md.
//!
//! Baseline Go commit: `ec47d33c23e464a17cdf2475632cba629bee8763`.

pub mod checker_core;
pub mod flagdef;
pub mod jsdoc;
pub mod links;
pub mod mapper;
pub mod nodebuilderimpl;
pub mod nodebuilderscopes;
pub mod services;
pub mod stringer_generated;
pub mod symboltracker;
pub mod tracer;
pub mod types;
