// tsc-diagnosticwriter — port of tsc/internal/diagnosticwriter

pub mod diagnosticwriter;

#[cfg(test)]
mod diagnosticwriter_test;

pub use diagnosticwriter::*;
