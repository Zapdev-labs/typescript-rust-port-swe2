// Ported from tsc/internal/project/programcounter.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::rc::{Rc, Weak};

use fragile::Fragile;
use rustc_hash::FxHashMap;
use tsc_compiler::program::Program;

/// `programCounter` — ref-counts programs across immutable snapshots. A
/// program whose count reaches zero is no longer referenced by any snapshot
/// and may be disposed.
///
/// PORT: Go keys the map on `*compiler.Program` (pointer identity). Here
/// the key is `Rc::as_ptr` (as `usize`) with a `Weak` retained per entry so
/// the allocation — and therefore the identity — cannot be recycled while
/// it is still tracked. `Program` is `!Send`, so the map lives behind
/// `Fragile`, which panics on cross-thread access (the compiler pipeline is
/// single-threaded; see the PORT note in `checkerpool.rs`).
pub struct ProgramCounter {
    refs: Fragile<RefCell<FxHashMap<usize, (Weak<Program>, i32)>>>,
}

impl Default for ProgramCounter {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgramCounter {
    /// `&programCounter{}`.
    pub fn new() -> Self {
        ProgramCounter {
            refs: Fragile::new(RefCell::new(FxHashMap::default())),
        }
    }

    /// `Ref` increments the reference count for a program. If the program is
    /// not yet tracked, it is added with a reference count of 1.
    pub fn ref_(&self, program: &Rc<Program>) {
        let mut refs = self.refs.get().borrow_mut();
        match refs.entry(Rc::as_ptr(program) as usize) {
            Entry::Occupied(mut e) => e.get_mut().1 += 1,
            Entry::Vacant(e) => {
                e.insert((Rc::downgrade(program), 1));
            }
        }
    }

    /// `Deref` decrements the reference count and reports whether the count
    /// reached zero (the program is no longer referenced by any snapshot).
    /// Returns false for untracked programs, matching Go's `ok == false`.
    pub fn deref(&self, program: &Rc<Program>) -> bool {
        let mut refs = self.refs.get().borrow_mut();
        let Entry::Occupied(mut e) = refs.entry(Rc::as_ptr(program) as usize) else {
            return false;
        };
        let count = e.get().1 - 1;
        if count < 0 {
            panic!("program reference count went below zero");
        }
        if count == 0 {
            e.remove();
            return true;
        }
        e.get_mut().1 = count;
        false
    }

    /// `Len`.
    pub fn len(&self) -> usize {
        self.refs.get().borrow().len()
    }
}
