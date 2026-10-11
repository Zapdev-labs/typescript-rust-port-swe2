// Ported from tsc/internal/ls/autoimport/index.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Go's `rune` keys are Rust `char`s; byte indices in `wordIndices` map to
// `str` slice boundaries, which are already UTF-8 safe.

use std::collections::HashMap;
use std::rc::Rc;

/// `Named` is the constraint for types that can provide their name.
pub trait Named {
    /// `Name() string`.
    fn name(&self) -> &str;
}

/// `Rc<T: Named>` forwards, so `Index<Rc<Export>>` can index shared exports.
impl<T: Named> Named for Rc<T> {
    fn name(&self) -> &str {
        (**self).name()
    }
}

/// `Index` stores entries with an index mapping uppercase letters to entries
/// whose name starts with that letter, and lowercase letters to entries whose
/// name contains a word starting with that letter.
#[derive(Default)]
pub struct Index<T: Named> {
    /// `entries`.
    pub(crate) entries: Vec<T>,
    index: HashMap<char, Vec<usize>>,
}

impl<T: Named> Index<T> {
    /// `len(idx.entries)` — read access for stats.
    pub fn entry_count(&self) -> usize {
        self.entries.len()
    }

    /// `Index.Find` — exact or case-insensitive lookup.
    pub fn find(&self, name: &str, case_sensitive: bool) -> Vec<T>
    where
        T: Clone,
    {
        if self.entries.is_empty() || name.is_empty() {
            return Vec::new();
        }
        let first_rune = match name.chars().next() {
            Some(c) => c,
            None => return Vec::new(),
        };
        let first_rune_upper = crate::autoimport::util::to_upper(first_rune);
        let Some(candidates) = self.index.get(&first_rune_upper) else {
            return Vec::new();
        };

        let mut results = Vec::new();
        for &entry_index in candidates {
            let entry = &self.entries[entry_index];
            let entry_name = entry.name();
            if (case_sensitive && entry_name == name)
                || (!case_sensitive && entry_name.to_lowercase() == name.to_lowercase())
            {
                results.push(entry.clone());
            }
        }
        results
    }

    /// `Index.SearchWordPrefix` returns each entry whose name contains a word
    /// beginning with the first character of `prefix`, and whose name contains
    /// all characters of `prefix` in order (case-insensitive).
    pub fn search_word_prefix(&self, prefix: &str) -> Vec<T>
    where
        T: Clone,
    {
        if self.entries.is_empty() {
            return Vec::new();
        }
        if prefix.is_empty() {
            return self.entries.clone();
        }

        let prefix_lower = prefix.to_lowercase();
        let first_rune = match prefix_lower.chars().next() {
            Some(c) => c,
            None => return Vec::new(),
        };
        let first_rune_upper = crate::autoimport::util::to_upper(first_rune);
        let first_rune_lower = crate::autoimport::util::to_lower(first_rune);

        // Look up entries that have words starting with this letter
        let name_starts = self.index.get(&first_rune_upper);
        let word_starts = if first_rune_upper != first_rune_lower {
            self.index.get(&first_rune_lower)
        } else {
            None
        };
        let count = name_starts.map_or(0, |v| v.len()) + word_starts.map_or(0, |v| v.len());
        if count == 0 {
            return Vec::new();
        }

        let mut results = Vec::with_capacity(count);
        for starts in [name_starts, word_starts].into_iter().flatten() {
            for &i in starts {
                let entry = &self.entries[i];
                if contains_chars_in_order(entry.name(), &prefix_lower) {
                    results.push(entry.clone());
                }
            }
        }
        results
    }

    /// `insertAsWords` adds a value to the index keyed by the first letter of
    /// each word in its name.
    pub fn insert_as_words(&mut self, value: T) {
        let name = value.name().to_string();
        if name.is_empty() {
            panic!("Cannot index entry with empty name");
        }
        let entry_index = self.entries.len();
        self.entries.push(value);

        let indices = crate::autoimport::util::word_indices(&name);
        let mut seen_runes: HashMap<char, bool> = HashMap::new();

        for (i, start) in indices.iter().enumerate() {
            let substr = &name[*start..];
            let Some(mut first_rune) = substr.chars().next() else {
                continue;
            };
            if i == 0 {
                // Name start keyed by uppercase
                first_rune = crate::autoimport::util::to_upper(first_rune);
                self.index.entry(first_rune).or_default().push(entry_index);
                seen_runes.insert(first_rune, true); // (Still set seenRunes in case first character is non-alphabetic)
            } else {
                // Subsequent word starts keyed by lowercase
                first_rune = crate::autoimport::util::to_lower(first_rune);
                if !seen_runes.contains_key(&first_rune) {
                    self.index.entry(first_rune).or_default().push(entry_index);
                    seen_runes.insert(first_rune, true);
                }
            }
        }
    }

    /// `Index.Clone` creates a new Index containing only entries for which
    /// `filter` returns true.
    pub fn clone_filtered(&self, filter: impl Fn(&T) -> bool) -> Option<Index<T>>
    where
        T: Clone,
    {
        let mut new_idx = Index::<T> {
            entries: Vec::with_capacity(self.entries.len()),
            index: HashMap::with_capacity(self.index.len()),
        };

        // Build mapping from old index to new index for filtered entries
        let mut old_to_new: HashMap<usize, usize> = HashMap::with_capacity(self.entries.len());
        for (old_index, entry) in self.entries.iter().enumerate() {
            if filter(entry) {
                old_to_new.insert(old_index, new_idx.entries.len());
                new_idx.entries.push(entry.clone());
            }
        }

        // Rebuild the index with remapped indices
        for (r, old_indices) in &self.index {
            let mut new_indices = Vec::with_capacity(old_indices.len());
            for &old_index in old_indices {
                if let Some(&new_index) = old_to_new.get(&old_index) {
                    new_indices.push(new_index);
                }
            }
            if !new_indices.is_empty() {
                new_idx.index.insert(*r, new_indices);
            }
        }

        Some(new_idx)
    }
}

/// `containsCharsInOrder` checks if `s` contains all characters from `pattern`
/// in order (case-insensitive).
fn contains_chars_in_order(s: &str, pattern: &str) -> bool {
    let s = s.to_lowercase();
    let mut pattern_chars = pattern.chars().peekable();
    for ch in s.chars() {
        match pattern_chars.peek() {
            Some(&p) if p == ch => {
                pattern_chars.next();
            }
            _ => {}
        }
    }
    pattern_chars.next().is_none()
}
