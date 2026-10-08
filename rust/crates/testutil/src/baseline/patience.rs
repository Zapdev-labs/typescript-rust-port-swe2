// Ported from github.com/peter-evans/patience v0.3.0
// (patience.go, lcs.go, unified.go, format.go) — the Go module
// `tsc/internal/testutil/baseline` imports for DiffText.
//
// PORT: Go `[]string` lines become `&[u8]` lines and the rendered diff is
// `Vec<u8>` (Go strings/diffs may hold arbitrary bytes). Only the pieces
// baseline.rs needs are ported: `Diff`, `LCS`, `makeHunks`, and
// `UnifiedDiffTextWithOptions`. `DiffText`/`DiffTextA`/`DiffTextB`/
// `UnifiedDiffText` are omitted — no callers.

use std::collections::HashMap;

/// DiffType defines the type of a diff element.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(i8)]
pub enum DiffType {
    /// Delete represents a diff delete operation.
    Delete = -1,
    /// Insert represents a diff insert operation.
    Insert = 1,
    /// Equal represents no diff.
    Equal = 0,
}

/// DiffLine represents a single line and its diff type.
#[derive(Clone, Copy, Debug)]
pub struct DiffLine<'l> {
    pub text: &'l [u8],
    pub type_: DiffType,
}

/// toDiffLines is a convenience function to convert a slice of lines
/// to a slice of DiffLines with the specified diff type.
fn to_diff_lines<'l>(a: &[&'l [u8]], t: DiffType) -> Vec<DiffLine<'l>> {
    a.iter().map(|&l| DiffLine { text: l, type_: t }).collect()
}

/// uniqueElements returns a slice of unique elements from a slice of
/// lines, and a slice of the original indices of each element.
fn unique_elements<'l>(a: &[&'l [u8]]) -> (Vec<&'l [u8]>, Vec<usize>) {
    let mut m: HashMap<&[u8], usize> = HashMap::new();
    for e in a {
        *m.entry(e).or_insert(0) += 1;
    }
    let mut elements = Vec::new();
    let mut indices = Vec::new();
    for (i, e) in a.iter().enumerate() {
        if m[e] == 1 {
            elements.push(*e);
            indices.push(i);
        }
    }
    (elements, indices)
}

/// Diff returns the patience diff of two slices of lines.
pub fn diff<'l>(a: &[&'l [u8]], b: &[&'l [u8]]) -> Vec<DiffLine<'l>> {
    if a.is_empty() && b.is_empty() {
        return Vec::new();
    }
    if a.is_empty() {
        return to_diff_lines(b, DiffType::Insert);
    }
    if b.is_empty() {
        return to_diff_lines(a, DiffType::Delete);
    }

    // Find equal elements at the head of slices a and b.
    let mut i = 0;
    while i < a.len() && i < b.len() && a[i] == b[i] {
        i += 1;
    }
    if i > 0 {
        let mut diffs = to_diff_lines(&a[..i], DiffType::Equal);
        diffs.extend(diff(&a[i..], &b[i..]));
        return diffs;
    }

    // Find equal elements at the tail of slices a and b.
    let mut j = 0;
    while j < a.len() && j < b.len() && a[a.len() - 1 - j] == b[b.len() - 1 - j] {
        j += 1;
    }
    if j > 0 {
        let mut diffs = diff(&a[..a.len() - j], &b[..b.len() - j]);
        diffs.extend(to_diff_lines(&a[a.len() - j..], DiffType::Equal));
        return diffs;
    }

    // Find the longest common subsequence of unique elements in a and b.
    let (ua, idxa) = unique_elements(a);
    let (ub, idxb) = unique_elements(b);
    let mut lcs = lcs(&ua, &ub);

    // If the LCS is empty, the diff is all deletions and insertions.
    if lcs.is_empty() {
        let mut diffs = to_diff_lines(a, DiffType::Delete);
        diffs.extend(to_diff_lines(b, DiffType::Insert));
        return diffs;
    }

    // Lookup the original indices of slices a and b.
    for x in &mut lcs {
        x[0] = idxa[x[0]];
        x[1] = idxb[x[1]];
    }

    let mut diffs = Vec::new();
    let (mut ga, mut gb) = (0usize, 0usize);
    for ip in &lcs {
        // Diff the gaps between the lcs elements.
        diffs.extend(diff(&a[ga..ip[0]], &b[gb..ip[1]]));
        // Append the LCS elements to the diff.
        diffs.push(DiffLine {
            type_: DiffType::Equal,
            text: a[ip[0]],
        });
        ga = ip[0] + 1;
        gb = ip[1] + 1;
    }
    // Diff the remaining elements of a and b after the final LCS element.
    diffs.extend(diff(&a[ga..], &b[gb..]));

    diffs
}

/// LCS computes the longest common subsequence of two line
/// slices and returns the index pairs of the LCS.
fn lcs(a: &[&[u8]], b: &[&[u8]]) -> Vec<[usize; 2]> {
    // Initialize the LCS table.
    let mut lcs = vec![vec![0usize; b.len() + 1]; a.len() + 1];

    // Populate the LCS table.
    for i in 1..lcs.len() {
        for j in 1..lcs[i].len() {
            if a[i - 1] == b[j - 1] {
                lcs[i][j] = lcs[i - 1][j - 1] + 1;
            } else {
                lcs[i][j] = lcs[i - 1][j].max(lcs[i][j - 1]);
            }
        }
    }

    // Backtrack to find the LCS.
    let (mut i, mut j) = (a.len(), b.len());
    let mut s = Vec::with_capacity(lcs[i][j]);
    while i > 0 && j > 0 {
        if a[i - 1] == b[j - 1] {
            s.push([i - 1, j - 1]);
            i -= 1;
            j -= 1;
        } else if lcs[i - 1][j] > lcs[i][j - 1] {
            i -= 1;
        } else {
            j -= 1;
        }
    }

    s.reverse();
    s
}

/// Hunk represents a subsection of a diff.
#[derive(Clone, Debug)]
pub struct Hunk<'l> {
    pub diffs: Vec<DiffLine<'l>>,
    pub src_start: usize,
    pub src_lines: usize,
    pub dst_start: usize,
    pub dst_lines: usize,
}

/// makeHunks returns the hunks of a diff.
fn make_hunks<'l>(diffs: &[DiffLine<'l>], precontext: usize, postcontext: usize) -> Vec<Hunk<'l>> {
    if diffs.is_empty() {
        return Vec::new();
    }

    let mut hunks: Vec<Hunk> = Vec::new();

    // Update hunks with a diff block.
    // Go: `updateHunks := func(block Hunk, lastBlock bool)` — block is a
    // value copy; the port takes it by reference, same effect.
    fn update_hunks<'l>(
        hunks: &mut Vec<Hunk<'l>>,
        block: &Hunk<'l>,
        last_block: bool,
        precontext: usize,
        postcontext: usize,
    ) {
        // Go: `curHunk := len(hunks) - 1` — captured before any push below,
        // so after appending a new hunk the index is stale and the
        // SrcStart/DstStart fixup still targets the previous hunk. Ported
        // bug-for-bug (usize::MAX when hunks is empty is never indexed —
        // the equal/empty and modified/empty branches push instead).
        let cur_hunk = hunks.len().wrapping_sub(1);
        if block.diffs[0].type_ == DiffType::Equal {
            // Unmodified block.
            if hunks.is_empty() {
                // Start a new hunk with the tail of the block.
                let ctx_len = precontext.min(block.diffs.len());
                hunks.push(Hunk {
                    diffs: block.diffs[block.diffs.len() - ctx_len..].to_vec(),
                    src_start: block.diffs.len() - ctx_len + block.src_start,
                    src_lines: ctx_len,
                    dst_start: block.diffs.len() - ctx_len + block.dst_start,
                    dst_lines: ctx_len,
                });
            } else {
                // Update the current hunk.
                let mut max_non_context = precontext + postcontext;
                if last_block {
                    max_non_context = postcontext;
                }
                if block.diffs.len() <= max_non_context {
                    // Block is small enough to be appended to the current hunk.
                    hunks[cur_hunk].diffs.extend_from_slice(&block.diffs);
                    hunks[cur_hunk].src_lines += block.diffs.len();
                    hunks[cur_hunk].dst_lines += block.diffs.len();
                } else {
                    // Append the head of the block to the current hunk.
                    hunks[cur_hunk]
                        .diffs
                        .extend_from_slice(&block.diffs[..postcontext]);
                    hunks[cur_hunk].src_lines += postcontext;
                    hunks[cur_hunk].dst_lines += postcontext;
                    if !last_block {
                        // Start a new hunk with the tail of the block.
                        hunks.push(Hunk {
                            diffs: block.diffs[block.diffs.len() - precontext..].to_vec(),
                            src_start: block.diffs.len() - precontext + block.src_start,
                            src_lines: precontext,
                            dst_start: block.diffs.len() - precontext + block.dst_start,
                            dst_lines: precontext,
                        });
                    }
                }
                // Update starting line numbers if the current hunk had no source or destination diff.
                if hunks[cur_hunk].src_start == 0 {
                    hunks[cur_hunk].src_start = block.src_start;
                }
                if hunks[cur_hunk].dst_start == 0 {
                    hunks[cur_hunk].dst_start = block.dst_start;
                }
            }
        } else {
            // Modified block.
            if !hunks.is_empty() {
                hunks[cur_hunk].diffs.extend_from_slice(&block.diffs);
                hunks[cur_hunk].src_lines += block.src_lines;
                hunks[cur_hunk].dst_lines += block.dst_lines;
            } else {
                hunks.push(Hunk {
                    diffs: block.diffs.clone(),
                    src_start: block.src_start,
                    src_lines: block.src_lines,
                    dst_start: block.dst_start,
                    dst_lines: block.dst_lines,
                });
            }
        }
    }

    // Aggregate blocks of modified and unmodified diff lines, creating
    // or updating hunks after each block.
    let mut block: Hunk = Hunk {
        diffs: Vec::new(),
        src_start: 0,
        src_lines: 0,
        dst_start: 0,
        dst_lines: 0,
    };
    let mut modified_lines = 0usize;
    let (mut src_line_num, mut dst_line_num) = (0usize, 0usize);
    for &l in diffs {
        if block.diffs.is_empty()
            || block.diffs[0].type_ == l.type_
            || (block.diffs[0].type_ != DiffType::Equal && l.type_ != DiffType::Equal)
        {
            block.diffs.push(l);
        } else {
            update_hunks(&mut hunks, &block, false, precontext, postcontext);
            block = Hunk {
                diffs: vec![l],
                src_start: 0,
                src_lines: 0,
                dst_start: 0,
                dst_lines: 0,
            };
        }

        match l.type_ {
            DiffType::Delete => {
                src_line_num += 1;
                block.src_lines += 1;
                modified_lines += 1;
            }
            DiffType::Insert => {
                dst_line_num += 1;
                block.dst_lines += 1;
                modified_lines += 1;
            }
            DiffType::Equal => {
                src_line_num += 1;
                dst_line_num += 1;
                block.src_lines += 1;
                block.dst_lines += 1;
            }
        }

        if block.src_start == 0 && (l.type_ == DiffType::Equal || l.type_ == DiffType::Delete) {
            block.src_start = src_line_num;
        }
        if block.dst_start == 0 && (l.type_ == DiffType::Equal || l.type_ == DiffType::Insert) {
            block.dst_start = dst_line_num;
        }
    }
    update_hunks(&mut hunks, &block, true, precontext, postcontext);

    // Return no hunks if the diffs contain only equal lines.
    if modified_lines == 0 {
        return Vec::new();
    }

    hunks
}

/// UnifiedDiffOptions represents the options for [unified_diff_text_with_options].
#[derive(Debug)]
pub struct UnifiedDiffOptions<'a> {
    /// Precontext is the number of lines of context before each change in a hunk.
    pub precontext: usize,
    /// Postcontext is the number of lines of context after each change in a hunk.
    pub postcontext: usize,
    /// SrcHeader is the header for the source file.
    pub src_header: &'a str,
    /// DstHeader is the header for the destination file.
    pub dst_header: &'a str,
}

/// typeSymbol returns the associated symbol of a DiffType.
fn type_symbol(t: DiffType) -> u8 {
    match t {
        DiffType::Equal => b' ',
        DiffType::Insert => b'+',
        DiffType::Delete => b'-',
    }
}

/// UnifiedDiffTextWithOptions returns the diff text in unidiff format.
pub fn unified_diff_text_with_options(
    diffs: &[DiffLine<'_>],
    opts: &UnifiedDiffOptions<'_>,
) -> Vec<u8> {
    let hunks = make_hunks(diffs, opts.precontext, opts.postcontext);
    let mut s: Vec<Vec<u8>> = Vec::new();
    if !opts.src_header.is_empty() {
        s.push(format!("--- {}", opts.src_header).into_bytes());
    }
    if !opts.dst_header.is_empty() {
        s.push(format!("+++ {}", opts.dst_header).into_bytes());
    }
    for h in &hunks {
        s.push(
            format!(
                "@@ -{},{} +{},{} @@",
                h.src_start, h.src_lines, h.dst_start, h.dst_lines
            )
            .into_bytes(),
        );
        for l in &h.diffs {
            if l.type_ == DiffType::Equal && l.text.is_empty() {
                s.push(Vec::new());
            } else {
                let mut line = Vec::with_capacity(l.text.len() + 1);
                line.push(type_symbol(l.type_));
                line.extend_from_slice(l.text);
                s.push(line);
            }
        }
    }
    s.join(&b"\n"[..])
}
