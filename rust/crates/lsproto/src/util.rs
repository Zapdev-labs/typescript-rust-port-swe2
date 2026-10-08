// Ported from tsc/internal/lsp/lsproto/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::lsp_generated::{Diagnostic, IntegerOrString, Position, Range, StringOrMarkupContent};

/// `func ComparePositions(pos, other Position) int`
///
/// Implements a cmp.Compare-like function for two `Position`s;
/// `compare_positions(&pos, &other)` orders by line, then character.
pub fn compare_positions(pos: &Position, other: &Position) -> i32 {
    pos.line
        .cmp(&other.line)
        .then(pos.character.cmp(&other.character)) as i32
}

/// `func CompareRanges(lsRange, other Range) int` — `start` before `end`.
pub fn compare_ranges(ls_range: &Range, other: &Range) -> i32 {
    let start = compare_positions(&ls_range.start, &other.start);
    if start != 0 {
        return start;
    }
    compare_positions(&ls_range.end, &other.end)
}

impl StringOrMarkupContent {
    /// `func (m StringOrMarkupContent) AsString() string` — the plain text,
    /// reading the `MarkupContent` value when the arm is not a plain string.
    pub fn as_string(&self) -> &str {
        if let Some(s) = &self.string {
            return s;
        }
        if let Some(mc) = &self.markup_content {
            return mc.value.as_str();
        }
        ""
    }
}

impl IntegerOrString {
    /// `func (m IntegerOrString) AsString() string` — the string arm, the
    /// integer rendered with `strconv.Itoa`, or `"-1"` when unset.
    pub fn as_string(&self) -> String {
        if let Some(s) = &self.string {
            s.clone()
        } else if let Some(i) = &self.integer {
            i.to_string()
        } else {
            "-1".to_string()
        }
    }
}

fn diagnostic_exists_in_slice<'a>(elem: &Diagnostic, diags: &'a [&'a Diagnostic]) -> bool {
    diags.iter().any(|d| diagnostics_equal(elem, d))
}

fn diagnostics_equal(diag1: &Diagnostic, diag2: &Diagnostic) -> bool {
    // PORT: Go nil-derefs `code1`/`code2` when `Code` is absent; `unwrap`
    // preserves the panic.
    diagnostic_codes_equal(diag1.code.as_ref().unwrap(), diag2.code.as_ref().unwrap())
        && diagnostic_messages_equal(&diag1.message, &diag2.message)
        && compare_ranges(&diag1.range, &diag2.range) == 0
}

fn diagnostic_codes_equal(code1: &IntegerOrString, code2: &IntegerOrString) -> bool {
    if let (Some(a), Some(b)) = (&code1.string, &code2.string) {
        return a == b;
    }
    if let (Some(a), Some(b)) = (&code1.integer, &code2.integer) {
        return a == b;
    }
    false
}

fn diagnostic_messages_equal(
    message1: &StringOrMarkupContent,
    message2: &StringOrMarkupContent,
) -> bool {
    if let (Some(a), Some(b)) = (&message1.string, &message2.string) {
        return a == b;
    }
    if let (Some(a), Some(b)) = (&message1.markup_content, &message2.markup_content) {
        return a.kind == b.kind && a.value == b.value;
    }
    false
}

/// `func CompareDiagnostics(list1, list2 []*Diagnostic) ([]*Diagnostic, []*Diagnostic)`
///
/// Returns `(missing_from_list1, missing_from_list2)` — elements present in
/// one list but not the other.
pub fn compare_diagnostics<'a>(
    list1: &'a [&'a Diagnostic],
    list2: &'a [&'a Diagnostic],
) -> (Vec<&'a Diagnostic>, Vec<&'a Diagnostic>) {
    let mut missing_from_list1 = Vec::new();
    let mut missing_from_list2 = Vec::new();
    for elem in list1 {
        if !diagnostic_exists_in_slice(elem, list2) {
            missing_from_list2.push(*elem);
        }
    }
    for elem in list2 {
        if !diagnostic_exists_in_slice(elem, list1) {
            missing_from_list1.push(*elem);
        }
    }
    (missing_from_list1, missing_from_list2)
}

impl Diagnostic {
    /// `func (elem *Diagnostic) AsString() string`
    ///
    /// PORT: `elem.Code` nil-derefs when absent — `unwrap` preserves the panic.
    pub fn as_string(&self) -> String {
        format!(
            "{} ({}:{}-{}:{}): {}",
            self.code.as_ref().unwrap().as_string(),
            self.range.start.line,
            self.range.start.character,
            self.range.end.line,
            self.range.end.character,
            self.message.as_string(),
        )
    }

    /// `func (elem *Diagnostic) CodeAsString() string`
    pub fn code_as_string(&self) -> String {
        format!("Code({})", self.code.as_ref().unwrap().as_string())
    }
}
