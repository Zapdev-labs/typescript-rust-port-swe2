// Ported from tsc/internal/core/textchange.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::text::TextRange;
use std::ops::Deref;

pub struct TextChange {
    // PORT: Go embeds TextRange (promoting Pos/End/etc.); Deref gives the
    // same promoted-method access on TextChange.
    pub text_range: TextRange,
    pub new_text: String,
}

impl Deref for TextChange {
    type Target = TextRange;

    fn deref(&self) -> &TextRange {
        &self.text_range
    }
}

impl TextChange {
    pub fn apply_to(&self, text: &str) -> String {
        let mut result = String::with_capacity(text.len() + self.new_text.len());
        result.push_str(&text[..self.pos() as usize]);
        result.push_str(&self.new_text);
        result.push_str(&text[self.end() as usize..]);
        result
    }
}

pub fn apply_bulk_edits(text: &str, edits: &[TextChange]) -> String {
    let mut b = String::with_capacity(text.len());
    let mut last_end = 0usize;
    for e in edits {
        let start = e.text_range.pos() as usize;
        if start != last_end {
            b.push_str(&text[last_end..e.text_range.pos() as usize]);
        }
        b.push_str(&e.new_text);

        last_end = e.text_range.end() as usize;
    }
    b.push_str(&text[last_end..]);

    b
}
