// Ported from tsc/internal/core/pattern.go @ ec47d33c23e464a17cdf2475632cba629bee8763

#[derive(Clone, Default, Debug)]
pub struct Pattern {
    pub text: String,
    /// -1 for exact match
    pub star_index: i32,
}

impl Pattern {
    pub fn is_valid(&self) -> bool {
        self.star_index == -1 || (self.star_index as usize) < self.text.len()
    }

    pub fn matches(&self, candidate: &str) -> bool {
        if self.star_index == -1 {
            return self.text == candidate;
        }
        let star_index = self.star_index as usize;
        candidate.len() >= self.text.len() - 1
            && candidate.starts_with(&self.text[..star_index])
            && candidate.ends_with(&self.text[star_index + 1..])
    }

    pub fn matched_text<'a>(&self, candidate: &'a str) -> &'a str {
        if !self.matches(candidate) {
            panic!("candidate does not match pattern");
        }
        if self.star_index == -1 {
            return "";
        }
        let star_index = self.star_index as usize;
        // PORT: Go computes `len(candidate)-len(p.Text)+p.StarIndex+1` in
        // signed ints; reordered to avoid usize underflow (identical result
        // — a matched candidate is always long enough).
        &candidate[star_index..candidate.len() + star_index + 1 - self.text.len()]
    }
}

// PORT: Go returns the zero value of T when there is no match; Rust returns
// Option<T>.
pub fn find_best_pattern_match<T: Clone>(
    values: &[T],
    get_pattern: impl Fn(&T) -> Pattern,
    candidate: &str,
) -> Option<T> {
    let mut best_pattern = None;
    let mut longest_match_prefix_length = -1i32;
    for value in values {
        let pattern = get_pattern(value);
        if (pattern.star_index == -1 || pattern.star_index > longest_match_prefix_length)
            && pattern.matches(candidate)
        {
            best_pattern = Some(value.clone());
            longest_match_prefix_length = pattern.star_index;
        }
    }
    best_pattern
}

pub fn try_parse_pattern(pattern: &str) -> Pattern {
    let star_index = pattern.find('*').map(|i| i as i32).unwrap_or(-1);
    if star_index == -1 || !pattern[star_index as usize + 1..].contains('*') {
        return Pattern {
            text: pattern.to_string(),
            star_index,
        };
    }
    Pattern::default()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pattern_overlapping_match() {
        let p = try_parse_pattern("ab*ab");
        assert!(!p.matches("ab"), "expected 'ab' not to match 'ab*ab'");
        assert!(p.matches("abXab"), "expected 'abXab' to match 'ab*ab'");
        assert_eq!(p.matched_text("abXab"), "X", "MatchedText");
        assert!(p.matches("abab"), "expected 'abab' to match 'ab*ab'");
        assert_eq!(p.matched_text("abab"), "", "MatchedText want empty");
    }
}
