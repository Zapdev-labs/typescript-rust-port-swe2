// Ported from tsc/internal/core/text.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// TextPos
//
// Positions are UTF-8 byte offsets into source text, identical to the Go port.

pub type TextPos = i32;

// TextRange

#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct TextRange {
    pos: TextPos,
    end: TextPos,
}

impl TextRange {
    pub fn new(pos: i32, end: i32) -> TextRange {
        TextRange { pos, end }
    }

    pub fn undefined() -> TextRange {
        TextRange { pos: -1, end: -1 }
    }

    pub fn pos(&self) -> i32 {
        self.pos
    }

    pub fn end(&self) -> i32 {
        self.end
    }

    // PORT: Go's TextRange has no IsEmpty; keep the API faithful.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> i32 {
        self.end - self.pos
    }

    pub fn is_valid(&self) -> bool {
        self.pos >= 0 || self.end >= 0
    }

    pub fn contains(&self, pos: i32) -> bool {
        pos >= self.pos && pos < self.end
    }

    pub fn contains_inclusive(&self, pos: i32) -> bool {
        pos >= self.pos && pos <= self.end
    }

    pub fn contains_exclusive(&self, pos: i32) -> bool {
        self.pos < pos && pos < self.end
    }

    pub fn with_pos(&self, pos: i32) -> TextRange {
        TextRange { pos, end: self.end }
    }

    pub fn with_end(&self, end: i32) -> TextRange {
        TextRange { pos: self.pos, end }
    }

    pub fn contained_by(&self, t2: &TextRange) -> bool {
        t2.pos <= self.pos && t2.end >= self.end
    }

    pub fn overlaps(&self, t2: &TextRange) -> bool {
        let start = self.pos.max(t2.pos);
        let end = self.end.min(t2.end);
        start < end
    }

    // Similar to overlaps, but treats touching ranges as intersecting.
    // For example, [0, 5) intersects [5, 10).
    pub fn intersects(&self, t2: &TextRange) -> bool {
        let start = self.pos.max(t2.pos);
        let end = self.end.min(t2.end);
        start <= end
    }
}

pub fn compare_text_ranges(r1: &TextRange, r2: &TextRange) -> i32 {
    let c = r1.pos.wrapping_sub(r2.pos);
    if c != 0 {
        return c;
    }
    r1.end.wrapping_sub(r2.end)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_range_basics() {
        let r = TextRange::new(5, 10);
        assert_eq!(r.pos(), 5);
        assert_eq!(r.end(), 10);
        assert_eq!(r.len(), 5);
        assert!(r.is_valid());
        assert!(!TextRange::undefined().is_valid());

        assert!(r.contains(5));
        assert!(r.contains(9));
        assert!(!r.contains(10));
        assert!(r.contains_inclusive(10));
        assert!(!r.contains_exclusive(5));
        assert!(r.contains_exclusive(7));

        assert_eq!(r.with_pos(1).pos(), 1);
        assert_eq!(r.with_end(20).end(), 20);
    }

    #[test]
    fn text_range_relations() {
        let r = TextRange::new(5, 10);
        assert!(r.contained_by(&TextRange::new(0, 15)));
        assert!(!r.contained_by(&TextRange::new(6, 15)));

        assert!(r.overlaps(&TextRange::new(9, 20)));
        assert!(!r.overlaps(&TextRange::new(10, 20))); // touching is not overlapping
        assert!(r.intersects(&TextRange::new(10, 20))); // but is intersecting

        assert_eq!(
            compare_text_ranges(&TextRange::new(1, 5), &TextRange::new(3, 4)),
            -2
        );
        assert_eq!(
            compare_text_ranges(&TextRange::new(1, 5), &TextRange::new(1, 7)),
            -2
        );
        assert_eq!(compare_text_ranges(&r, &r), 0);
    }
}
