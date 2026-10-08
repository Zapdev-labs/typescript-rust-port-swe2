// Ported from tsc/internal/core/binarysearch.go @ ec47d33c23e464a17cdf2475632cba629bee8763

// BinarySearchUniqueFunc works like [slices.BinarySearchFunc], but avoids extra
// invocations of the comparison function by assuming that only one element
// in the slice could match the target. Also, unlike [slices.BinarySearchFunc],
// the comparison function is passed the current index of the element being
// compared, instead of the target element.
//
// PORT: Go returns `int` indices; Rust slice indices are `usize`. The
// comparator receives the borrowed element (`&E`) rather than a copy.
pub fn binary_search_unique_func<E>(
    x: &[E],
    mut cmp: impl FnMut(usize, &E) -> i32,
) -> (usize, bool) {
    let n = x.len();
    if n == 0 {
        return (0, false);
    }
    let mut low = 0usize;
    let mut high = n - 1;
    while low <= high {
        let middle = low + ((high - low) >> 1);
        let value = cmp(middle, &x[middle]);
        if value < 0 {
            low = middle + 1;
        } else if value > 0 {
            high = middle - 1;
        } else {
            return (middle, true);
        }
    }
    (low, false)
}
