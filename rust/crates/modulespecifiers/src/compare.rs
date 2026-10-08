// Ported from tsc/internal/modulespecifiers/compare.go @ ec47d33c23e464a17cdf2475632cba629bee8763

/// `func CountPathComponents(path string) int`.
pub fn count_path_components(path: &str) -> i32 {
    let initial = if path.starts_with("./") { 2 } else { 0 };
    path[initial..].matches('/').count() as i32
}
