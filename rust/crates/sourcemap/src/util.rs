// Ported from tsc/internal/sourcemap/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::lineinfo::EcmaLineInfo;

/// `func TryGetSourceMappingURL(lineInfo *ECMALineInfo) string`
///
/// Tries to find the sourceMappingURL comment at the end of a file.
///
/// PORT: Go's `unicode.IsSpace` is the Unicode White_Space property, matching
/// `char::is_whitespace`.
pub fn try_get_source_mapping_url(line_info: Option<&EcmaLineInfo>) -> String {
    if let Some(line_info) = line_info {
        for index in (0..line_info.line_count()).rev() {
            let mut line = line_info.line_text(index);
            line = line.trim_start_matches(char::is_whitespace);
            line = line.trim_end_matches(tsc_stringutil::is_line_break);
            if line.is_empty() {
                continue;
            }
            if line.len() < 4
                || !line.starts_with("//")
                || (line.as_bytes()[2] != b'#' && line.as_bytes()[2] != b'@')
                || line.as_bytes()[3] != b' '
            {
                break;
            }
            if let Some(url) = line[4..].strip_prefix("sourceMappingURL=") {
                return url.trim_end_matches(char::is_whitespace).to_string();
            }
        }
    }
    String::new()
}
