// Ported from tsc/internal/project/ata/validatepackagename.go @ ec47d33c23e464a17cdf2475632cba629bee8763

/// `type NameValidationResult int`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NameValidationResult {
    NameOk,
    EmptyName,
    NameTooLong,
    NameStartsWithDot,
    NameStartsWithUnderscore,
    NameContainsNonURISafeCharacters,
}

pub const MAX_PACKAGE_NAME_LENGTH: usize = 214;

/// `url.QueryEscape` — escapes every byte that is not RFC 3986 "unreserved"
/// (`[A-Za-z0-9\-_.~]`); space becomes `+`. Go operates on the raw UTF-8 bytes,
/// so a byte-wise implementation matches it exactly (including for non-ASCII).
fn query_escape(s: &str) -> String {
    fn is_unreserved(b: u8) -> bool {
        matches!(b, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~')
    }
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        if is_unreserved(b) {
            out.push(b as char);
        } else if b == b' ' {
            out.push('+');
        } else {
            out.push('%');
            out.push(HEX[(b >> 4) as usize] as char);
            out.push(HEX[(b & 0xF) as usize] as char);
        }
    }
    out
}

/// `func ValidatePackageName(packageName string) (result NameValidationResult, name string, isScopeName bool)`
///
/// Validates package name using rules defined at https://docs.npmjs.com/files/package.json
pub fn validate_package_name(package_name: &str) -> (NameValidationResult, String, bool) {
    validate_package_name_worker(package_name, true)
}

fn validate_package_name_worker(
    package_name: &str,
    support_scoped_package: bool,
) -> (NameValidationResult, String, bool) {
    let package_name_len = package_name.len();
    if package_name_len == 0 {
        return (NameValidationResult::EmptyName, String::new(), false);
    }
    if package_name_len > MAX_PACKAGE_NAME_LENGTH {
        return (NameValidationResult::NameTooLong, String::new(), false);
    }
    let first_char = package_name.chars().next().unwrap();
    if first_char == '.' {
        return (NameValidationResult::NameStartsWithDot, String::new(), false);
    }
    if first_char == '_' {
        return (
            NameValidationResult::NameStartsWithUnderscore,
            String::new(),
            false,
        );
    }
    // check if name is scope package like: starts with @ and has one '/' in the middle
    if support_scoped_package {
        if let Some(without_scope) = package_name.strip_prefix('@') {
            if let Some((scope, scoped_package_name)) = without_scope.split_once('/') {
                if !scope.is_empty()
                    && !scoped_package_name.is_empty()
                    && !scoped_package_name.contains('/')
                {
                    let (scope_result, _, _) = validate_package_name_worker(scope, false);
                    if scope_result != NameValidationResult::NameOk {
                        return (scope_result, scope.to_string(), true);
                    }
                    let (package_result, _, _) =
                        validate_package_name_worker(scoped_package_name, false);
                    if package_result != NameValidationResult::NameOk {
                        return (package_result, scoped_package_name.to_string(), false);
                    }
                    return (NameValidationResult::NameOk, String::new(), false);
                }
            }
        }
    }
    if query_escape(package_name) != package_name {
        return (
            NameValidationResult::NameContainsNonURISafeCharacters,
            String::new(),
            false,
        );
    }
    (NameValidationResult::NameOk, String::new(), false)
}

/// `func renderPackageNameValidationFailure(...) string`
pub fn render_package_name_validation_failure(
    typing: &str,
    result: NameValidationResult,
    name: &str,
    is_scope_name: bool,
) -> String {
    let kind = if is_scope_name { "Scope" } else { "Package" };
    let name = if name.is_empty() { typing } else { name };
    match result {
        NameValidationResult::EmptyName => {
            format!("'{typing}':: {kind} name '{name}' cannot be empty")
        }
        NameValidationResult::NameTooLong => format!(
            "'{typing}':: {kind} name '{name}' should be less than {MAX_PACKAGE_NAME_LENGTH} characters"
        ),
        NameValidationResult::NameStartsWithDot => {
            format!("'{typing}':: {kind} name '{name}' cannot start with '.'")
        }
        NameValidationResult::NameStartsWithUnderscore => {
            format!("'{typing}':: {kind} name '{name}' cannot start with '_'")
        }
        NameValidationResult::NameContainsNonURISafeCharacters => {
            format!("'{typing}':: {kind} name '{name}' contains non URI safe characters")
        }
        NameValidationResult::NameOk => panic!("Unexpected Ok result"),
    }
}
