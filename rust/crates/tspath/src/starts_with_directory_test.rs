// Ported from tsc/internal/tspath/startsWithDirectory_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::{CaseSensitivity, starts_with_directory};

struct StartsWithDirectoryTestCase {
    name: &'static str,
    file_name: &'static str,
    directory_name: &'static str,
    case_sensitivity: CaseSensitivity,
    expected: bool,
}

#[test]
fn test_starts_with_directory() {
    let tests = [
        StartsWithDirectoryTestCase {
            name: "exact match case sensitive",
            file_name: "/project/src/file.ts",
            directory_name: "/project/src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: true,
        },
        StartsWithDirectoryTestCase {
            name: "exact match case insensitive",
            file_name: "/project/src/file.ts",
            directory_name: "/PROJECT/SRC",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            expected: true,
        },
        StartsWithDirectoryTestCase {
            name: "case sensitive mismatch",
            file_name: "/project/src/file.ts",
            directory_name: "/PROJECT/SRC",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "file not in directory",
            file_name: "/project/lib/file.ts",
            directory_name: "/project/src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "file in subdirectory",
            file_name: "/project/src/components/Button.tsx",
            directory_name: "/project/src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: true,
        },
        StartsWithDirectoryTestCase {
            name: "file in parent directory",
            file_name: "/project/file.ts",
            directory_name: "/project/src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "windows style separators",
            file_name: "C:\\project\\src\\file.ts",
            directory_name: "C:\\project\\src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: true,
        },
        StartsWithDirectoryTestCase {
            name: "mixed separators",
            file_name: "/project/src/file.ts",
            directory_name: "\\project\\src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "empty directory name",
            file_name: "/project/src/file.ts",
            directory_name: "",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "empty file name",
            file_name: "",
            directory_name: "/project/src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "identical paths",
            file_name: "/project/src",
            directory_name: "/project/src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            // File name doesn't start with directory + separator
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "directory with trailing separator",
            file_name: "/project/src/file.ts",
            directory_name: "/project/src/",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: true,
        },
        StartsWithDirectoryTestCase {
            name: "unicode characters",
            file_name: "/project/测试/file.ts",
            directory_name: "/project/测试",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: true,
        },
        StartsWithDirectoryTestCase {
            name: "unicode case insensitive",
            file_name: "/project/测试/file.ts",
            directory_name: "/PROJECT/测试",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            expected: true,
        },
    ];

    for tt in &tests {
        let result = starts_with_directory(tt.file_name, tt.directory_name, tt.case_sensitivity);
        assert_eq!(
            result, tt.expected,
            "{}: starts_with_directory({:?}, {:?}, {:?})",
            tt.name, tt.file_name, tt.directory_name, tt.case_sensitivity
        );
    }
}

#[test]
fn test_starts_with_directory_edge_cases() {
    let tests = [
        StartsWithDirectoryTestCase {
            name: "file name shorter than directory",
            file_name: "/proj",
            directory_name: "/project",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "file name starts with directory but no separator",
            file_name: "/projectsrc/file.ts",
            directory_name: "/project",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
        StartsWithDirectoryTestCase {
            name: "relative paths",
            file_name: "src/file.ts",
            directory_name: "src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: true,
        },
        StartsWithDirectoryTestCase {
            name: "absolute vs relative",
            file_name: "/project/src/file.ts",
            directory_name: "project/src",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            expected: false,
        },
    ];

    for tt in &tests {
        let result = starts_with_directory(tt.file_name, tt.directory_name, tt.case_sensitivity);
        assert_eq!(
            result, tt.expected,
            "{}: starts_with_directory({:?}, {:?}, {:?})",
            tt.name, tt.file_name, tt.directory_name, tt.case_sensitivity
        );
    }
}
