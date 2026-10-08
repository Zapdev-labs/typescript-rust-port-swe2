// Ported from tsc/internal/jsnum/string_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

// PORT: literals are kept verbatim from the Go test vectors; excess digits
// are deliberate (they mirror the Go test data).
#![allow(clippy::excessive_precision)]

use std::fs;

use serde::{Deserialize, Serialize};

use crate::jsnum::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER, NEGATIVE_ZERO, inf, nan};
use crate::jsnum_test::{
    assert_equal_number, eval_node_script, node_exe, num_to_uint32s, number_from_bits, temp_dir,
    uint32s_to_num,
};
use crate::ryu_test::RYU_TESTS;
use crate::{Number, from_string};

#[derive(Clone, Copy)]
pub(crate) struct StringTest {
    pub number: Number,
    pub r#str: &'static str,
}

static STRING_TESTS_BASE: &[StringTest] = &[
    StringTest {
        number: nan(),
        r#str: "NaN",
    },
    StringTest {
        number: inf(1),
        r#str: "Infinity",
    },
    StringTest {
        number: inf(-1),
        r#str: "-Infinity",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0",
    },
    StringTest {
        number: NEGATIVE_ZERO,
        r#str: "0",
    },
    StringTest {
        number: Number(1.0),
        r#str: "1",
    },
    StringTest {
        number: Number(-1.0),
        r#str: "-1",
    },
    StringTest {
        number: Number(0.3),
        r#str: "0.3",
    },
    StringTest {
        number: Number(-0.3),
        r#str: "-0.3",
    },
    StringTest {
        number: Number(1.5),
        r#str: "1.5",
    },
    StringTest {
        number: Number(-1.5),
        r#str: "-1.5",
    },
    StringTest {
        number: Number(1e308),
        r#str: "1e+308",
    },
    StringTest {
        number: Number(-1e308),
        r#str: "-1e+308",
    },
    StringTest {
        number: Number(std::f64::consts::PI),
        r#str: "3.141592653589793",
    },
    StringTest {
        number: Number(-std::f64::consts::PI),
        r#str: "-3.141592653589793",
    },
    StringTest {
        number: MAX_SAFE_INTEGER,
        r#str: "9007199254740991",
    },
    StringTest {
        number: MIN_SAFE_INTEGER,
        r#str: "-9007199254740991",
    },
    StringTest {
        number: number_from_bits(0x000FFFFFFFFFFFFF),
        r#str: "2.225073858507201e-308",
    },
    StringTest {
        number: number_from_bits(0x0010000000000000),
        r#str: "2.2250738585072014e-308",
    },
    StringTest {
        number: Number(1234567.8),
        r#str: "1234567.8",
    },
    StringTest {
        number: Number(19686109595169230000.0),
        r#str: "19686109595169230000",
    },
    StringTest {
        number: Number(123.456),
        r#str: "123.456",
    },
    StringTest {
        number: Number(-123.456),
        r#str: "-123.456",
    },
    StringTest {
        number: Number(444123.0),
        r#str: "444123",
    },
    StringTest {
        number: Number(-444123.0),
        r#str: "-444123",
    },
    StringTest {
        number: Number(444123.789123456789875436),
        r#str: "444123.7891234568",
    },
    StringTest {
        number: Number(-444123.78963636363636363636),
        r#str: "-444123.7896363636",
    },
    StringTest {
        number: Number(1e21),
        r#str: "1e+21",
    },
    StringTest {
        number: Number(1e20),
        r#str: "100000000000000000000",
    },
];

// slices.Concat(stringTests, ryuTests)
fn string_tests() -> impl Iterator<Item = &'static StringTest> {
    STRING_TESTS_BASE.iter().chain(RYU_TESTS.iter())
}

#[test]
fn test_string() {
    for test in string_tests() {
        assert_eq!(test.number.string(), test.r#str);
    }
}

static FROM_STRING_TESTS: &[StringTest] = &[
    StringTest {
        number: nan(),
        r#str: "    NaN",
    },
    StringTest {
        number: inf(1),
        r#str: "Infinity    ",
    },
    StringTest {
        number: inf(-1),
        r#str: "    -Infinity",
    },
    StringTest {
        number: Number(1.0),
        r#str: "1.",
    },
    StringTest {
        number: Number(1.0),
        r#str: "1.0   ",
    },
    StringTest {
        number: Number(1.0),
        r#str: "+1",
    },
    StringTest {
        number: Number(1.0),
        r#str: "+1.",
    },
    StringTest {
        number: Number(1.0),
        r#str: "+1.0",
    },
    StringTest {
        number: nan(),
        r#str: "whoops",
    },
    StringTest {
        number: Number(0.0),
        r#str: "",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0.",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0.0",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0.0000",
    },
    StringTest {
        number: Number(0.0),
        r#str: ".0000",
    },
    StringTest {
        number: NEGATIVE_ZERO,
        r#str: "-0",
    },
    StringTest {
        number: NEGATIVE_ZERO,
        r#str: "-0.",
    },
    StringTest {
        number: NEGATIVE_ZERO,
        r#str: "-0.0",
    },
    StringTest {
        number: NEGATIVE_ZERO,
        r#str: "-.0",
    },
    StringTest {
        number: nan(),
        r#str: ".",
    },
    StringTest {
        number: nan(),
        r#str: "e",
    },
    StringTest {
        number: nan(),
        r#str: ".e",
    },
    StringTest {
        number: nan(),
        r#str: "+",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0X0",
    },
    StringTest {
        number: nan(),
        r#str: "e0",
    },
    StringTest {
        number: nan(),
        r#str: "E0",
    },
    StringTest {
        number: nan(),
        r#str: "1e",
    },
    StringTest {
        number: nan(),
        r#str: "1e+",
    },
    StringTest {
        number: nan(),
        r#str: "1e-",
    },
    StringTest {
        number: Number(1.0),
        r#str: "1e+0",
    },
    StringTest {
        number: nan(),
        r#str: "++0",
    },
    StringTest {
        number: nan(),
        r#str: "0_0",
    },
    StringTest {
        number: inf(1),
        r#str: "1e1000",
    },
    StringTest {
        number: inf(-1),
        r#str: "-1e1000",
    },
    StringTest {
        number: Number(0.0),
        r#str: ".0e0",
    },
    StringTest {
        number: nan(),
        r#str: "0e++0",
    },
    StringTest {
        number: Number(10.0),
        r#str: "0XA",
    },
    StringTest {
        number: Number(0b1010 as f64),
        r#str: "0b1010",
    },
    StringTest {
        number: Number(0b1010 as f64),
        r#str: "0B1010",
    },
    StringTest {
        number: Number(0o12 as f64),
        r#str: "0o12",
    },
    StringTest {
        number: Number(0o12 as f64),
        r#str: "0O12",
    },
    StringTest {
        number: Number(0x123456789abcdef0_u64 as f64),
        r#str: "0x123456789abcdef0",
    },
    StringTest {
        number: Number(0x123456789abcdef0_u64 as f64),
        r#str: "0X123456789ABCDEF0",
    },
    StringTest {
        number: Number(18446744073709552000.0),
        r#str: "0X10000000000000000",
    },
    StringTest {
        number: Number(18446744073709597000.0),
        r#str: "0X1000000000000A801",
    },
    StringTest {
        number: nan(),
        r#str: "0B0.0",
    },
    StringTest {
        number: Number(1.231235345083403e+91),
        r#str: "12312353450834030486384068034683603046834603806830644850340602384608368034634603680348603864",
    },
    StringTest {
        number: nan(),
        r#str: "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX8OOOOOOOOOOOOOOOOOOO",
    },
    StringTest {
        number: inf(1),
        r#str: "+Infinity",
    },
    StringTest {
        number: Number(1234.56),
        r#str: "  \t1234.56  ",
    },
    StringTest {
        number: nan(),
        r#str: "\u{200b}",
    },
    StringTest {
        number: Number(0.0),
        r#str: " ",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\n",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\r",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\r\n",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\u{2028}",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\u{2029}",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\t",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\u{b}",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\u{c}",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\u{FEFF}",
    },
    StringTest {
        number: Number(0.0),
        r#str: "\u{00A0}",
    },
    StringTest {
        number: Number(10000000000000000000.0),
        r#str: "010000000000000000000",
    },
    StringTest {
        number: nan(),
        r#str: "0x1.fffffffffffffp1023",
    }, // Make sure Go's extended float syntax doesn't work.
    StringTest {
        number: nan(),
        r#str: "0X_1FFFP-16",
    },
    StringTest {
        number: nan(),
        r#str: "1_000",
    }, // NumberToString doesn't handle underscores.
    StringTest {
        number: Number(0.0),
        r#str: "0x0",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0X0",
    },
    StringTest {
        number: nan(),
        r#str: "0xOOPS",
    },
    StringTest {
        number: Number(0xABCDEF as f64),
        r#str: "0xABCDEF",
    },
    StringTest {
        number: Number(0xABCDEF as f64),
        r#str: "0xABCDEF",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0o0",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0O0",
    },
    StringTest {
        number: nan(),
        r#str: "0o8",
    },
    StringTest {
        number: nan(),
        r#str: "0O8",
    },
    StringTest {
        number: Number(0o12345 as f64),
        r#str: "0o12345",
    },
    StringTest {
        number: Number(0o12345 as f64),
        r#str: "0O12345",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0b0",
    },
    StringTest {
        number: Number(0.0),
        r#str: "0B0",
    },
    StringTest {
        number: nan(),
        r#str: "0b2",
    },
    StringTest {
        number: nan(),
        r#str: "0b2",
    },
    StringTest {
        number: Number(0b10101 as f64),
        r#str: "0b10101",
    },
    StringTest {
        number: Number(0b10101 as f64),
        r#str: "0B10101",
    },
    StringTest {
        number: nan(),
        r#str: "1.f",
    },
    StringTest {
        number: nan(),
        r#str: "1.e",
    },
    StringTest {
        number: nan(),
        r#str: "1.0ef",
    },
    StringTest {
        number: nan(),
        r#str: "1.0e",
    },
    StringTest {
        number: nan(),
        r#str: ".f",
    },
    StringTest {
        number: nan(),
        r#str: ".e",
    },
    StringTest {
        number: nan(),
        r#str: ".0ef",
    },
    StringTest {
        number: nan(),
        r#str: ".0e",
    },
    StringTest {
        number: nan(),
        r#str: "a.f",
    },
    StringTest {
        number: nan(),
        r#str: "a.e",
    },
    StringTest {
        number: nan(),
        r#str: "a.0ef",
    },
    StringTest {
        number: nan(),
        r#str: "a.0e",
    },
];

#[test]
fn test_from_string() {
    // t.Run("stringTests")
    for test in string_tests() {
        assert_equal_number(from_string(test.r#str), test.number);
        assert_equal_number(from_string(&format!("{} ", test.r#str)), test.number);
        assert_equal_number(from_string(&format!(" {}", test.r#str)), test.number);
    }

    // t.Run("fromStringTests")
    for test in FROM_STRING_TESTS {
        assert_equal_number(from_string(test.r#str), test.number);
    }
}

#[test]
fn test_string_roundtrip() {
    for test in string_tests() {
        assert_eq!(from_string(test.r#str).string(), test.r#str);
    }
}

// PORT: extra edge cases at the decimal/exponential notation boundaries
// (-6 < n <= 21 in ECMAScript §6.1.6.1.20) beyond the Go vectors, per the
// port brief (1e-6/1e-7, 1e20/1e21, 0.1+0.2, negative zero, huge integers).
#[test]
fn test_string_boundary_cases() {
    let tests: &[StringTest] = &[
        StringTest {
            number: Number(0.1 + 0.2),
            r#str: "0.30000000000000004",
        },
        StringTest {
            number: Number(1e-6),
            r#str: "0.000001",
        },
        StringTest {
            number: Number(1e-7),
            r#str: "1e-7",
        },
        StringTest {
            number: Number(2.5e-7),
            r#str: "2.5e-7",
        },
        StringTest {
            number: Number(1.5e-6),
            r#str: "0.0000015",
        },
        StringTest {
            number: Number(1.234e-6),
            r#str: "0.000001234",
        },
        StringTest {
            number: Number(1.234e-7),
            r#str: "1.234e-7",
        },
        StringTest {
            number: Number(-1e-7),
            r#str: "-1e-7",
        },
        StringTest {
            number: Number(-2.5e-7),
            r#str: "-2.5e-7",
        },
        StringTest {
            number: Number(1e20),
            r#str: "100000000000000000000",
        },
        StringTest {
            number: Number(1e21),
            r#str: "1e+21",
        },
        StringTest {
            number: Number(-1e21),
            r#str: "-1e+21",
        },
        StringTest {
            number: Number(9.99e21),
            r#str: "9.99e+21",
        },
        StringTest {
            number: Number(1e22),
            r#str: "1e+22",
        },
        StringTest {
            number: Number(1e-21),
            r#str: "1e-21",
        },
        StringTest {
            number: Number(-1e-21),
            r#str: "-1e-21",
        },
        StringTest {
            number: Number(123456789012345680000.0),
            r#str: "123456789012345680000",
        },
        StringTest {
            number: Number(0.0001),
            r#str: "0.0001",
        },
        StringTest {
            number: Number(1e-5),
            r#str: "0.00001",
        },
        StringTest {
            number: Number(5e-324),
            r#str: "5e-324",
        },
        StringTest {
            number: NEGATIVE_ZERO,
            r#str: "0",
        },
        StringTest {
            number: Number(0.1),
            r#str: "0.1",
        },
        StringTest {
            number: Number(1.0 / 3.0),
            r#str: "0.3333333333333333",
        },
        StringTest {
            number: Number(2.0 / 3.0),
            r#str: "0.6666666666666666",
        },
        StringTest {
            number: Number(-0.1),
            r#str: "-0.1",
        },
        StringTest {
            number: Number(3.0e-7),
            r#str: "3e-7",
        },
    ];
    for test in tests {
        assert_eq!(test.number.string(), test.r#str, "input: {:?}", test.number);
        assert_eq!(
            from_string(test.r#str).string(),
            test.r#str,
            "roundtrip: {}",
            test.r#str
        );
    }
}

const STRING_JS_SCRIPT: &str = r#"
		import fs from 'fs';

		function fromBits(bits) {
			const buffer = new ArrayBuffer(8);
			(new Uint32Array(buffer))[0] = bits[0];
			(new Uint32Array(buffer))[1] = bits[1];
			return new Float64Array(buffer)[0];
		}

		function toBits(number) {
			const buffer = new ArrayBuffer(8);
			(new Float64Array(buffer))[0] = number;
			return [(new Uint32Array(buffer))[0], (new Uint32Array(buffer))[1]];
		}

		export default function(inputFile) {
			const input = JSON.parse(fs.readFileSync(inputFile, 'utf8'));

			const output = input.map((input) => ({
				str: ""+fromBits(input.bits),
				bits: toBits(+input.str),
			}));

			return output;
		};
	"#;

#[test]
fn test_string_js() {
    // PORT: Go skips via jstest.SkipIfNoNodeJS(t); here the test returns early.
    if node_exe().is_none() {
        eprintln!("skipping test_string_js: Node.js not found");
        return;
    }

    // t.Run("stringTests")
    // These tests should roundtrip both ways.
    let base: Vec<StringTest> = string_tests().copied().collect();
    if let Some(results) = get_string_results_from_js(&base) {
        for (test, (number, str_)) in base.iter().zip(results.iter()) {
            assert_equal_number(*number, test.number);
            assert_eq!(str_, test.r#str);
        }
    }

    // t.Run("fromStringTests")
    // These tests should convert the string to the same number.
    if let Some(results) = get_string_results_from_js(FROM_STRING_TESTS) {
        for (test, (number, _)) in FROM_STRING_TESTS.iter().zip(results.iter()) {
            assert_equal_number(*number, test.number);
        }
    }
}

// PORT: Go's FuzzStringJS/FuzzFromStringJS fuzz tests have no cargo-test
// equivalent; their corpus is generated at fuzz time, not checked in.

#[derive(Serialize)]
struct StringDataIn {
    bits: [u32; 2],
    r#str: &'static str,
}

#[derive(Deserialize)]
struct StringDataOut {
    bits: [u32; 2],
    r#str: String,
}

fn get_string_results_from_js(tests: &[StringTest]) -> Option<Vec<(Number, String)>> {
    node_exe()?;
    let tmpdir = temp_dir();

    let input_data: Vec<StringDataIn> = tests
        .iter()
        .map(|test| StringDataIn {
            bits: num_to_uint32s(test.number),
            r#str: test.r#str,
        })
        .collect();

    let json_input = serde_json::to_string(&input_data).unwrap();

    let json_input_path = tmpdir.join("input.json");
    fs::write(&json_input_path, &json_input).unwrap();

    let output_data: Vec<StringDataOut> = eval_node_script(
        STRING_JS_SCRIPT,
        &tmpdir,
        &[json_input_path.to_str().unwrap()],
    );
    assert_eq!(output_data.len(), tests.len());

    let _ = fs::remove_dir_all(&tmpdir);
    Some(
        output_data
            .into_iter()
            .map(|d| (uint32s_to_num(d.bits), d.r#str))
            .collect(),
    )
}
