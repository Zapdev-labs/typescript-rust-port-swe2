// Ported from tsc/internal/jsnum/jsnum_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

// PORT: literals are kept verbatim from the Go test vectors; excess digits
// are deliberate (they mirror the Go test data).
#![allow(clippy::excessive_precision)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

use serde::{Deserialize, Serialize};

use crate::Number;
use crate::jsnum::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER, NEGATIVE_ZERO, inf, nan};

pub(crate) fn assert_equal_number(got: Number, want: Number) {
    if got.is_nan() || want.is_nan() {
        assert_eq!(got.is_nan(), want.is_nan(), "got: {}, want: {}", got, want);
    } else {
        assert_eq!(got, want, "got: {}, want: {}", got, want);
    }
}

// assertWithinOneULP checks that got and want are either equal or differ by
// at most 1 ULP (unit in the last place).
pub(crate) fn assert_within_one_ulp(got: Number, want: Number) {
    if got.is_nan() || want.is_nan() {
        assert_eq!(got.is_nan(), want.is_nan(), "got: {}, want: {}", got, want);
        return;
    }

    if got == want {
        return;
    }

    let got_bits = number_to_bits(got);
    let want_bits = number_to_bits(want);
    if got_bits == want_bits {
        return;
    }

    let ulp_dist = got_bits.abs_diff(want_bits);

    assert!(
        ulp_dist <= 1,
        "got {} ({:016x}), want {} ({:016x}) within 1 ULP (off by {} ULPs)",
        got,
        got_bits,
        want,
        want_bits,
        ulp_dist
    );
}

pub(crate) const fn number_from_bits(b: u64) -> Number {
    Number(f64::from_bits(b))
}

pub(crate) fn number_to_bits(n: Number) -> u64 {
    n.0.to_bits()
}

#[derive(Serialize)]
struct BinaryInput {
    x: [u32; 2],
    y: [u32; 2],
}

#[derive(Deserialize)]
struct BinaryResult {
    #[allow(dead_code)]
    x: [u32; 2],
    #[allow(dead_code)]
    y: [u32; 2],
    result: [u32; 2],
}

#[derive(Serialize)]
struct UnaryInput {
    x: [u32; 2],
}

#[derive(Deserialize)]
struct UnaryResult {
    #[allow(dead_code)]
    x: [u32; 2],
    result: [u32; 2],
}

pub(crate) fn num_to_uint32s(n: Number) -> [u32; 2] {
    let bits = number_to_bits(n);
    [bits as u32, (bits >> 32) as u32]
}

pub(crate) fn uint32s_to_num(a: [u32; 2]) -> Number {
    let bits = (a[0] as u64) | ((a[1] as u64) << 32);
    number_from_bits(bits)
}

// PORT: Go's jstest helpers (EvalNodeScript/SkipIfNoNodeJS) run a Node.js
// script in a temp dir and unmarshal its JSON output; ported below. Go's
// t.Skip becomes "return no results": callers skip the Node assertions.

const LOADER_SCRIPT: &str = r#"import script from "./script.mjs";
process.stdout.write(JSON.stringify(await script(...process.argv.slice(2))));"#;

pub(crate) fn node_exe() -> Option<&'static str> {
    static NODE_EXE: OnceLock<Option<&'static str>> = OnceLock::new();
    *NODE_EXE.get_or_init(|| {
        Command::new("node")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
            .then_some("node")
    })
}

pub(crate) fn temp_dir() -> PathBuf {
    static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "tsc-jsnum-test-{}-{}",
        std::process::id(),
        NEXT_ID.fetch_add(1, AtomicOrdering::Relaxed)
    ));
    fs::create_dir_all(&dir).expect("failed to create temp dir");
    dir
}

pub(crate) fn eval_node_script<T: serde::de::DeserializeOwned>(
    script: &str,
    dir: &Path,
    args: &[&str],
) -> T {
    let exe = node_exe().expect("Node.js not found");
    let script_path = dir.join("script.mjs");
    fs::write(&script_path, script).expect("failed to write script.mjs");
    let loader_path = dir.join("loader.mjs");
    fs::write(&loader_path, LOADER_SCRIPT).expect("failed to write loader.mjs");

    let output = Command::new(exe)
        .arg(&loader_path)
        .args(args)
        .current_dir(dir)
        .output()
        .expect("failed to run node");
    assert!(
        output.status.success(),
        "failed to run node:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    serde_json::from_slice(&output.stdout).expect("failed to unmarshal JSON output")
}

const BINARY_OP_SCRIPT: &str = r#"
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
			return input.map(({x, y}) => {
				const a = fromBits(x);
				const b = fromBits(y);
				return { x, y, result: toBits(%s) };
			});
		}
	"#;

const UNARY_OP_SCRIPT: &str = r#"
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
			return input.map(({x}) => {
				const a = fromBits(x);
				return { x, result: toBits(%s) };
			});
		}
	"#;

// evalBinaryOp evaluates a binary JS expression on all cases using Node.js.
// Returns None if Node.js is not available (Go: skips the calling test).
fn eval_binary_op(op: &str, xs: &[Number], ys: &[Number]) -> Option<Vec<Number>> {
    node_exe()?;

    let tmpdir = temp_dir();
    let inputs: Vec<BinaryInput> = xs
        .iter()
        .zip(ys.iter())
        .map(|(&x, &y)| BinaryInput {
            x: num_to_uint32s(x),
            y: num_to_uint32s(y),
        })
        .collect();

    let json_input = serde_json::to_string(&inputs).unwrap();

    let input_path = tmpdir.join("input.json");
    fs::write(&input_path, &json_input).unwrap();

    let script = BINARY_OP_SCRIPT.replace("%s", op);

    let results: Vec<BinaryResult> =
        eval_node_script(&script, &tmpdir, &[input_path.to_str().unwrap()]);
    assert_eq!(results.len(), xs.len());

    let _ = fs::remove_dir_all(&tmpdir);
    Some(results.iter().map(|r| uint32s_to_num(r.result)).collect())
}

// evalUnaryOp evaluates a unary JS expression on all cases using Node.js.
// Returns None if Node.js is not available (Go: skips the calling test).
fn eval_unary_op(op: &str, xs: &[Number]) -> Option<Vec<Number>> {
    node_exe()?;

    let tmpdir = temp_dir();
    let inputs: Vec<UnaryInput> = xs
        .iter()
        .map(|&x| UnaryInput {
            x: num_to_uint32s(x),
        })
        .collect();

    let json_input = serde_json::to_string(&inputs).unwrap();

    let input_path = tmpdir.join("input.json");
    fs::write(&input_path, &json_input).unwrap();

    let script = UNARY_OP_SCRIPT.replace("%s", op);

    let results: Vec<UnaryResult> =
        eval_node_script(&script, &tmpdir, &[input_path.to_str().unwrap()]);
    assert_eq!(results.len(), xs.len());

    let _ = fs::remove_dir_all(&tmpdir);
    Some(results.iter().map(|r| uint32s_to_num(r.result)).collect())
}

struct ToInt32Test {
    name: &'static str,
    input: Number,
    want: i32,
    // PORT: Go benchmarks (BenchmarkToInt32/BenchmarkExponentiate) are not
    // ported; the `bench` flag is kept so the table stays identical.
    #[allow(dead_code)]
    bench: bool,
}

static TO_INT32_TESTS: &[ToInt32Test] = &[
    ToInt32Test {
        name: "0.0",
        input: Number(0.0),
        want: 0,
        bench: true,
    },
    ToInt32Test {
        name: "-0.0",
        input: NEGATIVE_ZERO,
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "NaN",
        input: nan(),
        want: 0,
        bench: true,
    },
    ToInt32Test {
        name: "+Inf",
        input: inf(1),
        want: 0,
        bench: true,
    },
    ToInt32Test {
        name: "-Inf",
        input: inf(-1),
        want: 0,
        bench: true,
    },
    ToInt32Test {
        name: "MaxInt32",
        input: Number(i32::MAX as f64),
        want: i32::MAX,
        bench: false,
    },
    ToInt32Test {
        name: "MaxInt32+1",
        input: Number(i32::MAX as f64 + 1.0),
        want: i32::MIN,
        bench: true,
    },
    ToInt32Test {
        name: "MinInt32",
        input: Number(i32::MIN as f64),
        want: i32::MIN,
        bench: false,
    },
    ToInt32Test {
        name: "MinInt32-1",
        input: Number(i32::MIN as f64 - 1.0),
        want: i32::MAX,
        bench: true,
    },
    ToInt32Test {
        name: "MIN_SAFE_INTEGER",
        input: MIN_SAFE_INTEGER,
        want: 1,
        bench: false,
    },
    ToInt32Test {
        name: "MIN_SAFE_INTEGER-1",
        input: Number(MIN_SAFE_INTEGER.0 - 1.0),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "MIN_SAFE_INTEGER+1",
        input: Number(MIN_SAFE_INTEGER.0 + 1.0),
        want: 2,
        bench: false,
    },
    ToInt32Test {
        name: "MAX_SAFE_INTEGER",
        input: MAX_SAFE_INTEGER,
        want: -1,
        bench: true,
    },
    ToInt32Test {
        name: "MAX_SAFE_INTEGER-1",
        input: Number(MAX_SAFE_INTEGER.0 - 1.0),
        want: -2,
        bench: true,
    },
    ToInt32Test {
        name: "MAX_SAFE_INTEGER+1",
        input: Number(MAX_SAFE_INTEGER.0 + 1.0),
        want: 0,
        bench: true,
    },
    ToInt32Test {
        name: "-8589934590",
        input: Number(-8589934590.0),
        want: 2,
        bench: false,
    },
    ToInt32Test {
        name: "0xDEADBEEF",
        input: Number(0xDEADBEEF_u32 as f64),
        want: -559038737,
        bench: true,
    },
    ToInt32Test {
        name: "4294967808",
        input: Number(4294967808.0),
        want: 512,
        bench: false,
    },
    ToInt32Test {
        name: "-0.4",
        input: Number(-0.4),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "SmallestNonzeroFloat64",
        input: Number(5e-324),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "-SmallestNonzeroFloat64",
        input: Number(-5e-324),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "MaxFloat64",
        input: Number(f64::MAX),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "-MaxFloat64",
        input: Number(-f64::MAX),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "Largest subnormal number",
        input: number_from_bits(0x000FFFFFFFFFFFFF),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "Smallest positive normal number",
        input: number_from_bits(0x0010000000000000),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "Largest normal number",
        input: Number(f64::MAX),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "-Largest normal number",
        input: Number(-f64::MAX),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "1.0",
        input: Number(1.0),
        want: 1,
        bench: false,
    },
    ToInt32Test {
        name: "-1.0",
        input: Number(-1.0),
        want: -1,
        bench: false,
    },
    ToInt32Test {
        name: "1e308",
        input: Number(1e308),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "-1e308",
        input: Number(-1e308),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "math.Pi",
        input: Number(std::f64::consts::PI),
        want: 3,
        bench: false,
    },
    ToInt32Test {
        name: "-math.Pi",
        input: Number(-std::f64::consts::PI),
        want: -3,
        bench: false,
    },
    ToInt32Test {
        name: "math.E",
        input: Number(std::f64::consts::E),
        want: 2,
        bench: false,
    },
    ToInt32Test {
        name: "-math.E",
        input: Number(-std::f64::consts::E),
        want: -2,
        bench: false,
    },
    ToInt32Test {
        name: "0.5",
        input: Number(0.5),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "-0.5",
        input: Number(-0.5),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "0.49999999999999994",
        input: Number(0.49999999999999994),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "-0.49999999999999994",
        input: Number(-0.49999999999999994),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "0.5000000000000001",
        input: Number(0.5000000000000001),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "-0.5000000000000001",
        input: Number(-0.5000000000000001),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "2^31 + 0.5",
        input: Number(2147483648.5),
        want: -2147483648,
        bench: false,
    },
    ToInt32Test {
        name: "-2^31 - 0.5",
        input: Number(-2147483648.5),
        want: -2147483648,
        bench: false,
    },
    ToInt32Test {
        name: "2^40",
        input: Number(1099511627776.0),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "-2^40",
        input: Number(-1099511627776.0),
        want: 0,
        bench: false,
    },
    ToInt32Test {
        name: "TypeFlagsNarrowable",
        input: Number(536624127.0),
        want: 536624127,
        bench: true,
    },
];

#[test]
fn test_to_int32() {
    let inputs: Vec<Number> = TO_INT32_TESTS.iter().map(|t| t.input).collect();
    let zeros: Vec<Number> = TO_INT32_TESTS.iter().map(|_| Number(0.0)).collect();
    for test in TO_INT32_TESTS {
        let got = test.input.to_int32();
        assert_eq!(got, test.want, "{} ({})", test.name, test.input.0);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a | b", &inputs, &zeros) {
        for (i, test) in TO_INT32_TESTS.iter().enumerate() {
            assert_equal_number(Number(test.input.to_int32() as f64), js_results[i]);
        }
    }
}

#[test]
fn test_bitwise_not() {
    let tests: &[(Number, Number)] = &[
        // Original pairs: ~(-2147483649) == ~(2147483647)
        (Number(-2147483649.0), Number(-2147483648.0)),
        (Number(2147483647.0), Number(-2147483648.0)),
        // Original pairs: ~(-4294967296) == ~(0)
        (Number(-4294967296.0), Number(-1.0)),
        (Number(0.0), Number(-1.0)),
        // Original pairs: ~(2147483648) == ~(-2147483648)
        (Number(2147483648.0), Number(2147483647.0)),
        (Number(-2147483648.0), Number(2147483647.0)),
        // Original pairs: ~(4294967296) == ~(0)
        (Number(4294967296.0), Number(-1.0)),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    for (x, want) in tests {
        let got = x.bitwise_not();
        assert_equal_number(got, *want);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_unary_op("~a", &xs) {
        for (i, (x, _)) in tests.iter().enumerate() {
            assert_equal_number(x.bitwise_not(), js_results[i]);
        }
    }
}

#[test]
fn test_bitwise_and() {
    let tests: &[(Number, Number, Number)] = &[
        (Number(0.0), Number(0.0), Number(0.0)),
        (Number(0.0), Number(1.0), Number(0.0)),
        (Number(1.0), Number(0.0), Number(0.0)),
        (Number(1.0), Number(1.0), Number(1.0)),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    let ys: Vec<Number> = tests.iter().map(|t| t.1).collect();
    for (x, y, want) in tests {
        let got = x.bitwise_and(*y);
        assert_equal_number(got, *want);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a & b", &xs, &ys) {
        for (i, (x, y, _)) in tests.iter().enumerate() {
            assert_equal_number(x.bitwise_and(*y), js_results[i]);
        }
    }
}

#[test]
fn test_bitwise_or() {
    let tests: &[(Number, Number, Number)] = &[
        (Number(0.0), Number(0.0), Number(0.0)),
        (Number(0.0), Number(1.0), Number(1.0)),
        (Number(1.0), Number(0.0), Number(1.0)),
        (Number(1.0), Number(1.0), Number(1.0)),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    let ys: Vec<Number> = tests.iter().map(|t| t.1).collect();
    for (x, y, want) in tests {
        let got = x.bitwise_or(*y);
        assert_equal_number(got, *want);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a | b", &xs, &ys) {
        for (i, (x, y, _)) in tests.iter().enumerate() {
            assert_equal_number(x.bitwise_or(*y), js_results[i]);
        }
    }
}

#[test]
fn test_bitwise_xor() {
    let tests: &[(Number, Number, Number)] = &[
        (Number(0.0), Number(0.0), Number(0.0)),
        (Number(0.0), Number(1.0), Number(1.0)),
        (Number(1.0), Number(0.0), Number(1.0)),
        (Number(1.0), Number(1.0), Number(0.0)),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    let ys: Vec<Number> = tests.iter().map(|t| t.1).collect();
    for (x, y, want) in tests {
        let got = x.bitwise_xor(*y);
        assert_equal_number(got, *want);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a ^ b", &xs, &ys) {
        for (i, (x, y, _)) in tests.iter().enumerate() {
            assert_equal_number(x.bitwise_xor(*y), js_results[i]);
        }
    }
}

#[test]
fn test_signed_right_shift() {
    let tests: &[(Number, Number, Number)] = &[
        (Number(1.0), Number(0.0), Number(1.0)),
        (Number(1.0), Number(1.0), Number(0.0)),
        (Number(1.0), Number(2.0), Number(0.0)),
        (Number(1.0), Number(31.0), Number(0.0)),
        (Number(1.0), Number(32.0), Number(1.0)),
        (Number(-4.0), Number(0.0), Number(-4.0)),
        (Number(-4.0), Number(1.0), Number(-2.0)),
        (Number(-4.0), Number(2.0), Number(-1.0)),
        (Number(-4.0), Number(3.0), Number(-1.0)),
        (Number(-4.0), Number(4.0), Number(-1.0)),
        (Number(-4.0), Number(31.0), Number(-1.0)),
        (Number(-4.0), Number(32.0), Number(-4.0)),
        (Number(-4.0), Number(33.0), Number(-2.0)),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    let ys: Vec<Number> = tests.iter().map(|t| t.1).collect();
    for (x, y, want) in tests {
        let got = x.signed_right_shift(*y);
        assert_equal_number(got, *want);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a >> b", &xs, &ys) {
        for (i, (x, y, _)) in tests.iter().enumerate() {
            assert_equal_number(x.signed_right_shift(*y), js_results[i]);
        }
    }
}

#[test]
fn test_unsigned_right_shift() {
    let tests: &[(Number, Number, Number)] = &[
        (Number(1.0), Number(0.0), Number(1.0)),
        (Number(1.0), Number(1.0), Number(0.0)),
        (Number(1.0), Number(2.0), Number(0.0)),
        (Number(1.0), Number(31.0), Number(0.0)),
        (Number(1.0), Number(32.0), Number(1.0)),
        (Number(-4.0), Number(0.0), Number(4294967292.0)),
        (Number(-4.0), Number(1.0), Number(2147483646.0)),
        (Number(-4.0), Number(2.0), Number(1073741823.0)),
        (Number(-4.0), Number(3.0), Number(536870911.0)),
        (Number(-4.0), Number(4.0), Number(268435455.0)),
        (Number(-4.0), Number(31.0), Number(1.0)),
        (Number(-4.0), Number(32.0), Number(4294967292.0)),
        (Number(-4.0), Number(33.0), Number(2147483646.0)),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    let ys: Vec<Number> = tests.iter().map(|t| t.1).collect();
    for (x, y, want) in tests {
        let got = x.unsigned_right_shift(*y);
        assert_equal_number(got, *want);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a >>> b", &xs, &ys) {
        for (i, (x, y, _)) in tests.iter().enumerate() {
            assert_equal_number(x.unsigned_right_shift(*y), js_results[i]);
        }
    }
}

#[test]
fn test_left_shift() {
    let tests: &[(Number, Number, Number)] = &[
        (Number(1.0), Number(0.0), Number(1.0)),
        (Number(1.0), Number(1.0), Number(2.0)),
        (Number(1.0), Number(2.0), Number(4.0)),
        (Number(1.0), Number(31.0), Number(-2147483648.0)),
        (Number(1.0), Number(32.0), Number(1.0)),
        (Number(-4.0), Number(0.0), Number(-4.0)),
        (Number(-4.0), Number(1.0), Number(-8.0)),
        (Number(-4.0), Number(2.0), Number(-16.0)),
        (Number(-4.0), Number(3.0), Number(-32.0)),
        (Number(-4.0), Number(31.0), Number(0.0)),
        (Number(-4.0), Number(32.0), Number(-4.0)),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    let ys: Vec<Number> = tests.iter().map(|t| t.1).collect();
    for (x, y, want) in tests {
        let got = x.left_shift(*y);
        assert_equal_number(got, *want);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a << b", &xs, &ys) {
        for (i, (x, y, _)) in tests.iter().enumerate() {
            assert_equal_number(x.left_shift(*y), js_results[i]);
        }
    }
}

#[test]
fn test_remainder() {
    let tests: &[(Number, Number, Number)] = &[
        (nan(), Number(1.0), nan()),
        (Number(1.0), nan(), nan()),
        (inf(1), Number(1.0), nan()),
        (inf(-1), Number(1.0), nan()),
        (Number(123.0), inf(1), Number(123.0)),
        (Number(123.0), inf(-1), Number(123.0)),
        (Number(123.0), Number(0.0), nan()),
        (Number(123.0), NEGATIVE_ZERO, nan()),
        (Number(0.0), Number(123.0), Number(0.0)),
        (NEGATIVE_ZERO, Number(123.0), NEGATIVE_ZERO),
        // Normal cases
        (Number(10.0), Number(3.0), Number(1.0)),
        (Number(-10.0), Number(3.0), Number(-1.0)),
        (Number(10.0), Number(-3.0), Number(1.0)),
        (Number(-10.0), Number(-3.0), Number(-1.0)),
        (Number(5.5), Number(2.0), Number(1.5)),
        (Number(-5.5), Number(2.0), Number(-1.5)),
        (Number(1.0), Number(0.5), Number(0.0)),
        (Number(-1.0), Number(0.5), NEGATIVE_ZERO),
        (Number(1.5), Number(1.0), Number(0.5)),
        (Number(-1.5), Number(1.0), Number(-0.5)),
        // Edge cases that prove the bug in the manual formula:
        // The manual formula n - d*(n/d).trunc() accumulates floating-point
        // rounding errors that IEEE 754 fmod (math.Mod) avoids.
        (Number(7.0), Number(0.1), Number(7.0 % 0.1)),
        (Number(7.0), Number(0.2), Number(7.0 % 0.2)),
        (Number(7.0), Number(0.3), Number(7.0 % 0.3)),
        (Number(100.0), Number(0.3), Number(100.0 % 0.3)),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    let ys: Vec<Number> = tests.iter().map(|t| t.1).collect();
    for (x, y, want) in tests {
        let got = x.remainder(*y);
        assert_equal_number(got, *want);
    }

    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a % b", &xs, &ys) {
        for (i, (x, y, _)) in tests.iter().enumerate() {
            assert_equal_number(x.remainder(*y), js_results[i]);
        }
    }
}

#[test]
fn test_exponentiate() {
    let tests: &[(Number, Number, Number)] = &[
        (Number(2.0), Number(3.0), Number(8.0)),
        (inf(1), Number(3.0), inf(1)),
        (inf(1), Number(-5.0), Number(0.0)),
        (inf(-1), Number(3.0), inf(-1)),
        (inf(-1), Number(4.0), inf(1)),
        (inf(-1), Number(-3.0), NEGATIVE_ZERO),
        (inf(-1), Number(-4.0), Number(0.0)),
        (Number(0.0), Number(3.0), Number(0.0)),
        (Number(0.0), Number(-10.0), inf(1)),
        (NEGATIVE_ZERO, Number(3.0), NEGATIVE_ZERO),
        (NEGATIVE_ZERO, Number(4.0), Number(0.0)),
        (NEGATIVE_ZERO, Number(-3.0), inf(-1)),
        (NEGATIVE_ZERO, Number(-4.0), inf(1)),
        (Number(3.0), inf(1), inf(1)),
        (Number(-3.0), inf(1), inf(1)),
        (Number(3.0), inf(-1), Number(0.0)),
        (Number(-3.0), inf(-1), Number(0.0)),
        (nan(), Number(3.0), nan()),
        (Number(1.0), inf(1), nan()),
        (Number(1.0), inf(-1), nan()),
        (Number(-1.0), inf(1), nan()),
        (Number(-1.0), inf(-1), nan()),
        (Number(1.0), nan(), nan()),
        // Cases where math.Pow diverges from V8 by >1 ULP.
        // Expected values are the correctly-rounded IEEE 754 results
        // computed via exact integer arithmetic (big.Int).
        // Cross-engine testing (V8, SpiderMonkey, QuickJS, XS via jsvu)
        // confirmed these match the majority of JS engines.
        (
            Number(10.0),
            Number(308.0),
            number_from_bits(0x7fe1ccf385ebc8a0),
        ),
        (
            Number(5.0),
            Number(210.0),
            number_from_bits(0x5e68557f31326bbb),
        ),
        (
            Number(10.0),
            Number(200.0),
            number_from_bits(0x6974e718d7d7625a),
        ),
    ];

    let xs: Vec<Number> = tests.iter().map(|t| t.0).collect();
    let ys: Vec<Number> = tests.iter().map(|t| t.1).collect();
    for (x, y, want) in tests {
        let got = x.exponentiate(*y);
        assert_equal_number(got, *want);
    }

    // The ES spec says exponentiate is "implementation-approximated".
    // Different JS engines (V8, SpiderMonkey, JSC) use different pow
    // implementations that can differ by 1 ULP. Allow that tolerance.
    // t.Run("Node")
    if let Some(js_results) = eval_binary_op("a ** b", &xs, &ys) {
        for (i, (x, y, _)) in tests.iter().enumerate() {
            assert_within_one_ulp(x.exponentiate(*y), js_results[i]);
        }
    }
}
