// Fuzz corpus checker for the SPEC M1 jsnum gate — pairs with
// `scripts/jsnum-fuzz-gen.mjs` (Node oracle). Mirrors Go's FuzzStringJS:
//   1. Number::string(n) == JS ""+n                 (byte-for-byte)
//   2. from_string(our_str) IEEE-equals JS +str     (round-trip)
//   3. JS-parse of our string IEEE-equals the input n
// IEEE equality per assertEqualNumber: NaN==NaN, and -0.0 == +0.0 (f64 ==).
//
// Usage: cargo run --release -p tsc-jsnum --example fuzzcheck -- corpus.tsv
use tsc_jsnum::{Number, from_string};

fn ieee_eq(a: f64, b: f64) -> bool {
    (a.is_nan() && b.is_nan()) || a == b
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: fuzzcheck <corpus.tsv>");
    let text = std::fs::read_to_string(&path).expect("read corpus");
    let mut n_cases = 0u64;
    let mut mismatches = 0u64;

    for (line_no, line) in text.lines().enumerate() {
        let mut cols = line.split('\t');
        let (Some(in_hex), Some(js_str), Some(js_parse_hex)) =
            (cols.next(), cols.next(), cols.next())
        else {
            eprintln!("malformed corpus line {}", line_no + 1);
            mismatches += 1;
            continue;
        };
        let in_bits = u64::from_str_radix(in_hex, 16).unwrap();
        let js_parse_bits = u64::from_str_radix(js_parse_hex, 16).unwrap();
        let n = Number(f64::from_bits(in_bits));

        // 1. Our Number::string must match JS ""+n byte-for-byte.
        let our_str = n.string();
        if our_str != js_str {
            eprintln!(
                "string mismatch bits={in_hex}: ours={our_str:?} js={js_str:?}"
            );
            mismatches += 1;
        }

        // 2. JS's parse of our string must equal the original input.
        let js_roundtrip = f64::from_bits(js_parse_bits);
        if !ieee_eq(n.0, js_roundtrip) {
            eprintln!(
                "js round-trip mismatch bits={in_hex} str={our_str:?}: \
                 js_parse={js_roundtrip:?}"
            );
            mismatches += 1;
        }

        // 3. Our from_string of our own string must agree with JS's parse
        //    (and hence with the input).
        if !ieee_eq(from_string(&our_str).0, js_roundtrip) {
            eprintln!(
                "from_string mismatch bits={in_hex} str={our_str:?}: \
                 ours={:?} js={js_roundtrip:?}",
                from_string(&our_str).0
            );
            mismatches += 1;
        }
        n_cases += 1;
    }

    if mismatches > 0 {
        eprintln!("fuzzcheck: {mismatches} mismatches in {n_cases} cases");
        std::process::exit(1);
    }
    println!("fuzzcheck: {n_cases} cases, 0 mismatches");
}
