// Oracle corpus generator for the tsc-jsnum string round-trip fuzz gate
// (SPEC §M1). Mirrors tsc/internal/jsnum FuzzStringJS: for random f64 bit
// patterns emit `in_hex<TAB>String(n)<TAB>bits_hex(+str)` so the Rust side can
// assert our Number::string matches JS ""+n byte-for-byte AND that JS's
// parse of our string IEEE-equals the input.
//
// Usage: node jsnum-fuzz-gen.mjs [out.tsv] [count]
// Deterministic: seeded xorshift64*, so the corpus is reproducible.

import fs from 'node:fs';

const out = process.argv[2] ?? '/tmp/jsnum-corpus.tsv';
const count = Number(process.argv[3] ?? 1_000_000);

const buf = new ArrayBuffer(8);
const f64 = new Float64Array(buf);
const b64 = new BigUint64Array(buf);

function toBits(n) {
  f64[0] = n;
  return b64[0].toString(16).padStart(16, '0');
}

// xorshift64* — deterministic, no dependence on Math.random.
let s = 0x9e3779b97f4a7c15n;
function next64() {
  s ^= s >> 12n; s ^= (s << 25n) & 0xffff_ffff_ffff_ffffn; s ^= s >> 27n;
  return (s * 0x2545f4914f6cdd1dn) & 0xffff_ffff_ffff_ffffn;
}

const lines = [];

// Edge cases first: specials, denormals, boundaries, and prior bug
// regressions (2^-695 vicinity, 2^-25 midpoint, safe-int edges).
const edge = [
  0x0000000000000000n, 0x8000000000000000n, // ±0
  0x7ff0000000000000n, 0xfff0000000000000n, // ±Inf
  0x7ff8000000000000n, 0x7ff0000000000001n, // NaNs
  0x0000000000000001n, 0x000fffffffffffffn, // denormals
  0x0010000000000000n, 0x7fefffffffffffffn, // min normal, max finite
  0x3fd0000000000000n, 0x3fd0000000000001n, // 2^-25 midpoint region
  0x433fffffffffffffn, 0x4340000000000000n, // safe-int edge
  0x38b0000000000000n, 0x38afffffffffffffn, // ~2^-695
];
for (let i = 0; i < 0x1000; i++) edge.push(BigInt(i)); // smallest denormals
for (let i = 0; i < 0x1000; i++) edge.push(0x7fefffffffffffffn - BigInt(i)); // largest

const total = count + edge.length;
const chunks = [];
for (const bits of edge) {
  b64[0] = bits;
  const n = f64[0];
  const str = '' + n;
  chunks.push(bits.toString(16).padStart(16, '0'), '\t', str, '\t', toBits(+str), '\n');
}
for (let i = 0; i < count; i++) {
  const bits = next64();
  b64[0] = bits;
  const n = f64[0];
  const str = '' + n;
  chunks.push(bits.toString(16).padStart(16, '0'), '\t', str, '\t', toBits(+str), '\n');
}

fs.writeFileSync(out, chunks.join(''));
console.error(`jsnum-fuzz-gen: wrote ${total} cases to ${out}`);
