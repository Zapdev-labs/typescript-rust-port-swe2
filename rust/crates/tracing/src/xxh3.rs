// Ported from github.com/zeebo/xxh3 (used by tsc/internal/tracing/tracing.go) @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `xxh3.New()` + `WriteString` + `Sum64` collapses to the one-shot
// `xxh3_64` — Go streams the same bytes into the hash. This is the standard
// XXH3-64 algorithm (default secret, seed 0) implemented in safe Rust; test
// vectors in `xxh3_test.rs` cover every length class and are verified against
// the Go implementation's output.

const PRIME32_1: u64 = 0x9E37_79B1;
const PRIME32_2: u64 = 0x85EB_CA77;
const PRIME32_3: u64 = 0xC2B2_AE3D;

const PRIME64_1: u64 = 0x9E37_79B1_85EB_CA87;
const PRIME64_2: u64 = 0xC2B2_AE3D_27D4_EB4F;
const PRIME64_3: u64 = 0x1656_67B1_9E37_79F9;
const PRIME64_4: u64 = 0x85EB_CA77_C2B2_AE63;
const PRIME64_5: u64 = 0x27D4_EB2F_1656_67C5;

const PRIME_MX1: u64 = 0x1656_6791_9E37_79F9;
const PRIME_MX2: u64 = 0x9FB2_1C65_1E98_DF25;

const MIDSIZE_MAX: usize = 240;
const MIDSIZE_LASTOFFSET: usize = 17;
const SECRET_SIZE_MIN: usize = 136;

const STRIPE_LEN: usize = 64;
const ACC_NB: usize = STRIPE_LEN / 8;
const SECRET_CONSUME_RATE: usize = 8;
const SECRET_LASTACC_START: usize = 7;
const SECRET_MERGEACCS_START: usize = 11;

/// `kSecret` — `XXH3_kSecret`, the 192-byte default secret.
const SECRET_DEFAULT: [u8; 192] = [
    0xb8, 0xfe, 0x6c, 0x39, 0x23, 0xa4, 0x4b, 0xbe, 0x7c, 0x01, 0x81, 0x2c, 0xf7, 0x21, 0xad, 0x1c,
    0xde, 0xd4, 0x6d, 0xe9, 0x83, 0x90, 0x97, 0xdb, 0x72, 0x40, 0xa4, 0xa4, 0xb7, 0xb3, 0x67, 0x1f,
    0xcb, 0x79, 0xe6, 0x4e, 0xcc, 0xc0, 0xe5, 0x78, 0x82, 0x5a, 0xd0, 0x7d, 0xcc, 0xff, 0x72, 0x21,
    0xb8, 0x08, 0x46, 0x74, 0xf7, 0x43, 0x24, 0x8e, 0xe0, 0x35, 0x90, 0xe6, 0x81, 0x3a, 0x26, 0x4c,
    0x3c, 0x28, 0x52, 0xbb, 0x91, 0xc3, 0x00, 0xcb, 0x88, 0xd0, 0x65, 0x8b, 0x1b, 0x53, 0x2e, 0xa3,
    0x71, 0x64, 0x48, 0x97, 0xa2, 0x0d, 0xf9, 0x4e, 0x38, 0x19, 0xef, 0x46, 0xa9, 0xde, 0xac, 0xd8,
    0xa8, 0xfa, 0x76, 0x3f, 0xe3, 0x9c, 0x34, 0x3f, 0xf9, 0xdc, 0xbb, 0xc7, 0xc7, 0x0b, 0x4f, 0x1d,
    0x8a, 0x51, 0xe0, 0x4b, 0xcd, 0xb4, 0x59, 0x31, 0xc8, 0x9f, 0x7e, 0xc9, 0xd9, 0x78, 0x73, 0x64,
    0xea, 0xc5, 0xac, 0x83, 0x34, 0xd3, 0xeb, 0xc3, 0xc5, 0x81, 0xa0, 0xff, 0xfa, 0x13, 0x63, 0xeb,
    0x17, 0x0d, 0xdd, 0x51, 0xb7, 0xf0, 0xda, 0x49, 0xd3, 0x16, 0x55, 0x26, 0x29, 0xd4, 0x68, 0x9e,
    0x2b, 0x16, 0xbe, 0x58, 0x7d, 0x47, 0xa1, 0xfc, 0x8f, 0xf8, 0xb8, 0xd1, 0x7a, 0xd0, 0x31, 0xce,
    0x45, 0xcb, 0x3a, 0x8f, 0x95, 0x16, 0x04, 0x28, 0xaf, 0xd7, 0xfb, 0xca, 0xbb, 0x4b, 0x40, 0x7e,
];

#[inline]
fn read_u32(data: &[u8], at: usize) -> u64 {
    u32::from_le_bytes(data[at..at + 4].try_into().unwrap()) as u64
}

#[inline]
fn read_u64(data: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(data[at..at + 8].try_into().unwrap())
}

/// `XXH64_avalanche`
#[inline]
fn xxh64_avalanche(mut h: u64) -> u64 {
    h ^= h >> 33;
    h = h.wrapping_mul(PRIME64_2);
    h ^= h >> 29;
    h = h.wrapping_mul(PRIME64_3);
    h ^= h >> 32;
    h
}

/// `XXH3_avalanche`
#[inline]
fn xxh3_avalanche(mut h: u64) -> u64 {
    h ^= h >> 37;
    h = h.wrapping_mul(PRIME_MX1);
    h ^= h >> 32;
    h
}

/// `XXH3_rrmxmx`
#[inline]
fn xxh3_rrmxmx(mut h: u64, len: usize) -> u64 {
    h ^= h.rotate_left(49) ^ h.rotate_left(24);
    h = h.wrapping_mul(PRIME_MX2);
    h ^= (h >> 35).wrapping_add(len as u64);
    h = h.wrapping_mul(PRIME_MX2);
    h ^ (h >> 28)
}

/// `XXH3_mul128_fold64`
#[inline]
fn mul128_fold64(lhs: u64, rhs: u64) -> u64 {
    let product = (lhs as u128).wrapping_mul(rhs as u128);
    (product as u64) ^ ((product >> 64) as u64)
}

/// `XXH3_mix16B` with `seed = 0`
#[inline]
fn mix16b(input: &[u8], at: usize, secret: &[u8], secret_at: usize) -> u64 {
    let input_lo = read_u64(input, at) ^ read_u64(secret, secret_at);
    let input_hi = read_u64(input, at + 8) ^ read_u64(secret, secret_at + 8);
    mul128_fold64(input_lo, input_hi)
}

// PORT: `XXH3_mix32B` is not needed: zeebo's `hashAny` uses plain 16-byte
// mixes for the 129-240 path rather than the older 32-byte `mix32B` scheme.

/// `XXH3_len_0to16_64b` with `seed = 0`
fn len_0to16(input: &[u8], secret: &[u8]) -> u64 {
    let len = input.len();
    if len > 8 {
        // `XXH3_len_9to16_64b`
        let bitflip1 = (read_u64(secret, 24) ^ read_u64(secret, 32)).wrapping_add(0);
        let bitflip2 = (read_u64(secret, 40) ^ read_u64(secret, 48)).wrapping_sub(0);
        let input_lo = read_u64(input, 0) ^ bitflip1;
        let input_hi = read_u64(input, len - 8) ^ bitflip2;
        let acc = (len as u64)
            .wrapping_add(input_lo.swap_bytes())
            .wrapping_add(input_hi)
            .wrapping_add(mul128_fold64(input_lo, input_hi));
        return xxh3_avalanche(acc);
    }
    if len >= 4 {
        // `XXH3_len_4to8_64b`
        let input1 = read_u32(input, 0);
        let input2 = read_u32(input, len - 4);
        let input64 = input2.wrapping_add(input1 << 32);
        let bitflip = (read_u64(secret, 8) ^ read_u64(secret, 16)).wrapping_sub(0);
        let keyed = input64 ^ bitflip;
        return xxh3_rrmxmx(keyed, len);
    }
    if len != 0 {
        // `XXH3_len_1to3_64b`
        let c1 = input[0] as u64;
        let c2 = input[len >> 1] as u64;
        let c3 = input[len - 1] as u64;
        let combined = (c1 << 16) + (c2 << 24) + c3 + ((len as u64) << 8);
        let bitflip = (read_u32(secret, 0) ^ read_u32(secret, 4)).wrapping_add(0);
        let keyed = combined ^ bitflip;
        return xxh64_avalanche(keyed);
    }
    xxh64_avalanche(read_u64(secret, 56) ^ read_u64(secret, 64))
}

/// `XXH3_len_17to128_64b` with `seed = 0`
fn len_17to128(input: &[u8], secret: &[u8]) -> u64 {
    let len = input.len();
    let mut acc = (len as u64).wrapping_mul(PRIME64_1);
    if len > 32 {
        if len > 64 {
            if len > 96 {
                acc = acc.wrapping_add(mix16b(input, 48, secret, 96));
                acc = acc.wrapping_add(mix16b(input, len - 64, secret, 112));
            }
            acc = acc.wrapping_add(mix16b(input, 32, secret, 64));
            acc = acc.wrapping_add(mix16b(input, len - 48, secret, 80));
        }
        acc = acc.wrapping_add(mix16b(input, 16, secret, 32));
        acc = acc.wrapping_add(mix16b(input, len - 32, secret, 48));
    }
    acc = acc.wrapping_add(mix16b(input, 0, secret, 0));
    acc = acc.wrapping_add(mix16b(input, len - 16, secret, 16));
    xxh3_avalanche(acc)
}

/// `XXH3_len_129to240_64b` with `seed = 0` — zeebo's formulation: eight
/// 16-byte mixes, an avalanche, then one mix per trailing 16-byte group,
/// then the last 16 bytes (matching `hashAny`'s `l <= 240` case).
fn len_129to240(input: &[u8], secret: &[u8]) -> u64 {
    let len = input.len();
    let mut acc = (len as u64).wrapping_mul(PRIME64_1);
    for i in 0..8 {
        acc = acc.wrapping_add(mix16b(input, 16 * i, secret, 16 * i));
    }
    acc = xxh3_avalanche(acc);
    // Trailing full 16-byte groups after the first 128 bytes; the secret
    // offset restarts at `MIDSIZE_STARTOFFSET` (i.e. i - 125 = 3 + 16k).
    let top = len & !15;
    let mut i = 128;
    while i < top {
        acc = acc.wrapping_add(mix16b(input, i, secret, i - 125));
        i += 16;
    }
    // Last 16 bytes: `SECRET_SIZE_MIN - MIDSIZE_LASTOFFSET` = 119.
    acc = acc.wrapping_add(mix16b(
        input,
        len - 16,
        secret,
        SECRET_SIZE_MIN - MIDSIZE_LASTOFFSET,
    ));
    xxh3_avalanche(acc)
}

/// `XXH3_accumulate_512_scalar` — zeebo's per-lane pairing: the even lane's
/// keyed product and the odd lane's raw value land in the same accumulator.
#[inline]
fn accumulate_512(
    acc: &mut [u64; ACC_NB],
    input: &[u8],
    at: usize,
    secret: &[u8],
    secret_at: usize,
) {
    for i in 0..ACC_NB / 2 {
        let at_i = at + 16 * i;
        let at_s = secret_at + 16 * i;
        let dv0 = read_u64(input, at_i);
        let dk0 = dv0 ^ read_u64(secret, at_s);
        let dv1 = read_u64(input, at_i + 8);
        let dk1 = dv1 ^ read_u64(secret, at_s + 8);
        acc[2 * i] = acc[2 * i]
            .wrapping_add(dv1)
            .wrapping_add((dk0 & 0xFFFF_FFFF).wrapping_mul(dk0 >> 32));
        acc[2 * i + 1] = acc[2 * i + 1]
            .wrapping_add(dv0)
            .wrapping_add((dk1 & 0xFFFF_FFFF).wrapping_mul(dk1 >> 32));
    }
}

/// `XXH3_scrambleAccScalar`
fn scramble_acc(acc: &mut [u64; ACC_NB], secret: &[u8], secret_at: usize) {
    for (i, acc64) in acc.iter_mut().enumerate() {
        *acc64 ^= *acc64 >> 47;
        *acc64 ^= read_u64(secret, secret_at + 8 * i);
        *acc64 = acc64.wrapping_mul(PRIME32_1);
    }
}

/// `XXH3_accumulate`
fn accumulate(
    acc: &mut [u64; ACC_NB],
    input: &[u8],
    mut at: usize,
    secret: &[u8],
    nb_stripes: usize,
) {
    for n in 0..nb_stripes {
        accumulate_512(acc, input, at, secret, n * SECRET_CONSUME_RATE);
        at += STRIPE_LEN;
    }
}

/// `XXH3_hashLong_internal_loop`
fn hash_long(acc: &mut [u64; ACC_NB], input: &[u8], secret: &[u8]) {
    let len = input.len();
    let nb_rounds = (secret.len() - STRIPE_LEN) / SECRET_CONSUME_RATE;
    let block_len = STRIPE_LEN * nb_rounds;
    let nb_blocks = (len - 1) / block_len;

    for b in 0..nb_blocks {
        accumulate(acc, input, b * block_len, secret, nb_rounds);
        scramble_acc(acc, secret, secret.len() - STRIPE_LEN);
    }

    // last partial block
    let nb_stripes = ((len - 1) - (block_len * nb_blocks)) / STRIPE_LEN;
    accumulate(acc, input, nb_blocks * block_len, secret, nb_stripes);

    // last stripe
    accumulate_512(
        acc,
        input,
        len - STRIPE_LEN,
        secret,
        secret.len() - STRIPE_LEN - SECRET_LASTACC_START,
    );
}

/// `XXH3_mergeAccs`
fn merge_accs(acc: &[u64; ACC_NB], secret: &[u8], secret_at: usize, start: u64) -> u64 {
    let mut result64 = start;
    for i in 0..ACC_NB / 2 {
        result64 = result64.wrapping_add(mul128_fold64(
            acc[2 * i] ^ read_u64(secret, secret_at + 16 * i),
            acc[2 * i + 1] ^ read_u64(secret, secret_at + 16 * i + 8),
        ));
    }
    xxh3_avalanche(result64)
}

/// `XXH3_64bits` — one-shot XXH3-64 with the default secret and seed 0,
/// matching `xxh3.New(); Write(...); Sum64()`.
pub fn xxh3_64(input: &[u8]) -> u64 {
    let len = input.len();
    if len <= 16 {
        return len_0to16(input, &SECRET_DEFAULT);
    }
    if len <= 128 {
        return len_17to128(input, &SECRET_DEFAULT);
    }
    if len <= MIDSIZE_MAX {
        return len_129to240(input, &SECRET_DEFAULT);
    }
    // `XXH3_hashLong_64b_default`
    let mut acc: [u64; ACC_NB] = [
        PRIME32_3, PRIME64_1, PRIME64_2, PRIME64_3, PRIME64_4, PRIME32_2, PRIME64_5, PRIME32_1,
    ];
    hash_long(&mut acc, input, &SECRET_DEFAULT);
    merge_accs(
        &acc,
        &SECRET_DEFAULT,
        SECRET_MERGEACCS_START,
        (len as u64).wrapping_mul(PRIME64_1),
    )
}
