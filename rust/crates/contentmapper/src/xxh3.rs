// Ported from github.com/zeebo/xxh3 (the XXH3-128 implementation
// tsc/internal/contentmapper uses for transform identities).
//
// PORT: `xxh3.Uint128` becomes `Uint128 { hi, lo }`; `Uint128.Bytes()` is
// `Uint128::bytes()` (big-endian hi-then-lo, as Go's Uint128.Bytes). The
// hash itself is provided by the `xxhash-rust` crate — XXH3-128 is a
// canonical algorithm, so `xxhash_rust::xxh3::xxh3_128` produces
// byte-identical output to zeebo's Go port (verified by the reference
// vectors in the test below).

/// `type u128 struct` — the 128-bit result of [`hash_128`].
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct Uint128 {
    /// `u128.Hi`
    pub hi: u64,
    /// `u128.Lo`
    pub lo: u64,
}

impl Uint128 {
    /// `(u Uint128) Bytes()` — the 16-byte big-endian representation.
    pub fn bytes(&self) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&self.hi.to_be_bytes());
        out[8..].copy_from_slice(&self.lo.to_be_bytes());
        out
    }
}

/// `func Hash128(b []byte) Uint128`
pub fn hash_128(data: &[u8]) -> Uint128 {
    let h = ::xxhash_rust::xxh3::xxh3_128(data);
    Uint128 {
        hi: (h >> 64) as u64,
        lo: h as u64,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Vectors produced by `github.com/zeebo/xxh3` v1.1.0 `Hash128` (the Go
    /// dependency this ports) on the same inputs.
    #[test]
    fn hash128_matches_go_reference() {
        let cases: &[(&[u8], u64, u64)] = &[
            (b"", 0x99aa06d3014798d8, 0x6001c324468d497f),
            (b"a", 0xa96faf705af16834, 0xe6c632b61e964e1f),
            (b"hello", 0xb5e9c1ad071b3e7f, 0xc779cfaa5e523818),
            (b"0123456789abcdef0", 0x4d011b9cf16c97fc, 0x259d04103128b07b),
            (
                b"0123456789abcdef0123456789abcdef",
                0xcc9c4d5512a05c72,
                0xfe5f6378a7825dff,
            ),
            (
                b"vue@1.0.0\x00{\"strictTemplates\":true}\x00{\"target\":7,\"strict\":true}",
                0x9883916ff215779b,
                0xf7366561ace63500,
            ),
            (
                b"vue (vue@1.0.0)\x00\x00config:{\"a\":1}\x00\xff\xfe binary \x00\x01",
                0x6ea58d4cf8f6f7b6,
                0xf60e7b7ff92dbae9,
            ),
        ];
        for (input, hi, lo) in cases {
            let h = hash_128(input);
            assert_eq!((h.hi, h.lo), (*hi, *lo), "input {input:?}");
        }
        for (n, byte, hi, lo) in [
            (129usize, b'x', 0xe7f1abc92bce4135u64, 0xae9ec8f29e5baa27u64),
            (241, b'y', 0x9542183325e41bab, 0x97295e4657a9e196),
            (500, b'z', 0x864a8587b4a675f3, 0x0ff9839e0d749249),
            (3000, b'w', 0x454dce9e0f5fa02f, 0x66e61a9ca034ebe1),
            (10000, b'v', 0xcc12595389e72eda, 0x2d66b38f43a585f7),
        ] {
            let input = vec![byte; n];
            let h = hash_128(&input);
            assert_eq!((h.hi, h.lo), (hi, lo), "len {n}");
        }
    }
}
