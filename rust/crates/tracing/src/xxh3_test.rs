// Tests for the XXH3-64 port in `xxh3.rs`.
//
// Vectors were generated with the reference `xxhash` implementation and
// verified identical to the Go `zeebo/xxh3` package used by
// `tsc/internal/tracing`, covering every length class: 0, 1-3, 4-8, 9-16,
// 17-128, 129-240 (mid-size), and >240 (long, including multi-block and
// partial-stripe paths).

use crate::xxh3::xxh3_64;

#[test]
fn test_xxh3_64_known_vectors() {
    let cases: &[(usize, u64)] = &[
        (0, 0x2d06800538d394c2),
        (1, 0x4a4139caf4136257),
        (2, 0x571a2ebb238829bb),
        (3, 0x505118c313121c0e),
        (4, 0x3f6889ef166b4ad1),
        (7, 0x21d5b4b6d43277e2),
        (8, 0x93f1200f9be82671),
        (9, 0x05b2fd4d97edcdae),
        (15, 0xc01ae71cb4542755),
        (16, 0x2e4359e2a04a5e32),
        (17, 0xf60c53684bbc489d),
        (31, 0xa2ee08c196bd0790),
        (32, 0x664864df0876efc6),
        (33, 0xaa998d6131d956aa),
        (64, 0x8e7464ffdf82c775),
        (100, 0x5e0be2de8640a64c),
        (128, 0x5c6ab7b5b2360539),
        (129, 0x45fabbd183de7649),
        (160, 0x46209d72c7d8e02f),
        (200, 0x43ecce5b9e53d9db),
        (240, 0xc0796428068cd12e),
        (241, 0x859dc8ab6dd85c7c),
        (256, 0x2998c04a18028d12),
        (500, 0x61934600ec4c195d),
        (1024, 0x7df7f049c0c1ad73),
        (1030, 0xa7c347e70ccb3eca),
        (2000, 0x1ef96df628dab43c),
        (3000, 0x1319ce9bcc3d4650),
    ];
    for (len, expected) in cases {
        let data: Vec<u8> = (0..*len).map(|i| ((i * 37 + 11) & 0xFF) as u8).collect();
        assert_eq!(xxh3_64(&data), *expected, "len {len}");
    }
}

#[test]
fn test_xxh3_64_thread_id_inputs() {
    // The exact strings `stable_trace_thread_id` hashes.
    assert_eq!(xxh3_64(b"file:/a.ts"), 0xb81d63866592966e);
    assert_eq!(xxh3_64(b"file:/b.ts"), 0xd5ad15b2ece1eeff);
    assert_eq!(xxh3_64(b"checker:0"), 0x994e11d764a07de0);
    assert_eq!(xxh3_64(b"file:"), 0x7fa30d135189f6fd);
    assert_eq!(xxh3_64(b"hello"), 0x9555e8555c62dcfd);
}
