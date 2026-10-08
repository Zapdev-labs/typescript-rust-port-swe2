// Ported from tsc/internal/jsnum/ryu_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

// Copyright 2018 Ulf Adams
//
// The contents of this file may be used under the terms of the Apache License,
// Version 2.0.
//
//    (See accompanying file LICENSE-Apache or copy at
//     http://www.apache.org/licenses/LICENSE-2.0)
//
// Alternatively, the contents of this file may be used under the terms of
// the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE-Boost or copy at
//     https://www.boost.org/LICENSE_1_0.txt)
//
// Unless required by applicable law or agreed to in writing, this software
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.

// Copied from https://github.com/ulfjack/ryu/blob/1264a946ba66eab320e927bfd2362e0c8580c42f/ryu/tests/d2s_test.cc
// Modified to fit Number::toString's output.

use crate::jsnum_test::number_from_bits;
use crate::string_test::StringTest;
use crate::Number;

pub(crate) fn ieee_parts2_double(sign: bool, ieee_exponent: u32, ieee_mantissa: u64) -> Number {
    if ieee_exponent > 2047 {
        panic!("ieeeExponent > 2047");
    }
    if ieee_mantissa > MAX_MANTISSA {
        panic!("ieeeMantissa > maxMantissa");
    }
    let mut sign_bit = 0u64;
    if sign {
        sign_bit = 1;
    }
    number_from_bits((sign_bit << 63) | ((ieee_exponent as u64) << 52) | ieee_mantissa)
}

pub(crate) const MAX_MANTISSA: u64 = (1 << 53) - 1;

pub(crate) static RYU_TESTS: &[StringTest] = &[
    StringTest { number: Number(2.2250738585072014e-308), r#str: "2.2250738585072014e-308" },
    StringTest { number: number_from_bits(0x7fefffffffffffff), r#str: "1.7976931348623157e+308" },
    StringTest { number: number_from_bits(1), r#str: "5e-324" },
    StringTest { number: Number(2.98023223876953125e-8), r#str: "2.9802322387695312e-8" },
    StringTest { number: Number(-2.109808898695963e16), r#str: "-21098088986959630" },
    StringTest { number: Number(4.940656e-318), r#str: "4.940656e-318" },
    StringTest { number: Number(1.18575755e-316), r#str: "1.18575755e-316" },
    StringTest { number: Number(2.989102097996e-312), r#str: "2.989102097996e-312" },
    StringTest { number: Number(9.0608011534336e15), r#str: "9060801153433600" },
    StringTest { number: Number(4.708356024711512e18), r#str: "4708356024711512000" },
    StringTest { number: Number(9.409340012568248e18), r#str: "9409340012568248000" },
    StringTest { number: Number(1.2345678), r#str: "1.2345678" },
    StringTest { number: number_from_bits(0x4830F0CF064DD592), r#str: "5.764607523034235e+39" },
    StringTest { number: number_from_bits(0x4840F0CF064DD592), r#str: "1.152921504606847e+40" },
    StringTest { number: number_from_bits(0x4850F0CF064DD592), r#str: "2.305843009213694e+40" },
    StringTest { number: Number(1.2), r#str: "1.2" },
    StringTest { number: Number(1.23), r#str: "1.23" },
    StringTest { number: Number(1.234), r#str: "1.234" },
    StringTest { number: Number(1.2345), r#str: "1.2345" },
    StringTest { number: Number(1.23456), r#str: "1.23456" },
    StringTest { number: Number(1.234567), r#str: "1.234567" },
    StringTest { number: Number(1.2345678), r#str: "1.2345678" },
    StringTest { number: Number(1.23456789), r#str: "1.23456789" },
    StringTest { number: Number(1.234567895), r#str: "1.234567895" },
    StringTest { number: Number(1.2345678901), r#str: "1.2345678901" },
    StringTest { number: Number(1.23456789012), r#str: "1.23456789012" },
    StringTest { number: Number(1.234567890123), r#str: "1.234567890123" },
    StringTest { number: Number(1.2345678901234), r#str: "1.2345678901234" },
    StringTest { number: Number(1.23456789012345), r#str: "1.23456789012345" },
    StringTest { number: Number(1.234567890123456), r#str: "1.234567890123456" },
    StringTest { number: Number(1.2345678901234567), r#str: "1.2345678901234567" },
    StringTest { number: Number(4.294967294), r#str: "4.294967294" },
    StringTest { number: Number(4.294967295), r#str: "4.294967295" },
    StringTest { number: Number(4.294967296), r#str: "4.294967296" },
    StringTest { number: Number(4.294967297), r#str: "4.294967297" },
    StringTest { number: Number(4.294967298), r#str: "4.294967298" },
    StringTest { number: ieee_parts2_double(false, 4, 0), r#str: "1.7800590868057611e-307" },
    StringTest { number: ieee_parts2_double(false, 6, MAX_MANTISSA), r#str: "2.8480945388892175e-306" },
    StringTest { number: ieee_parts2_double(false, 41, 0), r#str: "2.446494580089078e-296" },
    StringTest { number: ieee_parts2_double(false, 40, MAX_MANTISSA), r#str: "4.8929891601781557e-296" },
    StringTest { number: ieee_parts2_double(false, 1077, 0), r#str: "18014398509481984" },
    StringTest { number: ieee_parts2_double(false, 1076, MAX_MANTISSA), r#str: "36028797018963964" },
    StringTest { number: ieee_parts2_double(false, 307, 0), r#str: "2.900835519859558e-216" },
    StringTest { number: ieee_parts2_double(false, 306, MAX_MANTISSA), r#str: "5.801671039719115e-216" },
    StringTest { number: ieee_parts2_double(false, 934, 0x000FA7161A4D6E0C), r#str: "3.196104012172126e-27" },
    StringTest { number: Number(9007199254740991.0), r#str: "9007199254740991" },
    StringTest { number: Number(9007199254740992.0), r#str: "9007199254740992" },
    StringTest { number: Number(1.0e+0), r#str: "1" },
    StringTest { number: Number(1.2e+1), r#str: "12" },
    StringTest { number: Number(1.23e+2), r#str: "123" },
    StringTest { number: Number(1.234e+3), r#str: "1234" },
    StringTest { number: Number(1.2345e+4), r#str: "12345" },
    StringTest { number: Number(1.23456e+5), r#str: "123456" },
    StringTest { number: Number(1.234567e+6), r#str: "1234567" },
    StringTest { number: Number(1.2345678e+7), r#str: "12345678" },
    StringTest { number: Number(1.23456789e+8), r#str: "123456789" },
    StringTest { number: Number(1.23456789e+9), r#str: "1234567890" },
    StringTest { number: Number(1.234567895e+9), r#str: "1234567895" },
    StringTest { number: Number(1.2345678901e+10), r#str: "12345678901" },
    StringTest { number: Number(1.23456789012e+11), r#str: "123456789012" },
    StringTest { number: Number(1.234567890123e+12), r#str: "1234567890123" },
    StringTest { number: Number(1.2345678901234e+13), r#str: "12345678901234" },
    StringTest { number: Number(1.23456789012345e+14), r#str: "123456789012345" },
    StringTest { number: Number(1.234567890123456e+15), r#str: "1234567890123456" },
    StringTest { number: Number(1.0e+0), r#str: "1" },
    StringTest { number: Number(1.0e+1), r#str: "10" },
    StringTest { number: Number(1.0e+2), r#str: "100" },
    StringTest { number: Number(1.0e+3), r#str: "1000" },
    StringTest { number: Number(1.0e+4), r#str: "10000" },
    StringTest { number: Number(1.0e+5), r#str: "100000" },
    StringTest { number: Number(1.0e+6), r#str: "1000000" },
    StringTest { number: Number(1.0e+7), r#str: "10000000" },
    StringTest { number: Number(1.0e+8), r#str: "100000000" },
    StringTest { number: Number(1.0e+9), r#str: "1000000000" },
    StringTest { number: Number(1.0e+10), r#str: "10000000000" },
    StringTest { number: Number(1.0e+11), r#str: "100000000000" },
    StringTest { number: Number(1.0e+12), r#str: "1000000000000" },
    StringTest { number: Number(1.0e+13), r#str: "10000000000000" },
    StringTest { number: Number(1.0e+14), r#str: "100000000000000" },
    StringTest { number: Number(1.0e+15), r#str: "1000000000000000" },
    StringTest { number: Number(1000000000000001.0), r#str: "1000000000000001" },
    StringTest { number: Number(1000000000000010.0), r#str: "1000000000000010" },
    StringTest { number: Number(1000000000000100.0), r#str: "1000000000000100" },
    StringTest { number: Number(1000000000001000.0), r#str: "1000000000001000" },
    StringTest { number: Number(1000000000010000.0), r#str: "1000000000010000" },
    StringTest { number: Number(1000000000100000.0), r#str: "1000000000100000" },
    StringTest { number: Number(1000000001000000.0), r#str: "1000000001000000" },
    StringTest { number: Number(1000000010000000.0), r#str: "1000000010000000" },
    StringTest { number: Number(1000000100000000.0), r#str: "1000000100000000" },
    StringTest { number: Number(1000001000000000.0), r#str: "1000001000000000" },
    StringTest { number: Number(1000010000000000.0), r#str: "1000010000000000" },
    StringTest { number: Number(1000100000000000.0), r#str: "1000100000000000" },
    StringTest { number: Number(1001000000000000.0), r#str: "1001000000000000" },
    StringTest { number: Number(1010000000000000.0), r#str: "1010000000000000" },
    StringTest { number: Number(1100000000000000.0), r#str: "1100000000000000" },
    StringTest { number: Number(8.0), r#str: "8" },
    StringTest { number: Number(64.0), r#str: "64" },
    StringTest { number: Number(512.0), r#str: "512" },
    StringTest { number: Number(8192.0), r#str: "8192" },
    StringTest { number: Number(65536.0), r#str: "65536" },
    StringTest { number: Number(524288.0), r#str: "524288" },
    StringTest { number: Number(8388608.0), r#str: "8388608" },
    StringTest { number: Number(67108864.0), r#str: "67108864" },
    StringTest { number: Number(536870912.0), r#str: "536870912" },
    StringTest { number: Number(8589934592.0), r#str: "8589934592" },
    StringTest { number: Number(68719476736.0), r#str: "68719476736" },
    StringTest { number: Number(549755813888.0), r#str: "549755813888" },
    StringTest { number: Number(8796093022208.0), r#str: "8796093022208" },
    StringTest { number: Number(70368744177664.0), r#str: "70368744177664" },
    StringTest { number: Number(562949953421312.0), r#str: "562949953421312" },
    StringTest { number: Number(9007199254740992.0), r#str: "9007199254740992" },
    StringTest { number: Number(8.0e+3), r#str: "8000" },
    StringTest { number: Number(64.0e+3), r#str: "64000" },
    StringTest { number: Number(512.0e+3), r#str: "512000" },
    StringTest { number: Number(8192.0e+3), r#str: "8192000" },
    StringTest { number: Number(65536.0e+3), r#str: "65536000" },
    StringTest { number: Number(524288.0e+3), r#str: "524288000" },
    StringTest { number: Number(8388608.0e+3), r#str: "8388608000" },
    StringTest { number: Number(67108864.0e+3), r#str: "67108864000" },
    StringTest { number: Number(536870912.0e+3), r#str: "536870912000" },
    StringTest { number: Number(8589934592.0e+3), r#str: "8589934592000" },
    StringTest { number: Number(68719476736.0e+3), r#str: "68719476736000" },
    StringTest { number: Number(549755813888.0e+3), r#str: "549755813888000" },
    StringTest { number: Number(8796093022208.0e+3), r#str: "8796093022208000" },
];
