// Ported from tsc/internal/lsp/lsproto/structcodec.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// structcodec.go is a reflection-driven object decoder: it reads `lsp:` tags,
// tracks required fields with a bitmask, rejects explicit `null` on nilable
// (pointer/slice/map) fields unless tagged `lsp:"nullable"`, skips unknown
// fields, and defers discriminated-union fields seen before the discriminator.
//
// PORT: Rust has no reflection over serde metadata, so gen.py compiles the
// equivalent behavior directly into each type's `UnmarshalerFrom` /
// `Deserialize` impl in lsp_generated.rs. What remains here is the shared
// runtime support those impls call:

use std::io;

use serde::Deserialize;
use serde::de::DeserializeOwned;
use tsc_json as json;

/// `structDecoder.field`'s decode step: `json.UnmarshalDecode(dec, &field)`
/// where the Go field is `*T`/`[]T`/`map[...]T` — `null` collapses to the
/// field's zero value (rejectNull has already run for non-nullable fields).
pub(crate) fn decode_member<R, T>(dec: &mut json::Decoder<R>) -> Result<T, serde_json::Error>
where
    R: io::Read,
    T: DeserializeOwned + Default,
{
    Ok(json::unmarshal_decode::<R, Option<T>>(dec, &[])?.unwrap_or_default())
}

/// `omitzero` predicate — Go's `IsZero` / reflect zero check. Covers numeric,
/// string, bool, enum newtypes, collections, and `Resolved*` structs (all of
/// which derive `Default + PartialEq`). `Option` fields use `is_none` instead.
pub(crate) fn is_zero<T: Default + PartialEq>(v: &T) -> bool {
    *v == T::default()
}

/// `func json.Unmarshal(..., &field)` where absent/`null` keep the zero value:
/// `Option::<T>::deserialize(...).unwrap_or_default()` (the same pattern the
/// jsonrpc port uses).
pub(crate) fn null_to_default<'de, D, T>(d: D) -> Result<T, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de> + Default,
{
    Ok(Option::<T>::deserialize(d)?.unwrap_or_default())
}
