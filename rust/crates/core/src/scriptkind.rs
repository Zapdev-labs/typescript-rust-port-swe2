// Ported from tsc/internal/core/scriptkind.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
//go:generate npx hereby generate:scriptkind

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(i32)]
pub enum ScriptKind {
    #[default]
    Unknown = 0,
    Js = 1,
    Jsx = 2,
    Ts = 3,
    Tsx = 4,

    // Value 5 is reserved (formerly ScriptKindExternal).

    Json = 6,
    // Value 7 is reserved (formerly ScriptKindDeferred).
}
