// Ported from tsc/internal/core/languagevariant.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
//go:generate npx hereby generate:languagevariant

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(i32)]
pub enum LanguageVariant {
    #[default]
    Standard = 0,
    Jsx = 1,
}
