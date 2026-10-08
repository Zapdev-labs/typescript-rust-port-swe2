// Ported from tsc/internal/locale/locale.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;

/// PORT: Go threads `Locale` through `context.Context` via
/// `context.WithValue`/`ctx.Value`. Rust has no context package yet (SPEC §5.5
/// plans an explicit CancelToken + parameter threading); contexts that carry
/// a locale implement this trait so `with_locale`/`from_context`/`has_locale`
/// keep their Go shape.
pub trait LocaleContext {
    fn get_locale(&self) -> Option<Locale>;
    fn set_locale(&mut self, locale: Locale);
}

/// `type Locale language.Tag` — a canonicalized BCP-47 language tag; the zero
/// value is `Default` (Go's `language.Tag{}` == "und").
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Locale {
    tag: String,
}

/// `var Default Locale` — the zero tag.
pub const DEFAULT: Locale = Locale { tag: String::new() };

impl fmt::Display for Locale {
    /// `func (l Locale) String() string`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == DEFAULT {
            return f.write_str("");
        }
        f.write_str(&self.tag)
    }
}

/// `func WithLocale(ctx context.Context, locale Locale) context.Context`.
/// PORT: attaches by mutation — the host context type provides the storage.
pub fn with_locale<C: LocaleContext + ?Sized>(ctx: &mut C, locale: Locale) {
    ctx.set_locale(locale);
}

/// `func FromContext(ctx context.Context) Locale` — returns `Default` when no
/// locale was attached (Go's comma-ok assertion yields the zero Locale).
pub fn from_context<C: LocaleContext + ?Sized>(ctx: &C) -> Locale {
    ctx.get_locale().unwrap_or_default()
}

/// `func HasLocale(ctx context.Context) bool`
pub fn has_locale<C: LocaleContext + ?Sized>(ctx: &C) -> bool {
    ctx.get_locale().is_some()
}

/// `func Parse(localeStr string) (locale Locale, ok bool)`.
///
/// Parse gracefully fails.
///
/// PORT: golang.org/x/text/language.Parse performs full BCP-47 parsing and
/// CLDR canonicalization (extlang folding, grandfathered/deprecated-tag
/// remapping, region suppression). This port validates subtag well-formedness
/// and applies case normalization (language lower, script Title, REGION
/// upper) — sufficient for the locales the CLI accepts ("en", "en-US", ...);
/// English is the only shipped message pack anyway.
pub fn parse(locale_str: &str) -> (Locale, bool) {
    if locale_str.is_empty() || !locale_str.is_ascii() {
        return (Locale::default(), false);
    }

    let mut canon = String::with_capacity(locale_str.len());
    for (i, subtag) in locale_str.split('-').enumerate() {
        if i > 0 {
            canon.push('-');
        }
        if i == 0 {
            // Primary language subtag: 2–8 ASCII letters. "x-…" is a
            // private-use tag.
            if subtag == "x" {
                canon.push('x');
                continue;
            }
            if !(2..=8).contains(&subtag.len())
                || !subtag.bytes().all(|b| b.is_ascii_alphabetic())
            {
                return (Locale::default(), false);
            }
            canon.extend(subtag.bytes().map(|b| b.to_ascii_lowercase() as char));
            continue;
        }
        if subtag.is_empty()
            || subtag.len() > 8
            || !subtag.bytes().all(|b| b.is_ascii_alphanumeric())
        {
            return (Locale::default(), false);
        }
        let mut bytes = subtag.bytes();
        if subtag.len() == 4 && subtag.bytes().all(|b| b.is_ascii_alphabetic()) {
            // Script subtag: Titlecase.
            canon.push(bytes.next().unwrap().to_ascii_uppercase() as char);
            canon.extend(bytes.map(|b| b.to_ascii_lowercase() as char));
        } else if (subtag.len() == 2 && subtag.bytes().all(|b| b.is_ascii_alphabetic()))
            || (subtag.len() == 3 && subtag.bytes().all(|b| b.is_ascii_digit()))
        {
            // Region subtag: uppercase.
            canon.extend(subtag.bytes().map(|b| b.to_ascii_uppercase() as char));
        } else {
            canon.extend(subtag.bytes().map(|b| b.to_ascii_lowercase() as char));
        }
    }

    // A private-use tag needs at least one subtag after "x".
    if canon == "x" {
        return (Locale::default(), false);
    }

    (Locale { tag: canon }, true)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestContext {
        locale: Option<Locale>,
    }

    impl LocaleContext for TestContext {
        fn get_locale(&self) -> Option<Locale> {
            self.locale.clone()
        }

        fn set_locale(&mut self, locale: Locale) {
            self.locale = Some(locale);
        }
    }

    #[test]
    fn test_default_locale_string_is_empty() {
        assert_eq!(DEFAULT.to_string(), "");
        assert_eq!(Locale::default(), DEFAULT);
    }

    #[test]
    fn test_parse() {
        let (locale, ok) = parse("en-US");
        assert!(ok);
        assert_eq!(locale.to_string(), "en-US");

        let (locale, ok) = parse("EN-us");
        assert!(ok);
        assert_eq!(locale.to_string(), "en-US");

        let (_, ok) = parse("");
        assert!(!ok);
        let (_, ok) = parse("not a locale");
        assert!(!ok);
        let (_, ok) = parse("en_US");
        assert!(!ok);
    }

    #[test]
    fn test_context_round_trip() {
        let mut ctx = TestContext { locale: None };
        assert!(!has_locale(&ctx));
        assert_eq!(from_context(&ctx), DEFAULT);

        let (locale, ok) = parse("fr");
        assert!(ok);
        with_locale(&mut ctx, locale);
        assert!(has_locale(&ctx));
        assert_eq!(from_context(&ctx).to_string(), "fr");
    }
}
