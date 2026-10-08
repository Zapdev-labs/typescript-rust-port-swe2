// Ported from tsc/internal/diagnostics/diagnostics.go @ ec47d33c23e464a17cdf2475632cba629bee8763

//! Package diagnostics contains generated localizable diagnostic messages.

use std::collections::HashMap;
use std::fmt;
use std::sync::{OnceLock, RwLock};

use tsc_locale::Locale;

use crate::diagnostics_generated::ALL_MESSAGES;
use crate::loc_generated::{LOCALE_FUNCS, MATCHER_TAGS};

/// `type Category int32`
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum Category {
    Warning = 0,
    Error = 1,
    Suggestion = 2,
    Message = 3,
}

impl Category {
    /// `func (category Category) Name() string`
    pub fn name(self) -> &'static str {
        match self {
            Category::Warning => "warning",
            Category::Error => "error",
            Category::Suggestion => "suggestion",
            Category::Message => "message",
        }
    }
}

/// `type Key string`
pub type Key = &'static str;

/// `type Message struct`
///
/// Go's `*Message` is a shared pointer to a lazily-initialized package var;
/// the generated table is `pub static` + `&'static` refs, which gives the same
/// shared-pointer semantics. Fields are `pub(crate)` so the `include!`d
/// generated table can use struct literals.
pub struct Message {
    pub(crate) code: i32,
    pub(crate) category: Category,
    pub(crate) key: Key,
    pub(crate) text: &'static str,
    pub(crate) reports_unnecessary: bool,
    pub(crate) elided_in_compatibility_pyramid: bool,
    pub(crate) reports_deprecated: bool,
}

impl Message {
    pub fn code(&self) -> i32 {
        self.code
    }
    pub fn category(&self) -> Category {
        self.category
    }
    pub fn key(&self) -> Key {
        self.key
    }
    pub fn reports_unnecessary(&self) -> bool {
        self.reports_unnecessary
    }
    pub fn elided_in_compatibility_pyramid(&self) -> bool {
        self.elided_in_compatibility_pyramid
    }
    pub fn reports_deprecated(&self) -> bool {
        self.reports_deprecated
    }

    /// For debugging only. Go: `func (m *Message) String() string`.
    pub fn text(&self) -> &'static str {
        self.text
    }

    /// `func (m *Message) Localize(locale locale.Locale, args ...any) string`
    pub fn localize<T: fmt::Display>(&self, locale: &Locale, args: &[T]) -> String {
        localize(locale, Some(self), "", &stringify_args(args))
    }
}

/// For debugging only. Go: `func (m *Message) String() string`.
impl fmt::Display for Message {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.text)
    }
}

// Most diagnostics carry a message pointer, so only build the lookup when a key is used.
static MESSAGES_BY_KEY: OnceLock<HashMap<Key, &'static Message>> = OnceLock::new();

fn messages_by_key() -> &'static HashMap<Key, &'static Message> {
    MESSAGES_BY_KEY.get_or_init(|| {
        let mut messages = HashMap::with_capacity(ALL_MESSAGES.len());
        for &p in ALL_MESSAGES {
            messages.insert(p.key, p);
        }
        messages
    })
}

/// `func keyToMessage(key Key) *Message` — `None` is Go's nil.
pub(crate) fn key_to_message(key: Key) -> Option<&'static Message> {
    messages_by_key().get(key).copied()
}

/// `func Localize(locale locale.Locale, message *Message, key Key, args ...string) string`
///
/// `None` for `message` mirrors Go's nil: the message is then looked up by
/// `key`, panicking on an unknown key.
pub fn localize(
    locale: &Locale,
    message: Option<&Message>,
    key: Key,
    args: &[String],
) -> String {
    let message = match message.or_else(|| key_to_message(key)) {
        Some(m) => m,
        None => panic!("Unknown diagnostic message: {key}"),
    };

    let mut text = message.text;
    if let Some(localized) = get_localized_messages(locale) {
        if let Some(localized_text) = localized.get(message.key) {
            text = localized_text;
        }
    }

    format(text, args)
}

/// `var localizedMessagesCache sync.Map // map[language.Tag]map[Key]string`
///
/// The cached `Option` is Go's stored nil (`localize` caches misses too).
static LOCALIZED_MESSAGES_CACHE: RwLock<
    HashMap<String, Option<&'static HashMap<Key, String>>>,
> = RwLock::new(HashMap::new());

fn get_localized_messages(loc: &Locale) -> Option<&'static HashMap<Key, String>> {
    let tag = loc.to_string();
    if tag.is_empty() {
        // language.Und
        return None;
    }

    // Check cache first
    if let Some(cached) = LOCALIZED_MESSAGES_CACHE.read().unwrap().get(&tag) {
        return *cached;
    }

    // PORT: Go runs `matcher.Match(loc)` — golang.org/x/text/language's full
    // CLDR matcher with confidence scoring and fallback (e.g. `de` or `de-AT`
    // would match `de-DE`). We only support exact-tag matching against the
    // generated tag list; anything else falls back to English (index 0's
    // `None` entry) just like Go's low-confidence/no-match path.
    let index = MATCHER_TAGS.iter().position(|&t| t == tag);
    let messages = index
        .filter(|&i| i < LOCALE_FUNCS.len())
        .and_then(|i| LOCALE_FUNCS[i].map(|f| f()));

    LOCALIZED_MESSAGES_CACHE.write().unwrap().insert(tag, messages);
    messages
}

/// `func Format(text string, args []string) string` — replaces `{n}`
/// placeholders. Go implements this with `regexp.MustCompile("{(\d+)}")`
/// + `ReplaceAllStringFunc`; this is a hand-rolled scan of the same pattern
/// (PORT: no regex crate per repo rules).
///
/// Panics on an out-of-range placeholder index
/// ("Invalid formatting placeholder"), like Go.
pub fn format(text: &str, args: &[String]) -> String {
    if args.is_empty() {
        return text.to_string();
    }

    // Go replaces invalid UTF-8 args with U+FFFD via strings.ToValidUTF8
    // (core.SameMap). PORT: Rust `String` is always valid UTF-8, so the
    // sanitization is a no-op here.

    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len() + args.len() * 4);
    let mut last = 0; // start of the not-yet-emitted span
    let mut i = 0; // scan position
    while i < bytes.len() {
        if bytes[i] == b'{' {
            // Try to match `{(\d+)}` at i.
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 && j < bytes.len() && bytes[j] == b'}' {
                // Go: strconv.ParseInt failure (overflow) also panics here.
                let index: usize = text[i + 1..j].parse().unwrap_or(usize::MAX);
                if index >= args.len() {
                    panic!("Invalid formatting placeholder");
                }
                out.push_str(&text[last..i]);
                out.push_str(&args[index]);
                last = j + 1;
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    out.push_str(&text[last..]);
    out
}

/// `func StringifyArgs(args []any) []string`
///
/// PORT: Go distinguishes `string` args (used as-is) from others (formatted
/// with `%v`); `Display` gives the identical result for both cases.
pub fn stringify_args<T: fmt::Display>(args: &[T]) -> Vec<String> {
    if args.is_empty() {
        return Vec::new();
    }

    args.iter().map(|arg| arg.to_string()).collect()
}

/// `func NewAdHocMessage(message string) *Message`
///
/// PORT: Go returns a GC-managed `*Message`; we leak a boxed `Message` (and
/// its text) to get `&'static`. Adhoc diagnostics are rare, so the bounded
/// leak matches the statics' lifetime semantics without complicating the
/// `Message` type.
pub fn new_adhoc_message(message: String) -> &'static Message {
    Box::leak(Box::new(Message {
        code: -1,
        category: Category::Error,
        key: "-1",
        text: Box::leak(message.into_boxed_str()),
        reports_unnecessary: false,
        elided_in_compatibility_pyramid: false,
        reports_deprecated: false,
    }))
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};
    use std::fs;
    use std::path::PathBuf;

    use super::*;
    use crate::diagnostics_generated::*;

    fn must_parse(s: &str) -> Locale {
        let (locale, ok) = tsc_locale::parse(s);
        assert!(ok, "failed to parse locale {s:?}");
        locale
    }

    fn english() -> Locale {
        must_parse("en")
    }

    #[test]
    fn test_localize() {
        struct Case {
            name: &'static str,
            message: &'static Message,
            locale: Locale,
            args: Vec<String>,
            expected: &'static str,
        }

        let tests = [
            Case {
                name: "english default",
                message: &Identifier_expected,
                locale: english(),
                args: vec![],
                expected: "Identifier expected.",
            },
            Case {
                name: "undefined locale uses english",
                message: &Identifier_expected,
                locale: Locale::default(),
                args: vec![],
                expected: "Identifier expected.",
            },
            Case {
                name: "with single argument",
                message: &X_0_expected,
                locale: english(),
                args: vec![")".to_string()],
                expected: "')' expected.",
            },
            Case {
                name: "with multiple arguments",
                message: &The_parser_expected_to_find_a_1_to_match_the_0_token_here,
                locale: english(),
                args: vec!["{".to_string(), "}".to_string()],
                expected: "The parser expected to find a '}' to match the '{' token here.",
            },
            Case {
                name: "fallback to english for unknown locale",
                message: &Identifier_expected,
                locale: must_parse("af-ZA"),
                args: vec![],
                expected: "Identifier expected.",
            },
            Case {
                name: "german",
                message: &Identifier_expected,
                locale: must_parse("de-DE"),
                args: vec![],
                expected: "Es wurde ein Bezeichner erwartet.",
            },
            Case {
                name: "french",
                message: &Identifier_expected,
                locale: must_parse("fr-FR"),
                args: vec![],
                expected: "Identificateur attendu.",
            },
            Case {
                name: "spanish",
                message: &Identifier_expected,
                locale: must_parse("es-ES"),
                args: vec![],
                expected: "Se esperaba un identificador.",
            },
            Case {
                name: "japanese",
                message: &Identifier_expected,
                locale: must_parse("ja-JP"),
                args: vec![],
                expected: "識別子が必要です。",
            },
            Case {
                name: "chinese simplified",
                message: &Identifier_expected,
                locale: must_parse("zh-CN"),
                args: vec![],
                expected: "应为标识符。",
            },
            Case {
                name: "korean",
                message: &Identifier_expected,
                locale: must_parse("ko-KR"),
                args: vec![],
                expected: "식별자가 필요합니다.",
            },
            Case {
                name: "russian",
                message: &Identifier_expected,
                locale: must_parse("ru-RU"),
                args: vec![],
                expected: "Ожидался идентификатор.",
            },
            Case {
                name: "german with args",
                message: &X_0_expected,
                locale: must_parse("de-DE"),
                args: vec![")".to_string()],
                expected: "\")\" wurde erwartet.",
            },
        ];

        for tt in tests {
            let result = tt.message.localize(&tt.locale, &tt.args);
            assert_eq!(result, tt.expected, "case {:?}", tt.name);
        }
    }

    #[test]
    fn test_localize_by_key() {
        struct Case {
            name: &'static str,
            key: Key,
            locale: Locale,
            args: Vec<String>,
            expected: &'static str,
        }

        let tests = [
            Case {
                name: "by key without args",
                key: "Identifier_expected_1003",
                locale: english(),
                args: vec![],
                expected: "Identifier expected.",
            },
            Case {
                name: "by key with args",
                key: "_0_expected_1005",
                locale: english(),
                args: vec![")".to_string()],
                expected: "')' expected.",
            },
        ];

        for tt in tests {
            let result = localize(&tt.locale, None, tt.key, &tt.args);
            assert_eq!(result, tt.expected, "case {:?}", tt.name);
        }
    }

    fn loc_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../../tsc/internal/diagnostics/loc")
    }

    #[test]
    fn test_locale_files() {
        let mut files: Vec<PathBuf> = fs::read_dir(loc_dir())
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| {
                p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.ends_with(".generated.json"))
            })
            .collect();
        assert!(!files.is_empty());
        files.sort();

        for path in files {
            let locale_name = path
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .trim_end_matches(".generated.json")
                .to_string();
            let data = fs::read(&path).unwrap();
            validate_locale_file(
                &data,
                get_localized_messages(&must_parse(&locale_name)),
            );
        }
    }

    fn validate_locale_file(
        data: &[u8],
        runtime_messages: Option<&HashMap<Key, String>>,
    ) {
        let handback: BTreeMap<Key, String> = serde_json::from_slice(data).unwrap();
        validate_localized_messages(&handback);

        // Go: `expected = json.MarshalIndent(&orderedMessages, "", "  ")` then
        // LF→CRLF. serde_json pretty output has the same shape ("k": v, two
        // spaces); BTreeMap iterates sorted like the OrderedMap built from
        // slices.Sorted(maps.Keys(handback)). PORT: Go's encoder is the
        // internal tsc json package, which does not HTML-escape — matching
        // serde_json's behavior.
        let mut expected = String::from("{\r\n");
        for (i, (k, v)) in handback.iter().enumerate() {
            if i > 0 {
                expected.push_str(",\r\n");
            }
            expected.push_str("  ");
            expected.push_str(&serde_json::to_string(k).unwrap());
            expected.push_str(": ");
            expected.push_str(&serde_json::to_string(v).unwrap());
        }
        if handback.is_empty() {
            expected = "{}".to_string();
        } else {
            expected.push_str("\r\n}");
        }
        assert_eq!(
            String::from_utf8_lossy(data),
            expected,
            "handback must use sorted keys and canonical formatting"
        );

        let active: BTreeMap<Key, &String> = handback
            .iter()
            .filter(|(key, _)| key_to_message(key).is_some())
            .map(|(&k, v)| (k, v))
            .collect();
        if active.is_empty() {
            assert_eq!(runtime_messages.map_or(0, HashMap::len), 0);
        } else {
            let runtime: BTreeMap<Key, &String> = runtime_messages
                .expect("runtime messages missing for non-empty locale")
                .iter()
                .map(|(&k, v)| (k, v))
                .collect();
            assert_eq!(runtime, active);
        }
    }

    #[test]
    fn test_locale_files_ignore_stale_diagnostics() {
        // PORT: stale-key filtering happens in build.rs (Go filters at codegen
        // time too) — `runtime_messages` here is what build.rs would have
        // emitted for this synthetic handback.
        let data = b"{\r\n  \"Identifier_expected_1003\": \"Known translation.\",\r\n  \"Removed_diagnostic_99999\": \"Stale translation.\"\r\n}";
        let runtime: HashMap<Key, String> =
            [("Identifier_expected_1003", "Known translation.".to_string())]
                .into_iter()
                .collect();
        validate_locale_file(data, Some(&runtime));
        validate_locale_file(
            b"{\r\n  \"Removed_diagnostic_99999\": \"Stale translation.\"\r\n}",
            None,
        );
    }

    // PORT: TestGenerateLocalizations exercises `go run generate.go` —
    // codegen moved to build.rs (SPEC §5.8), so there is no Go program to
    // invoke; determinism is covered by build.rs itself.

    fn validate_localized_messages(localized_messages: &BTreeMap<Key, String>) {
        for (key, localized_text) in localized_messages {
            let Some(message) = key_to_message(key) else {
                continue;
            };
            let localized_placeholders = placeholder_set(localized_text);
            let english_placeholders = placeholder_set(message.text());
            assert_eq!(
                localized_placeholders.len(),
                english_placeholders.len(),
                "placeholder mismatch for {key:?}"
            );
            for placeholder in &english_placeholders {
                assert!(
                    localized_placeholders.contains(placeholder),
                    "localized diagnostic {key:?} is missing placeholder {placeholder}"
                );
            }
        }
    }

    fn placeholder_set(text: &str) -> BTreeMap<String, bool> {
        // Same `{(\d+)}` scan as `format` — collect placeholder strings.
        let bytes = text.as_bytes();
        let mut result = BTreeMap::new();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'{' {
                let mut j = i + 1;
                while j < bytes.len() && bytes[j].is_ascii_digit() {
                    j += 1;
                }
                if j > i + 1 && j < bytes.len() && bytes[j] == b'}' {
                    result.insert(text[i..=j].to_string(), true);
                    i = j + 1;
                    continue;
                }
            }
            i += 1;
        }
        result
    }

    #[test]
    fn test_generated_table_sanity() {
        // Table is sorted by code with unique codes, and every message is
        // reachable through key_to_message.
        let mut prev = None;
        for m in ALL_MESSAGES {
            if let Some(prev) = prev {
                assert!(m.code() > prev, "messages not sorted by code");
            }
            prev = Some(m.code());
            assert_eq!(key_to_message(m.key()).unwrap().code(), m.code());
            assert!(!m.text().is_empty() && !m.category().name().is_empty());
        }
    }

    #[test]
    #[should_panic(expected = "Invalid formatting placeholder")]
    fn test_format_out_of_range_panics() {
        // Go: `strconv.ParseInt` ok but index >= len(args) → panic.
        // (Empty `args` short-circuits before scanning, like Go.)
        format("{1}", &["x".to_string()]);
    }

    #[test]
    fn test_format_literals() {
        // No args → text returned verbatim, placeholders untouched.
        let no_args: Vec<String> = vec![];
        assert_eq!(format("{0}", &no_args), "{0}");

        // `{abc}` / `{0x}` are not `{\d+}` matches → left as literals.
        let args = vec!["x".to_string()];
        assert_eq!(format("{abc}", &args), "{abc}");
        assert_eq!(format("{0x}", &args), "{0x}");
        assert_eq!(format("{{0}}", &args), "{x}");

        // Scan resumes inside a non-match: `{0{1}}` → `{0` + args[1] + `}`.
        let args = vec!["x".to_string(), "y".to_string()];
        assert_eq!(format("{0{1}}", &args), "{0y}");
    }

    #[test]
    fn test_new_adhoc_message() {
        let m = new_adhoc_message("custom".to_string());
        assert_eq!(m.code(), -1);
        assert_eq!(m.category(), Category::Error);
        assert_eq!(m.key(), "-1");
        assert_eq!(m.text(), "custom");
    }
}
