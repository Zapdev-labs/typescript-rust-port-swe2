// Ported from tsc/internal/diagnostics @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// STUB — bootstrap shim so dependent crates (tsc-ast, …) compile before the
// full diagnostics port lands (codegen of diagnosticMessages.json +
// loc/*.generated.json, language matcher, all ~2900 messages). The wave that
// ports diagnostics for real must expand this file faithfully, keeping the
// API shape below (which mirrors diagnostics.go) and replacing `STUB_MESSAGE`
// entries with the generated table.

use std::sync::atomic::{AtomicI32, Ordering};

pub type Key = &'static str;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Category {
    Warning,
    Error,
    Suggestion,
    Message,
}

impl Category {
    pub fn name(self) -> &'static str {
        match self {
            Category::Warning => "warning",
            Category::Error => "error",
            Category::Suggestion => "suggestion",
            Category::Message => "message",
        }
    }
}

pub struct Message {
    code: i32,
    category: Category,
    key: Key,
    text: &'static str,
    reports_unnecessary: bool,
    elided_in_compatibility_pyramid: bool,
    reports_deprecated: bool,
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

    // For debugging only.
    pub fn text(&self) -> &'static str {
        self.text
    }
}

// Go's diagnostics use a small *Message with lazy identity; statics give the
// same shared-pointer semantics.

fn format(text: &str, args: &[String]) -> String {
    if args.is_empty() {
        return text.to_string();
    }
    let mut out = String::with_capacity(text.len() + args.len() * 4);
    let mut rest = text;
    while let Some(i) = rest.find('{') {
        out.push_str(&rest[..i]);
        let after = &rest[i + 1..];
        if let Some(close) = after.find('}') {
            let inner = &after[..close];
            if !inner.is_empty() && inner.bytes().all(|b| b.is_ascii_digit()) {
                let index: usize = inner.parse().unwrap_or(usize::MAX);
                if index >= args.len() {
                    panic!("Invalid formatting placeholder");
                }
                out.push_str(&args[index]);
                rest = &after[close + 1..];
                continue;
            }
        }
        out.push('{');
        rest = after;
    }
    out.push_str(rest);
    out
}

pub fn localize(_locale: &tsc_locale::Locale, message: &Message, key: Key, args: &[String]) -> String {
    let _ = key;
    format(message.text, args)
}

pub fn stringify_args(args: &[String]) -> Vec<String> {
    args.to_vec()
}

static NEXT_ADHOC: AtomicI32 = AtomicI32::new(-1);

pub fn new_adhoc_message(_message: String) -> &'static Message {
    // PORT(stub): real port returns a heap Message; for the stub we return a
    // static error message — wave 3 must implement properly.
    let _ = NEXT_ADHOC.fetch_sub(1, Ordering::Relaxed);
    static ADHOC: Message = Message {
        code: -1,
        category: Category::Error,
        key: "-1",
        text: "<adhoc>",
        reports_unnecessary: false,
        elided_in_compatibility_pyramid: false,
        reports_deprecated: false,
    };
    &ADHOC
}

// Messages referenced by crates that landed before the real table existed.

pub static X_RESOLUTION_MODE_SHOULD_BE_EITHER_REQUIRE_OR_IMPORT: Message = Message {
    code: 1453,
    category: Category::Error,
    key: "resolution_mode_should_be_either_require_or_import_1453",
    text: "resolution-mode should be either require or import.",
    reports_unnecessary: false,
    elided_in_compatibility_pyramid: false,
    reports_deprecated: false,
};

pub static X_0_IS_DECLARED_HERE: Message = Message {
    code: 2728,
    category: Category::Error,
    key: "_0_is_declared_here_2728",
    text: "'{0}' is declared here.",
    reports_unnecessary: false,
    elided_in_compatibility_pyramid: false,
    reports_deprecated: false,
};

pub static CANNOT_FIND_NAME_0: Message = Message {
    code: 2304,
    category: Category::Error,
    key: "Cannot_find_name_0_2304",
    text: "Cannot find name '{0}'.",
    reports_unnecessary: false,
    elided_in_compatibility_pyramid: false,
    reports_deprecated: false,
};
