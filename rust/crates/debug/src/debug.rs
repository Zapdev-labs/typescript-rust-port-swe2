// Ported from tsc/internal/debug/debug.go @ ec47d33c23e464a17cdf2475632cba629bee8763

/// `func Fail(reason string)` — panics unconditionally in both debug and
/// release builds (SPEC §5.9: Go release binaries keep asserts; never remove
/// assertions).
pub fn fail(reason: &str) -> ! {
    let reason = if reason.is_empty() {
        "Debug failure.".to_string()
    } else {
        format!("Debug failure. {reason}")
    };
    // runtime.Breakpoint()
    panic!("{reason}");
}

/// `interface{ KindString() string }` — the argument contract of
/// `FailBadSyntaxKind` and the first arm of `AssertNever`'s detail dispatch.
pub trait KindString {
    fn kind_string(&self) -> String;
}

// PORT: lets `fail_bad_syntax_kind!(node)` accept both `Node` and `&Node`
// receivers, mirroring Go's method-set promotion on pointer arguments.
impl<T: KindString + ?Sized> KindString for &T {
    fn kind_string(&self) -> String {
        (**self).kind_string()
    }
}

/// `func FailBadSyntaxKind(node interface{ KindString() string }, message ...any)`.
///
/// PORT: the variadic `message ...any` becomes trailing macro args; the args
/// are rendered with `fmt::Display` and concatenated, matching `fmt.Sprint`
/// (which only inserts spaces between two adjacent non-string operands — a
/// divergence that does not occur in any existing call site).
#[macro_export]
macro_rules! fail_bad_syntax_kind {
    ($node:expr) => {
        $crate::fail_bad_syntax_kind(
            $crate::debug::KindString::kind_string(&$node),
            ::std::option::Option::None,
        )
    };
    ($node:expr, $($message:expr),+ $(,)?) => {{
        let mut message = ::std::string::String::new();
        $(
            ::std::fmt::Write::write_fmt(&mut message, ::std::format_args!("{}", $message))
                .unwrap();
        )+
        $crate::fail_bad_syntax_kind(
            $crate::debug::KindString::kind_string(&$node),
            ::std::option::Option::Some(message),
        )
    }};
}

/// `func FailBadSyntaxKind` body. Call through the `fail_bad_syntax_kind!`
/// macro, which adapts Go's variadic signature.
#[doc(hidden)]
pub fn fail_bad_syntax_kind(node_kind: String, message: Option<String>) -> ! {
    let msg = match message {
        None => "Unexpected node.".to_string(),
        Some(message) => message,
    };
    fail(&format!("{msg}\nNode {node_kind} was unexpected."));
}

/// `func AssertNever(member any, message ...any)`.
///
/// PORT: Go dispatches on `interface{ KindString() string }`, then
/// `fmt.Stringer`, then `%v`. Rust has no runtime interface checks, so the
/// member is rendered with `fmt::Display` — types carrying a `KindString()`
/// should implement `Display` delegating to `kind_string()` (the same result,
/// since no ported type implements both differently).
#[macro_export]
macro_rules! assert_never {
    ($member:expr) => {
        $crate::assert_never(::std::format!("{}", $member), ::std::option::Option::None)
    };
    ($member:expr, $($message:expr),+ $(,)?) => {{
        let mut message = ::std::string::String::new();
        $(
            ::std::fmt::Write::write_fmt(&mut message, ::std::format_args!("{}", $message))
                .unwrap();
        )+
        $crate::assert_never(
            ::std::format!("{}", $member),
            ::std::option::Option::Some(message),
        )
    }};
}

/// `func AssertNever` body. Call through the `assert_never!` macro, which
/// adapts Go's variadic signature.
#[doc(hidden)]
pub fn assert_never(member: String, message: Option<String>) -> ! {
    let msg = match message {
        None => "Illegal value:".to_string(),
        Some(message) => message,
    };
    fail(&format!("{msg} {member}"));
}

/// `func Assert(value bool, message ...any)` — fires in BOTH debug and release
/// builds (SPEC §5.9); this is not a `debug_assert!`.
#[macro_export]
macro_rules! assert_ {
    ($value:expr) => {
        if !($value) {
            $crate::assert_slow(::std::option::Option::None)
        }
    };
    ($value:expr, $($message:expr),+ $(,)?) => {{
        if !($value) {
            let mut message = ::std::string::String::new();
            $(
                ::std::fmt::Write::write_fmt(&mut message, ::std::format_args!("{}", $message))
                    .unwrap();
            )+
            $crate::assert_slow(::std::option::Option::Some(message))
        }
    }};
}

/// `func assertSlow(message ...any)` — the cold failure path of `Assert`.
/// Exported for the `assert_!` macro; not part of the public API.
#[doc(hidden)]
pub fn assert_slow(message: Option<String>) -> ! {
    // See https://dave.cheney.net/2020/05/02/mid-stack-inlining-in-go
    let msg = match message {
        Some(message) => format!("False expression: {message}"),
        None => "False expression.".to_string(),
    };
    fail(&msg);
}

// PORT: Go's `debug.Assert(x)` / `debug.AssertNever(m)` / `debug.FailBadSyntaxKind(n)`
// call shape is `debug::assert_!(x)` / `debug::assert_never!(m)` /
// `debug::fail_bad_syntax_kind!(n)` — the `#[macro_export]` macros live at
// the crate root, so `use tsc_debug as debug;` is the intended import.

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt;

    struct MockNode {
        kind: &'static str,
    }

    impl KindString for MockNode {
        fn kind_string(&self) -> String {
            self.kind.to_string()
        }
    }

    // PORT: AssertNever renders members via Display; mockNode's Go dispatch
    // hit KindString first, so its Display delegates to kind_string().
    impl fmt::Display for MockNode {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str(&self.kind_string())
        }
    }

    struct MockStringer {
        s: &'static str,
    }

    impl fmt::Display for MockStringer {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str(self.s)
        }
    }

    #[test]
    #[should_panic(expected = "Debug failure.")]
    fn test_fail_empty_reason() {
        fail("");
    }

    #[test]
    #[should_panic(expected = "Debug failure. something went wrong")]
    fn test_fail_with_reason() {
        fail("something went wrong");
    }

    #[test]
    #[should_panic(expected = "Debug failure. Unexpected node.\nNode FooNode was unexpected.")]
    fn test_fail_bad_syntax_kind_no_message() {
        fail_bad_syntax_kind!(MockNode { kind: "FooNode" });
    }

    #[test]
    #[should_panic(expected = "Debug failure. custom message\nNode BarNode was unexpected.")]
    fn test_fail_bad_syntax_kind_with_message() {
        fail_bad_syntax_kind!(MockNode { kind: "BarNode" }, "custom message");
    }

    #[test]
    #[should_panic(expected = "Debug failure. Illegal value: TestNode")]
    fn test_assert_never_default_message_kind_string() {
        assert_never!(MockNode { kind: "TestNode" });
    }

    #[test]
    #[should_panic(expected = "Debug failure. bad value: TestNode")]
    fn test_assert_never_custom_message_kind_string() {
        assert_never!(MockNode { kind: "TestNode" }, "bad value:");
    }

    #[test]
    #[should_panic(expected = "Debug failure. Illegal value: hello")]
    fn test_assert_never_stringer() {
        assert_never!(MockStringer { s: "hello" });
    }

    #[test]
    #[should_panic(expected = "Debug failure. Illegal value: 42")]
    fn test_assert_never_fallback() {
        assert_never!(42);
    }

    #[test]
    fn test_assert_true() {
        assert_!(true);
    }

    #[test]
    fn test_assert_true_with_message() {
        assert_!(true, "this should not trigger");
    }

    #[test]
    #[should_panic(expected = "Debug failure. False expression.")]
    fn test_assert_false_no_message() {
        assert_!(false);
    }

    #[test]
    #[should_panic(expected = "Debug failure. False expression: expected x > 0")]
    fn test_assert_false_with_message() {
        assert_!(false, "expected x > 0");
    }
}
