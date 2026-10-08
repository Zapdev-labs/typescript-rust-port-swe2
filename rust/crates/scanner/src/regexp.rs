// Ported from tsc/internal/scanner/regexp.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's `regExpParser` borrows the caller's `*Scanner` and both reads its
// state (pos/end/tokenValue/tokenStart/tokenFlags/scriptTarget) and calls its
// methods (char/charAt/charAndSize/errorAt/scanIdentifier/scanEscapeSequence/
// scanUnicodeEscape/...). Those Scanner methods live in scanner.go, which is
// ported separately. Until scanner.rs lands and reconciles, the parser owns
// the subset of scanner state it needs and carries private ports of the
// required Scanner helpers — see the "Scanner helpers" section at the bottom.
// The flag-scanning loop of `Scanner.ReScanSlashToken` (scanner.go) is also
// ported here as `scan_regular_expression_flags` since it only consumes the
// flag tables defined in this file.
//
// PORT: strings returned by the scan helpers are `Vec<u8>` rather than
// `String`/`&str`: Go strings hold arbitrary bytes, and lone UTF-16
// surrogates are preserved via tsc-stringutil's CESU-8 sentinel encoding
// (encode_js_string_rune/decode_js_string_rune), which is not valid UTF-8.
// Positions remain byte offsets into the UTF-8 source text, as in Go.

// No non-test caller exists yet (scanner.rs is being ported in parallel), so
// the pub(crate) Scanner surface below would otherwise warn as dead code.
#![allow(dead_code)]

use std::cmp::Ordering;
use std::fmt;

use tsc_ast::TokenFlags;
use tsc_collections::Set;
use tsc_core::core::get_spelling_suggestion_for_strings;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::ScriptTarget;
use tsc_debug as debug;
use tsc_diagnostics::{self as diagnostics, Message};
use tsc_stringutil as stringutil;

use crate::unicodeproperties::{
    NON_BINARY_UNICODE_PROPERTY_NAMES, is_binary_unicode_property,
    is_binary_unicode_property_of_strings, is_general_category_value, non_binary_unicode_property,
    values_of_non_binary_unicode_property,
};

/// `type regularExpressionFlags int32`
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct RegularExpressionFlags(pub i32);

impl RegularExpressionFlags {
    pub const NONE: Self = Self(0);
    /// d
    pub const HAS_INDICES: Self = Self(1 << 0);
    /// g
    pub const GLOBAL: Self = Self(1 << 1);
    /// i
    pub const IGNORE_CASE: Self = Self(1 << 2);
    /// m
    pub const MULTILINE: Self = Self(1 << 3);
    /// s
    pub const DOT_ALL: Self = Self(1 << 4);
    /// u
    pub const UNICODE: Self = Self(1 << 5);
    /// v
    pub const UNICODE_SETS: Self = Self(1 << 6);
    /// y
    pub const STICKY: Self = Self(1 << 7);
    pub const ANY_UNICODE_MODE: Self = Self(Self::UNICODE.0 | Self::UNICODE_SETS.0);
    pub const MODIFIERS: Self = Self(Self::IGNORE_CASE.0 | Self::MULTILINE.0 | Self::DOT_ALL.0);

    /// `self & other != 0`
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// `self & other == other`
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }
}

impl std::ops::BitOr for RegularExpressionFlags {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for RegularExpressionFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl std::ops::BitAnd for RegularExpressionFlags {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl fmt::Debug for RegularExpressionFlags {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RegularExpressionFlags({:#x})", self.0)
    }
}

/// `var charCodeToRegExpFlag`
pub(crate) fn char_code_to_reg_exp_flag(ch: i32) -> Option<RegularExpressionFlags> {
    Some(match u8::try_from(ch).ok()? {
        b'd' => RegularExpressionFlags::HAS_INDICES,
        b'g' => RegularExpressionFlags::GLOBAL,
        b'i' => RegularExpressionFlags::IGNORE_CASE,
        b'm' => RegularExpressionFlags::MULTILINE,
        b's' => RegularExpressionFlags::DOT_ALL,
        b'u' => RegularExpressionFlags::UNICODE,
        b'v' => RegularExpressionFlags::UNICODE_SETS,
        b'y' => RegularExpressionFlags::STICKY,
        _ => return None,
    })
}

/// `var regExpFlagToFirstAvailableLanguageVersion`
fn reg_exp_flag_to_first_available_language_version(
    flag: RegularExpressionFlags,
) -> Option<ScriptTarget> {
    Some(match flag {
        RegularExpressionFlags::HAS_INDICES => ScriptTarget::ES2022,
        RegularExpressionFlags::DOT_ALL => ScriptTarget::ES2018,
        RegularExpressionFlags::UNICODE_SETS => ScriptTarget::ES2024,
        _ => return None,
    })
}

/// `type ErrorCallback func(diagnostic *diagnostics.Message, start, length int, args ...any)`
///
/// PORT: Go's `args ...any` becomes `&[String]` — every diagnostic emitted
/// here takes string or small-integer args only (ints are pre-stringified at
/// the call site), matching the `packagejson` TraceFunc convention.
pub type ErrorCallback<'a> = dyn FnMut(&'static Message, usize, usize, &[String]) + 'a;

/// `func (s *Scanner) checkRegularExpressionFlagAvailability`
///
/// PORT: the Scanner receiver reduces to `languageVersion()` and `errorAt`;
/// both are passed in until scanner.rs reconciles.
pub(crate) fn check_regular_expression_flag_availability(
    language_version: ScriptTarget,
    flag: RegularExpressionFlags,
    pos: usize,
    size: usize,
    on_error: &mut ErrorCallback,
) {
    // PORT: `.filter` instead of an `if let ... && ...` let-chain (needs Rust 1.88+).
    if let Some(available_from) =
        reg_exp_flag_to_first_available_language_version(flag).filter(|v| language_version < *v)
    {
        on_error(
            &diagnostics::This_regular_expression_flag_is_only_available_when_targeting_0_or_later,
            pos,
            size,
            &[available_from.to_string().to_lowercase()],
        );
    }
}

/// `type classSetExpressionType int`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(dead_code)] // Unknown/ClassUnion exist for Go parity; only the operator types are dispatched on.
enum ClassSetExpressionType {
    Unknown,
    ClassUnion,
    ClassIntersection,
    ClassSubtraction,
}

/// `type groupNameReference struct`
struct GroupNameReference {
    pos: usize,
    end: usize,
    name: Vec<u8>,
}

/// `type decimalEscapeValue struct`
struct DecimalEscapeValue {
    pos: usize,
    end: usize,
    value: i64,
}

/// `type regExpParser struct`
pub(crate) struct RegExpParser<'a> {
    // ==== Scanner-owned state (Go fields on `p.scanner`) ====
    // PORT: owned by the parser until scanner.rs reconciles — see file header.
    text: &'a [u8],
    pos: usize,
    // `p.end` and `s.end` coincide during `run` (the caller restricts the
    // scanner's end to endOfRegExpBody before constructing the parser).
    end: usize,
    token_value: Vec<u8>,
    token_start: usize,
    token_flags: TokenFlags,
    script_target: ScriptTarget,
    on_error: Option<&'a mut ErrorCallback<'a>>,

    // ==== regExpParser fields ====
    // PORT: end_of_body/reg_exp_flags are kept for Go parity (ReScanSlashToken
    // also reads them), but `run()` only needs the decoded booleans.
    #[allow(dead_code)]
    end_of_body: usize,
    #[allow(dead_code)]
    reg_exp_flags: RegularExpressionFlags,
    any_unicode_mode: bool,
    unicode_sets_mode: bool,
    annex_b: bool,

    any_unicode_mode_or_non_annex_b: bool,
    named_capture_groups: bool,

    /// See scanClassSetExpression.
    may_contain_strings: bool,
    /// The number of all (named and unnamed) capturing groups defined in the regex.
    number_of_capturing_groups: i64,
    /// All named capturing groups defined in the regex.
    group_specifiers: Set<Vec<u8>>,
    /// All references to named capturing groups in the regex.
    group_name_references: Vec<GroupNameReference>,
    /// All numeric backreferences within the regex.
    decimal_escapes: Vec<DecimalEscapeValue>,
    /// A stack of scopes for named capturing groups. See scanGroupName.
    named_capturing_groups: Vec<Set<Vec<u8>>>,

    /// pendingLowSurrogate holds the low surrogate to emit on the next
    /// scanSourceCharacter call when Corsa has to split a non-BMP rune into
    /// UTF-16 surrogate code units in non-unicode mode. Strada did not need
    /// this bookkeeping because its source text was already indexed as UTF-16.
    pending_low_surrogate: i32,
}

impl<'a> RegExpParser<'a> {
    /// `&regExpParser{scanner: s, end: endOfRegExpBody, ...}` from
    /// `Scanner.ReScanSlashToken` — `text` is the whole source text, `pos` is
    /// startOfRegExpBody, `end` is endOfRegExpBody. `reg_exp_flags` is the
    /// accumulated flag set from `scan_regular_expression_flags`.
    /// `named_capture_groups` is the first-pass guess from ReScanSlashToken;
    /// Go always constructs the parser with `annexB: true`.
    pub(crate) fn new(
        text: &'a [u8],
        pos: usize,
        end: usize,
        reg_exp_flags: RegularExpressionFlags,
        named_capture_groups: bool,
        script_target: ScriptTarget,
        on_error: Option<&'a mut ErrorCallback<'a>>,
    ) -> Self {
        Self {
            text,
            pos,
            end,
            token_value: Vec::new(),
            token_start: 0,
            token_flags: TokenFlags::NONE,
            script_target,
            on_error,
            end_of_body: end,
            reg_exp_flags,
            any_unicode_mode: reg_exp_flags.intersects(RegularExpressionFlags::ANY_UNICODE_MODE),
            unicode_sets_mode: reg_exp_flags.intersects(RegularExpressionFlags::UNICODE_SETS),
            annex_b: true,
            any_unicode_mode_or_non_annex_b: false,
            named_capture_groups,
            may_contain_strings: false,
            number_of_capturing_groups: 0,
            group_specifiers: Set::new(),
            group_name_references: Vec::new(),
            decimal_escapes: Vec::new(),
            named_capturing_groups: Vec::new(),
            pending_low_surrogate: 0,
        }
    }

    /// The scanner position after `run`, for the caller to copy back (Go reads
    /// it off the shared `s.pos`).
    // PORT: pos()/set_pos() are the Scanner surface the main scanner agent
    // will consume via ReScanSlashToken.
    #[allow(dead_code)]
    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    /// `func (p *regExpParser) setPos`
    #[allow(dead_code)]
    pub(crate) fn set_pos(&mut self, v: usize) {
        self.pos = v;
    }

    /// `func (p *regExpParser) incPos` — `n` is signed because Go passes -1 to
    /// back up by one position.
    fn inc_pos(&mut self, n: isize) {
        self.pos = self.pos.wrapping_add_signed(n);
    }

    /// `func (p *regExpParser) char` → `s.char()` — NOTE: like Go, this only
    /// decodes the current byte and returns -1 at end.
    fn char(&self) -> i32 {
        match self.byte() {
            Some(b) => i32::from(b),
            None => -1,
        }
    }

    /// PORT: byte-view of `char()` so match sites can use byte-literal
    /// patterns; `None` is Go's -1.
    fn byte(&self) -> Option<u8> {
        if self.pos < self.end {
            Some(self.text[self.pos])
        } else {
            None
        }
    }

    /// `func (p *regExpParser) charAt` — takes an absolute position (Go's
    /// `p.charAt(pos)` calls `s.charAt(pos - p.pos())`).
    fn char_at(&self, pos: usize) -> i32 {
        if pos < self.end {
            i32::from(self.text[pos])
        } else {
            -1
        }
    }

    /// `func (s *Scanner) charAt` — the byte `offset` ahead of pos, -1 at end.
    fn char_at_offset(&self, offset: usize) -> i32 {
        self.char_at(self.pos + offset)
    }

    /// `func (p *regExpParser) error` → `s.errorAt`.
    fn error_at(&mut self, msg: &'static Message, pos: usize, length: usize, args: &[String]) {
        if let Some(on_error) = self.on_error.as_deref_mut() {
            on_error(msg, pos, length, args);
        }
    }

    /// `func (s *Scanner) error` → `s.errorAt(msg, s.pos, 0)`.
    fn error(&mut self, msg: &'static Message) {
        self.error_at(msg, self.pos, 0, &[]);
    }

    /// `func (p *regExpParser) text`
    fn text(&self) -> &'a [u8] {
        self.text
    }

    /// `func (s *Scanner) languageVersion`
    fn language_version(&self) -> ScriptTarget {
        if self.script_target == ScriptTarget::None {
            ScriptTarget::LATEST
        } else {
            self.script_target
        }
    }

    /// `func (s *Scanner) charAndSize`
    fn char_and_size(&self) -> (i32, usize) {
        if self.pos < self.end {
            let b = self.text[self.pos];
            if b < 0x80 {
                return (i32::from(b), 1);
            }
        }
        decode_rune_in_string(&self.text()[self.pos..])
    }

    /// `func (s *Scanner) scanASCIIWhile`
    fn scan_ascii_while(&mut self, pred: impl Fn(u8) -> bool) {
        let text = &self.text()[self.pos..self.end];
        let mut i = 0;
        while i < text.len() {
            let b = text[i];
            if b >= 0x80 || !pred(b) {
                break;
            }
            i += 1;
        }
        self.pos += i;
    }
}

fn compare_decimal_strings(a: &[u8], b: &[u8]) -> i32 {
    fn trim_leading_zeros(s: &[u8]) -> &[u8] {
        let t = &s[s.iter().take_while(|&&b| b == b'0').count()..];
        if t.is_empty() { b"0" } else { t }
    }
    let a = trim_leading_zeros(a);
    let b = trim_leading_zeros(b);
    match a.len().cmp(&b.len()) {
        Ordering::Less => -1,
        Ordering::Greater => 1,
        Ordering::Equal => match a.cmp(b) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        },
    }
}

impl<'a> RegExpParser<'a> {
    // Disjunction ::= Alternative ('|' Alternative)*
    /// `func (p *regExpParser) scanDisjunction`
    fn scan_disjunction(&mut self, is_in_group: bool) {
        // Names defined by any of this disjunction's alternatives. Since exactly one
        // alternative is chosen at runtime, these names are unioned together (rather
        // than intersected) and, when this disjunction is nested inside a group,
        // bubbled up into the enclosing alternative's scope once the group closes.
        // This ensures a name defined inside a nested group (e.g. `(?:(?<a>x))`) is
        // still visible to a duplicate check for a sibling group later in the same
        // enclosing alternative (e.g. `(?:(?<a>x))(?<a>z)`).
        let mut disjunction_names: Set<Vec<u8>> = Set::new();
        loop {
            self.named_capturing_groups.push(Set::new());
            self.scan_alternative(is_in_group);
            let alternative_names = self.named_capturing_groups.pop().unwrap_or_default();
            for name in alternative_names.keys() {
                disjunction_names.add(name.clone());
            }
            if self.char() != i32::from(b'|') {
                break;
            }
            self.inc_pos(1);
        }
        if is_in_group && !self.named_capturing_groups.is_empty() {
            let parent_scope = self.named_capturing_groups.last_mut().unwrap();
            for name in disjunction_names.keys() {
                parent_scope.add(name.clone());
            }
        }
    }

    // Alternative ::= Term*
    // Term ::=
    //
    //	| Assertion
    //	| Atom Quantifier?
    //
    // Assertion ::=
    //
    //	| '^'
    //	| '$'
    //	| '\b'
    //	| '\B'
    //	| '(?=' Disjunction ')'
    //	| '(?!' Disjunction ')'
    //	| '(?<=' Disjunction ')'
    //	| '(?<!' Disjunction ')'
    //
    // Quantifier ::= QuantifierPrefix '?'?
    // QuantifierPrefix ::=
    //
    //	| '*'
    //	| '+'
    //	| '?'
    //	| '{' DecimalDigits (',' DecimalDigits?)? '}'
    //
    // Atom ::=
    //
    //	| PatternCharacter
    //	| '.'
    //	| '\' AtomEscape
    //	| CharacterClass
    //	| '(?<' RegExpIdentifierName '>' Disjunction ')'
    //	| '(?' RegularExpressionFlags ('-' RegularExpressionFlags)? ':' Disjunction ')'
    //
    // CharacterClass ::= unicodeMode
    //
    //	? '[' ClassRanges ']'
    //	: '[' ClassSetExpression ']'
    /// `func (p *regExpParser) scanAlternative`
    fn scan_alternative(&mut self, is_in_group: bool) {
        let mut is_previous_term_quantifiable = false;
        while self.pos < self.end {
            let start = self.pos;
            let ch = self.char();
            match u8::try_from(ch) {
                Ok(b'^' | b'$') => {
                    self.inc_pos(1);
                    is_previous_term_quantifiable = false;
                }
                Ok(b'\\') => {
                    self.inc_pos(1);
                    match self.byte() {
                        Some(b'b' | b'B') => {
                            self.inc_pos(1);
                            is_previous_term_quantifiable = false;
                        }
                        _ => {
                            self.scan_atom_escape();
                            is_previous_term_quantifiable = true;
                        }
                    }
                }
                Ok(b'(') => {
                    self.inc_pos(1);
                    if self.byte() == Some(b'?') {
                        self.inc_pos(1);
                        match self.byte() {
                            Some(b'=' | b'!') => {
                                self.inc_pos(1);
                                // In Annex B, `(?=Disjunction)` and `(?!Disjunction)` are quantifiable
                                is_previous_term_quantifiable =
                                    !self.any_unicode_mode_or_non_annex_b;
                            }
                            Some(b'<') => {
                                let group_name_start = self.pos;
                                self.inc_pos(1);
                                match self.byte() {
                                    Some(b'=' | b'!') => {
                                        self.inc_pos(1);
                                        is_previous_term_quantifiable = false;
                                    }
                                    _ => {
                                        self.scan_group_name(false /*isReference*/);
                                        self.scan_expected_char(b'>');
                                        if self.language_version() < ScriptTarget::ES2018 {
                                            self.error_at(&diagnostics::Named_capturing_groups_are_only_available_when_targeting_ES2018_or_later, group_name_start, self.pos - group_name_start, &[]);
                                        }
                                        self.number_of_capturing_groups += 1;
                                        is_previous_term_quantifiable = true;
                                    }
                                }
                            }
                            _ => {
                                let flags_start = self.pos;
                                let set_flags =
                                    self.scan_pattern_modifiers(RegularExpressionFlags::NONE);
                                if self.byte() == Some(b'-') {
                                    self.inc_pos(1);
                                    self.scan_pattern_modifiers(set_flags);
                                    if self.pos == flags_start + 1 {
                                        self.error_at(&diagnostics::Subpattern_flags_must_be_present_when_there_is_a_minus_sign, flags_start, self.pos - flags_start, &[]);
                                    }
                                }
                                // Modifier characters were consumed, so this is `(?flags:` rather than a plain `(?:` group.
                                if self.pos != flags_start
                                    && self.language_version() < ScriptTarget::ES2025
                                {
                                    self.error_at(&diagnostics::Regular_expression_pattern_modifiers_are_only_available_when_targeting_0_or_later, flags_start, self.pos - flags_start, &[ScriptTarget::ES2025.to_string().to_lowercase()]);
                                }
                                self.scan_expected_char(b':');
                                is_previous_term_quantifiable = true;
                            }
                        }
                    } else {
                        self.number_of_capturing_groups += 1;
                        is_previous_term_quantifiable = true;
                    }
                    self.scan_disjunction(true /*isInGroup*/);
                    self.scan_expected_char(b')');
                }
                Ok(b'{') | Ok(b'*' | b'+' | b'?') => {
                    if ch == i32::from(b'{') {
                        self.inc_pos(1);
                        let digits_start = self.pos;
                        self.scan_digits();
                        let min_str = self.token_value.clone();
                        if !self.any_unicode_mode_or_non_annex_b && min_str.is_empty() {
                            is_previous_term_quantifiable = true;
                            continue;
                        }
                        if self.byte() == Some(b',') {
                            self.inc_pos(1);
                            self.scan_digits();
                            let max_str = self.token_value.clone();
                            if min_str.is_empty() {
                                if !max_str.is_empty() || self.byte() == Some(b'}') {
                                    self.error_at(
                                        &diagnostics::Incomplete_quantifier_Digit_expected,
                                        digits_start,
                                        0,
                                        &[],
                                    );
                                } else {
                                    self.error_at(&diagnostics::Unexpected_0_Did_you_mean_to_escape_it_with_backslash, start, 1, &[rune_to_string(ch)]);
                                    is_previous_term_quantifiable = true;
                                    continue;
                                }
                            } else if !max_str.is_empty()
                                && compare_decimal_strings(&min_str, &max_str) > 0
                                && (self.any_unicode_mode_or_non_annex_b
                                    || self.byte() == Some(b'}'))
                            {
                                self.error_at(
                                    &diagnostics::Numbers_out_of_order_in_quantifier,
                                    digits_start,
                                    self.pos - digits_start,
                                    &[],
                                );
                            }
                        } else if min_str.is_empty() {
                            if self.any_unicode_mode_or_non_annex_b {
                                self.error_at(&diagnostics::Unexpected_0_Did_you_mean_to_escape_it_with_backslash, start, 1, &[rune_to_string(ch)]);
                            }
                            is_previous_term_quantifiable = true;
                            continue;
                        }
                        if self.byte() != Some(b'}') {
                            if self.any_unicode_mode_or_non_annex_b {
                                self.error_at(
                                    &diagnostics::X_0_expected,
                                    self.pos,
                                    0,
                                    &["}".to_string()],
                                );
                                self.inc_pos(-1);
                            } else {
                                is_previous_term_quantifiable = true;
                                continue;
                            }
                        }
                        // PORT: Go `fallthrough` into the '*','+','?' quantifier arm.
                    }
                    self.inc_pos(1);
                    if self.byte() == Some(b'?') {
                        // Non-greedy
                        self.inc_pos(1);
                    }
                    if !is_previous_term_quantifiable {
                        self.error_at(
                            &diagnostics::There_is_nothing_available_for_repetition,
                            start,
                            self.pos - start,
                            &[],
                        );
                    }
                    is_previous_term_quantifiable = false;
                }
                Ok(b'.') => {
                    self.inc_pos(1);
                    is_previous_term_quantifiable = true;
                }
                Ok(b'[') => {
                    self.inc_pos(1);
                    if self.unicode_sets_mode {
                        self.scan_class_set_expression();
                    } else {
                        self.scan_class_ranges();
                        self.pending_low_surrogate = 0;
                    }
                    self.scan_expected_char(b']');
                    is_previous_term_quantifiable = true;
                }
                Ok(b')') if is_in_group => return,
                Ok(b')' | b']' | b'}') => {
                    if self.any_unicode_mode_or_non_annex_b || ch == i32::from(b')') {
                        self.error_at(
                            &diagnostics::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                            self.pos,
                            1,
                            &[rune_to_string(ch)],
                        );
                    }
                    self.inc_pos(1);
                    is_previous_term_quantifiable = true;
                }
                Ok(b'/' | b'|') => return,
                _ => {
                    self.scan_source_character();
                    is_previous_term_quantifiable = true;
                }
            }
        }
    }

    /// `func (p *regExpParser) scanPatternModifiers`
    fn scan_pattern_modifiers(
        &mut self,
        mut curr_flags: RegularExpressionFlags,
    ) -> RegularExpressionFlags {
        while self.pos < self.end {
            let (ch, size) = decode_rune_in_string(&self.text()[self.pos..]);
            if ch == RUNE_ERROR || !is_identifier_part(ch) {
                break;
            }
            match char_code_to_reg_exp_flag(ch) {
                None => {
                    self.error_at(
                        &diagnostics::Unknown_regular_expression_flag,
                        self.pos,
                        size,
                        &[],
                    );
                }
                Some(flag) if curr_flags.intersects(flag) => {
                    self.error_at(
                        &diagnostics::Duplicate_regular_expression_flag,
                        self.pos,
                        size,
                        &[],
                    );
                }
                Some(flag) if !flag.intersects(RegularExpressionFlags::MODIFIERS) => {
                    self.error_at(&diagnostics::This_regular_expression_flag_cannot_be_toggled_within_a_subpattern, self.pos, size, &[]);
                }
                Some(flag) => {
                    // Modifier syntax itself requires ES2025, which is later than any flag that can appear
                    // here, so the group's own diagnostic already covers availability.
                    curr_flags |= flag;
                }
            }
            self.inc_pos(size as isize);
        }
        curr_flags
    }

    // AtomEscape ::=
    //
    //	| DecimalEscape
    //	| CharacterClassEscape
    //	| CharacterEscape
    //	| 'k<' RegExpIdentifierName '>'
    /// `func (p *regExpParser) scanAtomEscape`
    fn scan_atom_escape(&mut self) {
        debug::assert_!(self.pos > 0 && self.text[self.pos - 1] == b'\\');
        match self.byte() {
            Some(b'k') => {
                self.inc_pos(1);
                if self.byte() == Some(b'<') {
                    self.inc_pos(1);
                    self.scan_group_name(true /*isReference*/);
                    self.scan_expected_char(b'>');
                } else if self.any_unicode_mode_or_non_annex_b || self.named_capture_groups {
                    self.error_at(&diagnostics::X_k_must_be_followed_by_a_capturing_group_name_enclosed_in_angle_brackets, self.pos - 2, 2, &[]);
                }
            }
            Some(b'q') if self.unicode_sets_mode => {
                self.inc_pos(1);
                self.error_at(
                    &diagnostics::X_q_is_only_available_inside_character_class,
                    self.pos - 2,
                    2,
                    &[],
                );
            }
            _ => {
                // PORT: Go's `case 'q':` falls through to `default` when not in
                // UnicodeSets mode; merged into the default arm.
                if !self.scan_character_class_escape() && !self.scan_decimal_escape() {
                    // Regex literals cannot contain line breaks here, so a character escape must consume something.
                    debug::assert_!(!self.scan_character_escape(true /*atomEscape*/).is_empty());
                }
            }
        }
    }

    // DecimalEscape ::= [1-9] [0-9]*
    /// `func (p *regExpParser) scanDecimalEscape`
    fn scan_decimal_escape(&mut self) -> bool {
        debug::assert_!(self.pos > 0 && self.text[self.pos - 1] == b'\\');
        let ch = self.char();
        if (i32::from(b'1')..=i32::from(b'9')).contains(&ch) {
            let start = self.pos;
            self.scan_digits();
            // Go: `strconv.Atoi` — on error (only overflow is reachable) math.MaxInt.
            let val = std::str::from_utf8(&self.token_value)
                .ok()
                .and_then(|s| s.parse::<i64>().ok())
                .unwrap_or(i64::MAX);
            self.decimal_escapes.push(DecimalEscapeValue {
                pos: start,
                end: self.pos,
                value: val,
            });
            return true;
        }
        false
    }

    // CharacterEscape ::=
    //
    //	| `c` ControlLetter
    //	| IdentityEscape
    //	| (Other sequences handled by `scanEscapeSequence`)
    //
    // IdentityEscape ::=
    //
    //	| '^' | '$' | '/' | '\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{' | '}' | '|'
    //	| [~AnyUnicodeMode] (any other non-identifier characters)
    /// `func (p *regExpParser) scanCharacterEscape`
    fn scan_character_escape(&mut self, atom_escape: bool) -> Vec<u8> {
        debug::assert_!(self.pos > 0 && self.text[self.pos - 1] == b'\\');
        let ch = self.char();
        match u8::try_from(ch) {
            Err(_) => {
                // Go `case -1:`
                self.error_at(
                    &diagnostics::Undetermined_character_escape,
                    self.pos - 1,
                    1,
                    &[],
                );
                b"\\".to_vec()
            }
            Ok(b'c') => {
                self.inc_pos(1);
                let ch = self.char();
                if is_ascii_letter(ch) {
                    self.inc_pos(1);
                    return vec![(ch & 0x1f) as u8];
                }
                if self.any_unicode_mode_or_non_annex_b {
                    self.error_at(
                        &diagnostics::X_c_must_be_followed_by_an_ASCII_letter,
                        self.pos - 2,
                        2,
                        &[],
                    );
                } else if atom_escape {
                    self.inc_pos(-1);
                    return b"\\".to_vec();
                }
                // Go `string(ch)` — ch may be -1 here, which Go renders as U+FFFD.
                stringutil::encode_js_string_rune(ch)
            }
            Ok(
                b'^' | b'$' | b'/' | b'\\' | b'.' | b'*' | b'+' | b'?' | b'(' | b')' | b'[' | b']'
                | b'{' | b'}' | b'|',
            ) => {
                self.inc_pos(1);
                stringutil::encode_js_string_rune(ch)
            }
            _ => {
                self.inc_pos(-1); // back up to include the backslash for scanEscapeSequence
                let mut flags = ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION;
                if self.annex_b {
                    flags |= ESCAPE_SEQUENCE_SCANNING_FLAGS_ANNEX_B;
                }
                if self.any_unicode_mode {
                    flags |= ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE;
                }
                if atom_escape {
                    flags |= ESCAPE_SEQUENCE_SCANNING_FLAGS_ATOM_ESCAPE;
                }
                self.scan_escape_sequence(flags)
            }
        }
    }

    /// `func (p *regExpParser) scanGroupName`
    fn scan_group_name(&mut self, is_reference: bool) {
        debug::assert_!(self.pos > 0 && self.text[self.pos - 1] == b'<');
        self.token_start = self.pos;
        if !self.scan_identifier(0, IdentifierVariant::RegExpGroupName) {
            self.error_at(
                &diagnostics::Expected_a_capturing_group_name,
                self.pos,
                0,
                &[],
            );
        } else if is_reference {
            self.group_name_references.push(GroupNameReference {
                pos: self.token_start,
                end: self.pos,
                name: self.token_value.clone(),
            });
        } else if self.named_capturing_groups_contains(&self.token_value) {
            self.error_at(&diagnostics::Named_capturing_groups_with_the_same_name_must_be_mutually_exclusive_to_each_other, self.token_start, self.pos - self.token_start, &[]);
        } else {
            // A previous definition can only have come from a mutually exclusive alternative.
            // Below ES2018 the group itself is already reported, so don't stack a second error on it.
            if self.group_specifiers.has(&self.token_value)
                && self.language_version() >= ScriptTarget::ES2018
                && self.language_version() < ScriptTarget::ES2025
            {
                self.error_at(&diagnostics::Duplicate_named_capturing_groups_are_only_available_when_targeting_0_or_later, self.token_start, self.pos - self.token_start, &[ScriptTarget::ES2025.to_string().to_lowercase()]);
            }
            if let Some(scope) = self.named_capturing_groups.last_mut() {
                scope.add(self.token_value.clone());
            }
            self.group_specifiers.add(self.token_value.clone());
        }
    }

    /// `func (p *regExpParser) namedCapturingGroupsContains`
    fn named_capturing_groups_contains(&self, name: &[u8]) -> bool {
        self.named_capturing_groups
            .iter()
            .any(|group| group.has(name))
    }

    /// `func (p *regExpParser) isClassContentExit`
    fn is_class_content_exit(&self, ch: i32) -> bool {
        ch == i32::from(b']') || self.pos >= self.end
    }

    // ClassRanges ::= '^'? (ClassAtom ('-' ClassAtom)?)*
    /// `func (p *regExpParser) scanClassRanges`
    fn scan_class_ranges(&mut self) {
        debug::assert_!(self.pos > 0 && self.text[self.pos - 1] == b'[');
        self.pending_low_surrogate = 0;
        if self.byte() == Some(b'^') {
            self.inc_pos(1);
        }
        while self.pos < self.end {
            let ch = self.char();
            if self.is_class_content_exit(ch) {
                return;
            }
            let min_start = self.pos;
            let min_character = self.scan_class_atom();
            if self.byte() == Some(b'-') {
                self.inc_pos(1);
                let ch = self.char();
                if self.is_class_content_exit(ch) {
                    return;
                }
                if min_character.is_empty() && self.any_unicode_mode_or_non_annex_b {
                    self.error_at(&diagnostics::A_character_class_range_must_not_be_bounded_by_another_character_class, min_start, self.pos - 1 - min_start, &[]);
                }
                let max_start = self.pos;
                let max_character = self.scan_class_atom();
                if max_character.is_empty() && self.any_unicode_mode_or_non_annex_b {
                    self.error_at(&diagnostics::A_character_class_range_must_not_be_bounded_by_another_character_class, max_start, self.pos - max_start, &[]);
                    continue;
                }
                if min_character.is_empty() {
                    continue;
                }
                let (min_character_value, min_size) =
                    stringutil::decode_js_string_rune(&min_character);
                let (max_character_value, max_size) =
                    stringutil::decode_js_string_rune(&max_character);
                if min_character.len() == min_size
                    && max_character.len() == max_size
                    && min_character_value > max_character_value
                {
                    self.error_at(
                        &diagnostics::Range_out_of_order_in_character_class,
                        min_start,
                        self.pos - min_start,
                        &[],
                    );
                }
            }
        }
    }

    // Static Semantics: MayContainStrings
    //     ClassUnion: ClassSetOperands.some(ClassSetOperand => ClassSetOperand.MayContainStrings)
    //     ClassIntersection: ClassSetOperands.every(ClassSetOperand => ClassSetOperand.MayContainStrings)
    //     ClassSubtraction: ClassSetOperands[0].MayContainStrings
    //     ClassSetOperand:
    //         || ClassStringDisjunctionContents.MayContainStrings
    //         || CharacterClassEscape.UnicodePropertyValueExpression.LoneUnicodePropertyNameOrValue.MayContainStrings
    //     ClassStringDisjunctionContents: ClassStrings.some(ClassString => ClassString.ClassSetCharacters.length !== 1)
    //     LoneUnicodePropertyNameOrValue: isBinaryUnicodePropertyOfStrings(LoneUnicodePropertyNameOrValue)
    //
    // ClassSetExpression ::= '^'? (ClassUnion | ClassIntersection | ClassSubtraction)
    // ClassUnion ::= (ClassSetRange | ClassSetOperand)*
    // ClassIntersection ::= ClassSetOperand ('&&' ClassSetOperand)+
    // ClassSubtraction ::= ClassSetOperand ('--' ClassSetOperand)+
    // ClassSetRange ::= ClassSetCharacter '-' ClassSetCharacter
    /// `func (p *regExpParser) scanClassSetExpression`
    fn scan_class_set_expression(&mut self) {
        debug::assert_!(self.pos > 0 && self.text[self.pos - 1] == b'[');
        let mut is_character_complement = false;
        if self.byte() == Some(b'^') {
            self.inc_pos(1);
            is_character_complement = true;
        }
        let mut expression_may_contain_strings = false;
        let mut ch = self.char();
        if self.is_class_content_exit(ch) {
            return;
        }
        let mut start = self.pos;
        let mut operand: Vec<u8> = Vec::new();
        let two_chars = if self.pos + 1 < self.end {
            &self.text()[self.pos..self.pos + 2]
        } else {
            b""
        };
        match two_chars {
            b"--" | b"&&" => {
                self.error_at(&diagnostics::Expected_a_class_set_operand, self.pos, 0, &[]);
                self.may_contain_strings = false;
            }
            _ => {
                operand = self.scan_class_set_operand();
            }
        }
        match self.byte() {
            Some(b'-') => {
                if self.pos + 1 < self.end && self.char_at(self.pos + 1) == i32::from(b'-') {
                    if is_character_complement && self.may_contain_strings {
                        self.error_at(&diagnostics::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class, start, self.pos - start, &[]);
                    }
                    expression_may_contain_strings = self.may_contain_strings;
                    self.scan_class_set_sub_expression(ClassSetExpressionType::ClassSubtraction);
                    self.may_contain_strings =
                        !is_character_complement && expression_may_contain_strings;
                    return;
                }
            }
            Some(b'&') => {
                if self.pos + 1 < self.end && self.char_at(self.pos + 1) == i32::from(b'&') {
                    self.scan_class_set_sub_expression(ClassSetExpressionType::ClassIntersection);
                    if is_character_complement && self.may_contain_strings {
                        self.error_at(&diagnostics::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class, start, self.pos - start, &[]);
                    }
                    expression_may_contain_strings = self.may_contain_strings;
                    self.may_contain_strings =
                        !is_character_complement && expression_may_contain_strings;
                    return;
                }
            }
            _ => {
                if is_character_complement && self.may_contain_strings {
                    self.error_at(&diagnostics::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class, start, self.pos - start, &[]);
                }
                expression_may_contain_strings = self.may_contain_strings;
            }
        }
        while self.pos < self.end {
            ch = self.char();
            match u8::try_from(ch) {
                Ok(b'-') => {
                    self.inc_pos(1);
                    ch = self.char();
                    if self.is_class_content_exit(ch) {
                        self.may_contain_strings =
                            !is_character_complement && expression_may_contain_strings;
                        return;
                    }
                    if ch == i32::from(b'-') {
                        self.inc_pos(1);
                        self.error_at(&diagnostics::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead, self.pos - 2, 2, &[]);
                        start = self.pos - 2;
                        operand = self.text()[start..self.pos].to_vec();
                        continue;
                    } else {
                        if operand.is_empty() {
                            self.error_at(&diagnostics::A_character_class_range_must_not_be_bounded_by_another_character_class, start, self.pos - 1 - start, &[]);
                        }
                        let second_start = self.pos;
                        let second_operand = self.scan_class_set_operand();
                        if is_character_complement && self.may_contain_strings {
                            self.error_at(&diagnostics::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class, second_start, self.pos - second_start, &[]);
                        }
                        expression_may_contain_strings =
                            expression_may_contain_strings || self.may_contain_strings;
                        if second_operand.is_empty() {
                            self.error_at(&diagnostics::A_character_class_range_must_not_be_bounded_by_another_character_class, second_start, self.pos - second_start, &[]);
                        } else if !operand.is_empty() {
                            let (min_character_value, min_size) =
                                stringutil::decode_js_string_rune(&operand);
                            let (max_character_value, max_size) =
                                stringutil::decode_js_string_rune(&second_operand);
                            if operand.len() == min_size
                                && second_operand.len() == max_size
                                && min_character_value > max_character_value
                            {
                                self.error_at(
                                    &diagnostics::Range_out_of_order_in_character_class,
                                    start,
                                    self.pos - start,
                                    &[],
                                );
                            }
                        }
                    }
                }
                Ok(b'&')
                    if self.pos + 1 < self.end && self.char_at(self.pos + 1) == i32::from(b'&') =>
                {
                    start = self.pos;
                    self.inc_pos(2);
                    self.error_at(&diagnostics::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead, self.pos - 2, 2, &[]);
                    if self.byte() == Some(b'&') {
                        self.error_at(
                            &diagnostics::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                            self.pos,
                            1,
                            &[rune_to_string(ch)],
                        );
                        self.inc_pos(1);
                    }
                    operand = self.text()[start..self.pos].to_vec();
                    continue;
                }
                _ => {}
            }
            if self.is_class_content_exit(self.char()) {
                break;
            }
            start = self.pos;
            let two_chars = if self.pos + 1 < self.end {
                &self.text()[self.pos..self.pos + 2]
            } else {
                b""
            };
            match two_chars {
                b"--" | b"&&" => {
                    self.error_at(&diagnostics::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead, self.pos, 2, &[]);
                    self.inc_pos(2);
                    operand = self.text()[start..self.pos].to_vec();
                }
                _ => {
                    operand = self.scan_class_set_operand();
                    if is_character_complement && self.may_contain_strings {
                        self.error_at(&diagnostics::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class, start, self.pos - start, &[]);
                    }
                    expression_may_contain_strings =
                        expression_may_contain_strings || self.may_contain_strings;
                }
            }
        }
        self.may_contain_strings = !is_character_complement && expression_may_contain_strings;
    }

    /// `func (p *regExpParser) scanClassSetSubExpression`
    fn scan_class_set_sub_expression(&mut self, expression_type: ClassSetExpressionType) {
        let mut expression_may_contain_strings = self.may_contain_strings;
        while self.pos < self.end {
            let mut ch = self.char();
            if self.is_class_content_exit(ch) {
                break;
            }
            match u8::try_from(ch) {
                Ok(b'-') => {
                    self.inc_pos(1);
                    if self.byte() == Some(b'-') {
                        self.inc_pos(1);
                        if expression_type != ClassSetExpressionType::ClassSubtraction {
                            self.error_at(&diagnostics::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead, self.pos - 2, 2, &[]);
                        }
                    } else {
                        self.error_at(&diagnostics::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead, self.pos - 1, 1, &[]);
                    }
                }
                Ok(b'&') => {
                    self.inc_pos(1);
                    if self.byte() == Some(b'&') {
                        self.inc_pos(1);
                        if expression_type != ClassSetExpressionType::ClassIntersection {
                            self.error_at(&diagnostics::Operators_must_not_be_mixed_within_a_character_class_Wrap_it_in_a_nested_class_instead, self.pos - 2, 2, &[]);
                        }
                        if self.byte() == Some(b'&') {
                            self.error_at(
                                &diagnostics::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                                self.pos,
                                1,
                                &[rune_to_string(ch)],
                            );
                            self.inc_pos(1);
                        }
                    } else {
                        self.error_at(
                            &diagnostics::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                            self.pos - 1,
                            1,
                            &[rune_to_string(ch)],
                        );
                    }
                }
                _ => match expression_type {
                    ClassSetExpressionType::ClassSubtraction => {
                        self.error_at(&diagnostics::X_0_expected, self.pos, 0, &["--".to_string()]);
                    }
                    ClassSetExpressionType::ClassIntersection => {
                        self.error_at(&diagnostics::X_0_expected, self.pos, 0, &["&&".to_string()]);
                    }
                    _ => {}
                },
            }
            ch = self.char();
            if self.is_class_content_exit(ch) {
                self.error_at(&diagnostics::Expected_a_class_set_operand, self.pos, 0, &[]);
                break;
            }
            self.scan_class_set_operand();
            if expression_type == ClassSetExpressionType::ClassIntersection {
                expression_may_contain_strings =
                    expression_may_contain_strings && self.may_contain_strings;
            }
        }
        self.may_contain_strings = expression_may_contain_strings;
    }

    // ClassSetOperand ::=
    //
    //	| '[' ClassSetExpression ']'
    //	| '\' CharacterClassEscape
    //	| '\q{' ClassStringDisjunctionContents '}'
    //	| ClassSetCharacter
    /// `func (p *regExpParser) scanClassSetOperand`
    fn scan_class_set_operand(&mut self) -> Vec<u8> {
        self.may_contain_strings = false;
        match self.byte() {
            Some(b'[') => {
                self.inc_pos(1);
                self.scan_class_set_expression();
                self.scan_expected_char(b']');
                Vec::new()
            }
            Some(b'\\') => {
                self.inc_pos(1);
                if self.scan_character_class_escape() {
                    return Vec::new();
                } else if self.byte() == Some(b'q') {
                    self.inc_pos(1);
                    if self.byte() == Some(b'{') {
                        self.inc_pos(1);
                        self.scan_class_string_disjunction_contents();
                        self.scan_expected_char(b'}');
                        return Vec::new();
                    } else {
                        self.error_at(&diagnostics::X_q_must_be_followed_by_string_alternatives_enclosed_in_braces, self.pos - 2, 2, &[]);
                        return b"q".to_vec();
                    }
                }
                self.inc_pos(-1);
                // PORT: Go `fallthrough` into the default arm.
                self.scan_class_set_character()
            }
            _ => self.scan_class_set_character(),
        }
    }

    // ClassStringDisjunctionContents ::= ClassSetCharacter* ('|' ClassSetCharacter*)*
    /// `func (p *regExpParser) scanClassStringDisjunctionContents`
    fn scan_class_string_disjunction_contents(&mut self) {
        debug::assert_!(self.pos > 0 && self.text[self.pos - 1] == b'{');
        let mut character_count = 0;
        while self.pos < self.end {
            match self.byte() {
                Some(b'}') => {
                    if character_count != 1 {
                        self.may_contain_strings = true;
                    }
                    return;
                }
                Some(b'|') => {
                    if character_count != 1 {
                        self.may_contain_strings = true;
                    }
                    self.inc_pos(1);
                    character_count = 0;
                }
                _ => {
                    self.scan_class_set_character();
                    character_count += 1;
                }
            }
        }
    }

    // ClassSetCharacter ::=
    //
    //	| SourceCharacter -- ClassSetSyntaxCharacter -- ClassSetReservedDoublePunctuator
    //	| '\' (CharacterEscape | ClassSetReservedPunctuator | 'b')
    /// `func (p *regExpParser) scanClassSetCharacter`
    fn scan_class_set_character(&mut self) -> Vec<u8> {
        let ch = self.char();
        if ch == i32::from(b'\\') {
            self.inc_pos(1);
            let inner_ch = self.char();
            match u8::try_from(inner_ch) {
                Ok(b'b') => {
                    self.inc_pos(1);
                    return b"\x08".to_vec();
                }
                Ok(
                    b'&' | b'-' | b'!' | b'#' | b'%' | b',' | b':' | b';' | b'<' | b'=' | b'>'
                    | b'@' | b'`' | b'~',
                ) => {
                    self.inc_pos(1);
                    return stringutil::encode_js_string_rune(inner_ch);
                }
                _ => {
                    return self.scan_character_escape(false /*atomEscape*/);
                }
            }
        } else if self.pos + 1 < self.end
            && ch == self.char_at(self.pos + 1)
            && matches!(
                u8::try_from(ch),
                Ok(b'&'
                    | b'!'
                    | b'#'
                    | b'%'
                    | b'*'
                    | b'+'
                    | b','
                    | b'.'
                    | b':'
                    | b';'
                    | b'<'
                    | b'='
                    | b'>'
                    | b'?'
                    | b'@'
                    | b'`'
                    | b'~')
            )
        {
            self.error_at(&diagnostics::A_character_class_must_not_contain_a_reserved_double_punctuator_Did_you_mean_to_escape_it_with_backslash, self.pos, 2, &[]);
            self.inc_pos(2);
            return self.text()[self.pos - 2..self.pos].to_vec();
        }
        if let Ok(b'/' | b'(' | b')' | b'[' | b']' | b'{' | b'}' | b'-' | b'|') = u8::try_from(ch) {
            self.error_at(
                &diagnostics::Unexpected_0_Did_you_mean_to_escape_it_with_backslash,
                self.pos,
                1,
                &[rune_to_string(ch)],
            );
            self.inc_pos(1);
            return vec![ch as u8];
        }
        self.scan_source_character()
    }

    // ClassAtom ::=
    //
    //	| SourceCharacter but not one of '\' or ']'
    //	| '\' ClassEscape
    //
    // ClassEscape ::=
    //
    //	| 'b'
    //	| '-'
    //	| CharacterClassEscape
    //	| CharacterEscape
    /// `func (p *regExpParser) scanClassAtom`
    fn scan_class_atom(&mut self) -> Vec<u8> {
        if self.byte() == Some(b'\\') {
            self.inc_pos(1);
            match self.byte() {
                Some(b'b') => {
                    self.inc_pos(1);
                    b"\x08".to_vec()
                }
                Some(b'-') => {
                    self.inc_pos(1);
                    vec![b'-']
                }
                _ => {
                    if self.scan_character_class_escape() {
                        Vec::new()
                    } else {
                        self.scan_character_escape(false /*atomEscape*/)
                    }
                }
            }
        } else {
            self.scan_source_character()
        }
    }

    // CharacterClassEscape ::=
    //
    //	| 'd' | 'D' | 's' | 'S' | 'w' | 'W'
    //	| [+AnyUnicodeMode] ('P' | 'p') '{' UnicodePropertyValueExpression '}'
    /// `func (p *regExpParser) scanCharacterClassEscape`
    fn scan_character_class_escape(&mut self) -> bool {
        debug::assert_!(self.pos > 0 && self.text[self.pos - 1] == b'\\');
        let mut is_character_complement = false;
        let start = self.pos - 1;
        let ch = self.char();
        match u8::try_from(ch) {
            Ok(b'd' | b'D' | b's' | b'S' | b'w' | b'W') => {
                self.inc_pos(1);
                true
            }
            Ok(b'P' | b'p') => {
                if ch == i32::from(b'P') {
                    is_character_complement = true;
                }
                self.inc_pos(1);
                if self.byte() == Some(b'{') {
                    self.inc_pos(1);
                    let property_name_or_value_start = self.pos;
                    let property_name_or_value = self.scan_word_characters();
                    if self.byte() == Some(b'=') {
                        let property_name = non_binary_unicode_property(property_name_or_value);
                        if self.pos == property_name_or_value_start {
                            self.error_at(
                                &diagnostics::Expected_a_Unicode_property_name,
                                self.pos,
                                0,
                                &[],
                            );
                        } else if property_name.is_none() {
                            self.error_at(
                                &diagnostics::Unknown_Unicode_property_name,
                                property_name_or_value_start,
                                self.pos - property_name_or_value_start,
                                &[],
                            );
                            if let Some(suggestion) = self
                                .get_spelling_suggestion_for_unicode_property_name(
                                    property_name_or_value,
                                )
                            {
                                self.error_at(
                                    &diagnostics::Did_you_mean_0,
                                    property_name_or_value_start,
                                    self.pos - property_name_or_value_start,
                                    std::slice::from_ref(&suggestion),
                                );
                            }
                        }
                        self.inc_pos(1);
                        let property_value_start = self.pos;
                        let property_value = self.scan_word_characters();
                        if self.pos == property_value_start {
                            self.error_at(
                                &diagnostics::Expected_a_Unicode_property_value,
                                self.pos,
                                0,
                                &[],
                            );
                        } else if let Some(property_name) = property_name.filter(|pn| {
                            values_of_non_binary_unicode_property(pn).is_some_and(|values| {
                                values.binary_search(&property_value).is_err()
                            })
                        }) {
                            self.error_at(
                                &diagnostics::Unknown_Unicode_property_value,
                                property_value_start,
                                self.pos - property_value_start,
                                &[],
                            );
                            if let Some(suggestion) = self
                                .get_spelling_suggestion_for_unicode_property_value(
                                    property_name,
                                    property_value,
                                )
                            {
                                self.error_at(
                                    &diagnostics::Did_you_mean_0,
                                    property_value_start,
                                    self.pos - property_value_start,
                                    std::slice::from_ref(&suggestion),
                                );
                            }
                        }
                    } else {
                        if self.pos == property_name_or_value_start {
                            self.error_at(
                                &diagnostics::Expected_a_Unicode_property_name_or_value,
                                self.pos,
                                0,
                                &[],
                            );
                        } else if is_binary_unicode_property_of_strings(property_name_or_value) {
                            if !self.unicode_sets_mode {
                                self.error_at(&diagnostics::Any_Unicode_property_that_would_possibly_match_more_than_a_single_character_is_only_available_when_the_Unicode_Sets_v_flag_is_set, property_name_or_value_start, self.pos - property_name_or_value_start, &[]);
                            } else if is_character_complement {
                                self.error_at(&diagnostics::Anything_that_would_possibly_match_more_than_a_single_character_is_invalid_inside_a_negated_character_class, property_name_or_value_start, self.pos - property_name_or_value_start, &[]);
                            } else {
                                self.may_contain_strings = true;
                            }
                        } else if !is_general_category_value(property_name_or_value)
                            && !is_binary_unicode_property(property_name_or_value)
                        {
                            self.error_at(
                                &diagnostics::Unknown_Unicode_property_name_or_value,
                                property_name_or_value_start,
                                self.pos - property_name_or_value_start,
                                &[],
                            );
                            if let Some(suggestion) = self
                                .get_spelling_suggestion_for_unicode_property_name_or_value(
                                    property_name_or_value,
                                )
                            {
                                self.error_at(
                                    &diagnostics::Did_you_mean_0,
                                    property_name_or_value_start,
                                    self.pos - property_name_or_value_start,
                                    std::slice::from_ref(&suggestion),
                                );
                            }
                        }
                    }
                    self.scan_expected_char(b'}');
                    if !self.any_unicode_mode {
                        self.error_at(&diagnostics::Unicode_property_value_expressions_are_only_available_when_the_Unicode_u_flag_or_the_Unicode_Sets_v_flag_is_set, start, self.pos - start, &[]);
                    }
                } else if self.any_unicode_mode_or_non_annex_b {
                    self.error_at(&diagnostics::X_0_must_be_followed_by_a_Unicode_property_value_expression_enclosed_in_braces, self.pos - 2, 2, &[rune_to_string(ch)]);
                } else {
                    self.inc_pos(-1);
                    return false;
                }
                true
            }
            _ => false,
        }
    }

    /// `func (p *regExpParser) getSpellingSuggestionForUnicodePropertyName`
    // PORT: Go returns `string`; an owned `String` avoids coupling the
    // suggestion's lifetime to the `name` parameter.
    fn get_spelling_suggestion_for_unicode_property_name(&self, name: &str) -> Option<String> {
        get_spelling_suggestion_for_strings(name, NON_BINARY_UNICODE_PROPERTY_NAMES.iter().copied())
            .map(str::to_string)
    }

    /// `func (p *regExpParser) getSpellingSuggestionForUnicodePropertyValue`
    fn get_spelling_suggestion_for_unicode_property_value(
        &self,
        property_name: &str,
        value: &str,
    ) -> Option<String> {
        let values = values_of_non_binary_unicode_property(property_name)?;
        get_spelling_suggestion_for_strings(value, values.iter().copied()).map(str::to_string)
    }

    /// `func (p *regExpParser) getSpellingSuggestionForUnicodePropertyNameOrValue`
    fn get_spelling_suggestion_for_unicode_property_name_or_value(
        &self,
        name: &str,
    ) -> Option<String> {
        // PORT: `core.ConcatenateSeq(maps.Keys(...), ...)` over the three
        // property tables — the sorted static arrays play the same role as
        // Go's map-key iteration (see unicodeproperties.rs).
        get_spelling_suggestion_for_strings(
            name,
            crate::unicodeproperties::GENERAL_CATEGORY_VALUES
                .iter()
                .copied()
                .chain(
                    crate::unicodeproperties::BINARY_UNICODE_PROPERTIES
                        .iter()
                        .copied(),
                )
                .chain(
                    crate::unicodeproperties::BINARY_UNICODE_PROPERTIES_OF_STRINGS
                        .iter()
                        .copied(),
                ),
        )
        .map(str::to_string)
    }

    /// `func (p *regExpParser) scanWordCharacters`
    fn scan_word_characters(&mut self) -> &'a str {
        let start = self.pos;
        while self.pos < self.end {
            let ch = self.char();
            if !is_word_character(ch) {
                break;
            }
            self.inc_pos(1);
        }
        // Word characters are ASCII, so the slice is always valid UTF-8.
        std::str::from_utf8(&self.text()[start..self.pos]).expect("word characters are ASCII")
    }

    /// `func (p *regExpParser) scanSourceCharacter`
    fn scan_source_character(&mut self) -> Vec<u8> {
        if self.pos >= self.end {
            return Vec::new();
        }
        if !self.any_unicode_mode {
            if self.pending_low_surrogate != 0 {
                // Second of two surrogate code units for the same non-BMP character.
                // Now advance past the full UTF-8 sequence (the high surrogate call did not advance).
                let (_, size) = decode_rune_in_string(&self.text()[self.pos..]);
                self.inc_pos(size as isize);
                let low = self.pending_low_surrogate;
                self.pending_low_surrogate = 0;
                return stringutil::encode_js_string_rune(low);
            }
            let (ch, size) = decode_rune_in_string(&self.text()[self.pos..]);
            if ch == RUNE_ERROR || size == 0 {
                // Not a valid rune; consume one raw byte.
                self.inc_pos(1);
                // Go `string(p.text()[p.pos()-1])` — the byte as a code point,
                // UTF-8 encoded (so bytes >= 0x80 become 2 bytes).
                return stringutil::encode_js_string_rune(i32::from(self.text[self.pos - 1]));
            }
            if utf16_rune_len(ch) == 2 {
                // Non-BMP character: emit the high surrogate first WITHOUT advancing.
                // The low surrogate will be emitted on the next call, which also advances.
                let (high, low) = stringutil::code_point_to_surrogate_pair(ch);
                self.pending_low_surrogate = low;
                return stringutil::encode_js_string_rune(high);
            }
            self.inc_pos(size as isize);
            return stringutil::encode_js_string_rune(ch);
        }
        let (ch, size) = decode_rune_in_string(&self.text()[self.pos..]);
        if size == 0 {
            return Vec::new();
        }
        if ch == RUNE_ERROR {
            // Invalid UTF-8; consume the byte to avoid infinite loops.
            self.inc_pos(size as isize);
            return Vec::new();
        }
        self.inc_pos(size as isize);
        stringutil::encode_js_string_rune(ch)
    }

    /// `func (p *regExpParser) scanExpectedChar`
    ///
    /// PORT: `ch` is always an ASCII literal at call sites, so `u8`.
    fn scan_expected_char(&mut self, ch: u8) {
        if self.byte() == Some(ch) {
            self.inc_pos(1);
        } else {
            self.error_at(
                &diagnostics::X_0_expected,
                self.pos,
                0,
                &[char::from(ch).to_string()],
            );
        }
    }

    /// `func (p *regExpParser) scanDigits`
    fn scan_digits(&mut self) {
        let start = self.pos;
        while self.pos < self.end && is_digit(self.char()) {
            self.inc_pos(1);
        }
        self.token_value = self.text()[start..self.pos].to_vec();
    }

    /// `func (p *regExpParser) run`
    pub(crate) fn run(&mut self) {
        // Regular expressions are checked more strictly when either in 'u' or 'v' mode, or
        // when not using the looser interpretation of the syntax from ECMA-262 Annex B.
        self.any_unicode_mode_or_non_annex_b = self.any_unicode_mode || !self.annex_b;

        self.scan_disjunction(false /*isInGroup*/);

        for i in 0..self.group_name_references.len() {
            let reference = &self.group_name_references[i];
            let (pos, end, name) = (reference.pos, reference.end, reference.name.clone());
            if !self.group_specifiers.has(&name) {
                self.error_at(
                    &diagnostics::There_is_no_capturing_group_named_0_in_this_regular_expression,
                    pos,
                    end - pos,
                    &[String::from_utf8_lossy(&name).into_owned()],
                );
                if !self.group_specifiers.is_empty() {
                    // PORT: Go's `maps.Keys(p.groupSpecifiers)` for the
                    // suggestion candidates; group names may contain CESU-8
                    // surrogate sentinels, hence the lossy conversion.
                    let name = String::from_utf8_lossy(&name).into_owned();
                    let candidates: Vec<String> = self
                        .group_specifiers
                        .keys()
                        .iter()
                        .map(|k| String::from_utf8_lossy(k).into_owned())
                        .collect();
                    if let Some(suggestion) = get_spelling_suggestion_for_strings(
                        &name,
                        candidates.iter().map(String::as_str),
                    ) {
                        let suggestion = suggestion.to_string();
                        self.error_at(&diagnostics::Did_you_mean_0, pos, end - pos, &[suggestion]);
                    }
                }
            }
        }
        for i in 0..self.decimal_escapes.len() {
            let escape = &self.decimal_escapes[i];
            let (pos, end, value) = (escape.pos, escape.end, escape.value);
            // Although a DecimalEscape with a value greater than the number of capturing groups
            // is treated as either a LegacyOctalEscapeSequence or an IdentityEscape in Annex B,
            // an error is nevertheless reported since it's most likely a mistake.
            if value > self.number_of_capturing_groups {
                if self.number_of_capturing_groups > 0 {
                    self.error_at(&diagnostics::This_backreference_refers_to_a_group_that_does_not_exist_There_are_only_0_capturing_groups_in_this_regular_expression, pos, end - pos, &[self.number_of_capturing_groups.to_string()]);
                } else {
                    self.error_at(&diagnostics::This_backreference_refers_to_a_group_that_does_not_exist_There_are_no_capturing_groups_in_this_regular_expression, pos, end - pos, &[]);
                }
            }
        }
    }
}

// =============================================================================
// PORT: the flag-scanning loop of `Scanner.ReScanSlashToken` (scanner.go). It
// lives here because it is essentially flag-table parsing; the main scanner
// port will reconcile.
// =============================================================================

/// The regexp flag loop of `func (s *Scanner) ReScanSlashToken` — scans flag
/// characters starting after the closing `/` while `IsIdentifierPart` holds,
/// emitting the same diagnostics in the same order. Returns the accumulated
/// flags and the position after the last flag character.
pub(crate) fn scan_regular_expression_flags(
    text: &[u8],
    mut pos: usize,
    end: usize,
    should_report_errors: bool,
    language_version: ScriptTarget,
    on_error: &mut ErrorCallback,
) -> (RegularExpressionFlags, usize) {
    let mut reg_exp_flags = RegularExpressionFlags::NONE;
    while pos < end {
        let (ch, size) = decode_rune_in_string(&text[pos..]);
        if ch == RUNE_ERROR || !is_identifier_part(ch) {
            break;
        }
        if should_report_errors {
            match char_code_to_reg_exp_flag(ch) {
                None => {
                    on_error(
                        &diagnostics::Unknown_regular_expression_flag,
                        pos,
                        size,
                        &[],
                    );
                }
                Some(flag) if reg_exp_flags.intersects(flag) => {
                    on_error(
                        &diagnostics::Duplicate_regular_expression_flag,
                        pos,
                        size,
                        &[],
                    );
                }
                Some(flag)
                    if (reg_exp_flags | flag)
                        .contains(RegularExpressionFlags::ANY_UNICODE_MODE) =>
                {
                    on_error(&diagnostics::The_Unicode_u_flag_and_the_Unicode_Sets_v_flag_cannot_be_set_simultaneously, pos, size, &[]);
                }
                Some(flag) => {
                    reg_exp_flags |= flag;
                    check_regular_expression_flag_availability(
                        language_version,
                        flag,
                        pos,
                        size,
                        on_error,
                    );
                }
            }
        }
        pos += size;
    }
    (reg_exp_flags, pos)
}

// =============================================================================
// PORT: local ports of the Scanner helpers from scanner.go that regexp.go
// needs (Go shares one package; here the owner is still in flight). These are
// `pub(crate)` so scanner.rs can reconcile them onto the real `Scanner`.
// =============================================================================

/// `type identifierVariant int32`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum IdentifierVariant {
    #[allow(dead_code)] // used by scanner.rs's identifier paths, not regexp.go
    Standard,
    Jsx,
    RegExpGroupName,
}

/// `type EscapeSequenceScanningFlags int32`
pub(crate) type EscapeSequenceScanningFlags = u32;

pub(crate) const ESCAPE_SEQUENCE_SCANNING_FLAGS_STRING: EscapeSequenceScanningFlags = 1 << 0;
pub(crate) const ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_ERRORS: EscapeSequenceScanningFlags = 1 << 1;
pub(crate) const ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION: EscapeSequenceScanningFlags =
    1 << 2;
pub(crate) const ESCAPE_SEQUENCE_SCANNING_FLAGS_ANNEX_B: EscapeSequenceScanningFlags = 1 << 3;
pub(crate) const ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE: EscapeSequenceScanningFlags =
    1 << 4;
pub(crate) const ESCAPE_SEQUENCE_SCANNING_FLAGS_ATOM_ESCAPE: EscapeSequenceScanningFlags = 1 << 5;
pub(crate) const ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS:
    EscapeSequenceScanningFlags = ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION
    | ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_ERRORS;
#[allow(dead_code)]
pub(crate) const ESCAPE_SEQUENCE_SCANNING_FLAGS_ALLOW_EXTENDED_UNICODE_ESCAPE:
    EscapeSequenceScanningFlags =
    ESCAPE_SEQUENCE_SCANNING_FLAGS_STRING | ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE;

impl RegExpParser<'_> {
    /// `func (s *Scanner) scanIdentifier`
    fn scan_identifier(&mut self, prefix_length: usize, variant: IdentifierVariant) -> bool {
        let start = self.pos;
        self.pos += prefix_length;
        let identifier_start = self.pos;
        let ch = self.char();
        // Fast path for simple ASCII identifiers
        if variant != IdentifierVariant::Jsx
            && (is_ascii_letter(ch) || ch == i32::from(b'_') || ch == i32::from(b'$'))
        {
            self.pos += 1;
            self.scan_ascii_while(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'$');
            let ch = self.char();
            if ch < RUNE_SELF && ch != i32::from(b'\\') {
                self.token_value = self.text()[start..self.pos].to_vec();
                return true;
            }
            self.pos = identifier_start;
        }
        let (mut ch, mut size) = self.char_and_size();
        if is_identifier_start(ch) {
            let language_variant = if variant == IdentifierVariant::Jsx {
                LanguageVariant::Jsx
            } else {
                LanguageVariant::Standard
            };
            loop {
                self.pos += size;
                let next = self.char_and_size();
                (ch, size) = next;
                if !is_identifier_part_ex(ch, language_variant) {
                    break;
                }
            }
            self.token_value = self.text()[start..self.pos].to_vec();
            if ch == i32::from(b'\\') {
                let parts = self.scan_identifier_parts(variant);
                self.token_value.extend_from_slice(&parts);
            }
            return true;
        }
        // PORT: `if ch == '\\' && let Some(escaped) = ...` can't be written as
        // a let-chain before Rust 1.88 (workspace MSRV is 1.85), so the escape
        // is bound first.
        let escaped = if ch == i32::from(b'\\') {
            self.scan_identifier_escape(
                is_identifier_start,
                variant == IdentifierVariant::RegExpGroupName,
            )
        } else {
            None
        };
        if let Some(escaped) = escaped {
            self.token_value = self.text()[start..identifier_start].to_vec();
            self.token_value
                .extend_from_slice(&stringutil::encode_js_string_rune(escaped));
            let parts = self.scan_identifier_parts(variant);
            self.token_value.extend_from_slice(&parts);
            return true;
        }
        false
    }

    /// `func (s *Scanner) scanIdentifierParts`
    fn scan_identifier_parts(&mut self, variant: IdentifierVariant) -> Vec<u8> {
        let mut sb = Vec::new();
        let mut start = self.pos;
        let language_variant = if variant == IdentifierVariant::Jsx {
            LanguageVariant::Jsx
        } else {
            LanguageVariant::Standard
        };
        loop {
            let (ch, size) = self.char_and_size();
            if is_identifier_part_ex(ch, language_variant) {
                self.pos += size;
                continue;
            }
            if ch == i32::from(b'\\') {
                let escape_start = self.pos;
                if let Some(escaped) = self.scan_identifier_escape(
                    |ch| is_identifier_part_ex(ch, language_variant),
                    variant == IdentifierVariant::RegExpGroupName,
                ) {
                    sb.extend_from_slice(&self.text()[start..escape_start]);
                    sb.extend_from_slice(&stringutil::encode_js_string_rune(escaped));
                    start = self.pos;
                    continue;
                }
            }
            break;
        }
        sb.extend_from_slice(&self.text()[start..self.pos]);
        sb
    }

    /// `func (s *Scanner) scanIdentifierEscape`
    ///
    /// Go returns `(rune, bool)`; `None` is `(0, false)`.
    fn scan_identifier_escape(
        &mut self,
        is_valid: impl Fn(i32) -> bool,
        allow_surrogate_pair_escape: bool,
    ) -> Option<i32> {
        let escaped = self.peek_unicode_escape();
        if escaped >= 0 && is_valid(escaped) {
            return Some(self.scan_unicode_escape(true));
        }
        if allow_surrogate_pair_escape
            && self.char_at_offset(2) != i32::from(b'{')
            && stringutil::is_high_surrogate(escaped)
        {
            // Unlike normal identifiers, group names in regular expressions, whether in Unicode mode or not,
            // accept \u HexLeadSurrogate \u HexTrailSurrogate as part of RegExpIdentifierName.
            // See https://github.com/tc39/ecma262/pull/1869 for the change.
            let saved_pos = self.pos;
            let saved_token_flags = self.token_flags;
            self.scan_unicode_escape(false);
            // scanLowSurrogateEscape also accepts the braced form used in string literals,
            // but RegExpIdentifierName does not allow it.
            // PORT: `if ... { if let Some(cp) = ... { if is_valid(cp) { ... } } }`
            // flattened via filter() since let-chains need Rust 1.88+.
            let code_point = if self.char_at_offset(2) != i32::from(b'{') {
                self.scan_low_surrogate_escape(escaped)
            } else {
                None
            };
            if let Some(code_point) = code_point.filter(|&cp| is_valid(cp)) {
                return Some(code_point);
            }
            self.pos = saved_pos;
            self.token_flags = saved_token_flags;
        }
        None
    }

    /// `func (s *Scanner) scanEscapeSequence`
    fn scan_escape_sequence(&mut self, flags: EscapeSequenceScanningFlags) -> Vec<u8> {
        let start = self.pos;
        self.pos += 1;
        let ch = self.char();
        if ch < 0 {
            self.error(&diagnostics::Unexpected_end_of_text);
            return Vec::new();
        }
        self.pos += 1;
        match ch {
            c if c == i32::from(b'0') && !is_digit(self.char()) => {
                // Although '0' preceding any digit is treated as LegacyOctalEscapeSequence,
                // '\08' should separately be interpreted as '\0' + '8'.
                vec![0x00]
            }
            c if (i32::from(b'0')..=i32::from(b'7')).contains(&c) => {
                // PORT: Go's `case '0'` falls through into '1'-'3', which falls
                // through into '4'-'7' — flattened here. '0'-'3' may consume a
                // second octal digit; '0'-'7' may then consume one more.
                if c <= i32::from(b'3') && is_octal_digit(self.char()) {
                    self.pos += 1;
                }
                if is_octal_digit(self.char()) {
                    self.pos += 1;
                }
                self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS) != 0 {
                    let code = i64::from_str_radix(
                        std::str::from_utf8(&self.text()[start + 1..self.pos]).unwrap_or(""),
                        8,
                    )
                    .unwrap_or(i64::MAX);
                    if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION) != 0
                        && (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ATOM_ESCAPE) == 0
                        && c != i32::from(b'0')
                    {
                        self.error_at(&diagnostics::Octal_escape_sequences_and_backreferences_are_not_allowed_in_a_character_class_If_this_was_intended_as_an_escape_sequence_use_the_syntax_0_instead, start, self.pos - start, &[format!("\\x{code:02x}")]);
                    } else {
                        self.error_at(
                            &diagnostics::Octal_escape_sequences_are_not_allowed_Use_the_syntax_0,
                            start,
                            self.pos - start,
                            &[format!("\\x{code:02x}")],
                        );
                    }
                    return stringutil::encode_js_string_rune(code as i32);
                }
                self.text()[start..self.pos].to_vec()
            }
            c if c == i32::from(b'8') || c == i32::from(b'9') => {
                // the invalid '\8' and '\9'
                self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS) != 0 {
                    if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION) != 0
                        && (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ATOM_ESCAPE) == 0
                    {
                        self.error_at(&diagnostics::Decimal_escape_sequences_and_backreferences_are_not_allowed_in_a_character_class, start, self.pos - start, &[]);
                    } else {
                        self.error_at(
                            &diagnostics::Escape_sequence_0_is_not_allowed,
                            start,
                            self.pos - start,
                            &[String::from_utf8_lossy(&self.text()[start..self.pos]).into_owned()],
                        );
                    }
                    return stringutil::encode_js_string_rune(ch);
                }
                self.text()[start..self.pos].to_vec()
            }
            c if c == i32::from(b'b') => b"\x08".to_vec(),
            c if c == i32::from(b't') => b"\t".to_vec(),
            c if c == i32::from(b'n') => b"\n".to_vec(),
            c if c == i32::from(b'v') => b"\x0b".to_vec(),
            c if c == i32::from(b'f') => b"\x0c".to_vec(),
            c if c == i32::from(b'r') => b"\r".to_vec(),
            c if c == i32::from(b'\'') => b"'".to_vec(),
            c if c == i32::from(b'"') => b"\"".to_vec(),
            c if c == i32::from(b'u') => {
                // '\uDDDD' and '\u{DDDDDD}'
                let extended = self.byte() == Some(b'{');
                self.pos -= 2;
                let code_point = self.scan_unicode_escape(
                    (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS) != 0,
                );
                if extended {
                    if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ALLOW_EXTENDED_UNICODE_ESCAPE) == 0 {
                        self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                        if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS)
                            != 0
                        {
                            self.error_at(&diagnostics::Unicode_escape_sequences_are_only_available_when_the_Unicode_u_flag_or_the_Unicode_Sets_v_flag_is_set, start, self.pos - start, &[]);
                        }
                    }
                    if code_point < 0 {
                        return self.text()[start..self.pos].to_vec();
                    }
                    // In string literals, a high surrogate \u{...} followed by a low
                    // surrogate escape forms a single code point, exactly as adjacent
                    // UTF-16 code units would in a JavaScript string.
                    // PORT: `if flags&RE == 0 && isHighSurrogate { if let Some(c) = ... }`
                    // flattened since let-chains need Rust 1.88+.
                    let combined = if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION)
                        == 0
                        && stringutil::is_high_surrogate(code_point)
                    {
                        self.scan_low_surrogate_escape(code_point)
                    } else {
                        None
                    };
                    if let Some(combined) = combined {
                        return stringutil::encode_js_string_rune(combined);
                    }
                    return stringutil::encode_js_string_rune(code_point);
                }
                if code_point < 0 {
                    return self.text()[start..self.pos].to_vec();
                } else if stringutil::is_high_surrogate(code_point) {
                    if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION) == 0 {
                        // Combine \uHigh followed by any low surrogate escape (\uLow or
                        // \u{Low}) into a single code point in string literals, matching
                        // how adjacent UTF-16 code units pair in a JavaScript string.
                        if let Some(combined) = self.scan_low_surrogate_escape(code_point) {
                            return stringutil::encode_js_string_rune(combined);
                        }
                    } else if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE) != 0
                        && self.char() == i32::from(b'\\')
                        && self.char_at_offset(1) == i32::from(b'u')
                        && self.char_at_offset(2) != i32::from(b'{')
                    {
                        // In regex AnyUnicodeMode, combine \uHigh\uLow so scanClassRanges
                        // can compare the pair numerically. In non-unicode regex mode they
                        // are separate atoms, and extended \u{...} escapes never combine.
                        let saved_pos = self.pos;
                        let next_code_point = self.scan_unicode_escape(
                            (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS)
                                != 0,
                        );
                        if stringutil::is_low_surrogate(next_code_point) {
                            return stringutil::encode_js_string_rune(
                                stringutil::surrogate_pair_to_code_point(
                                    code_point,
                                    next_code_point,
                                ),
                            );
                        }
                        self.pos = saved_pos;
                    }
                }
                // Lone surrogate: encode as CESU-8 so it survives losslessly. In a
                // non-unicode regex this also lets scanClassRanges compare it numerically.
                stringutil::encode_js_string_rune(code_point)
            }
            c if c == i32::from(b'x') => {
                // '\xDD'
                while self.pos < start + 4 {
                    if !is_hex_digit(self.char()) {
                        self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                        if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS)
                            != 0
                        {
                            self.error(&diagnostics::Hexadecimal_digit_expected);
                        }
                        return self.text()[start..self.pos].to_vec();
                    }
                    self.pos += 1;
                }
                self.token_flags |= TokenFlags::HEX_ESCAPE;
                let escaped_value = i64::from_str_radix(
                    std::str::from_utf8(&self.text()[start + 2..self.pos]).unwrap_or(""),
                    16,
                )
                .unwrap_or(i64::MAX);
                stringutil::encode_js_string_rune(escaped_value as i32)
            }
            c if c == i32::from(b'\r') || c == i32::from(b'\n') => {
                // when encountering a LineContinuation (i.e. a backslash and a line terminator sequence),
                // the line terminator is interpreted to be "the empty code unit sequence".
                // PORT: Go's `case '\r'` falls through into `case '\n'`.
                if ch == i32::from(b'\r') && self.byte() == Some(b'\n') {
                    self.pos += 1;
                }
                Vec::new()
            }
            _ => {
                // ch was read as a single byte; for multi-byte UTF-8 characters,
                // we need to decode the full rune and advance past all its bytes.
                let mut ch = ch;
                if ch >= RUNE_SELF {
                    self.pos -= 1; // back up past the single-byte advance
                    let (decoded, size) = decode_rune_in_string(&self.text()[self.pos..]);
                    ch = decoded;
                    self.pos += size;
                }
                // LineContinuation: a backslash followed by a line terminator is "the empty code unit sequence".
                if ch == 0x2028 || ch == 0x2029 {
                    return Vec::new();
                }
                if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE) != 0
                    || ((flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION) != 0
                        && (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ANNEX_B) == 0
                        && is_identifier_part(ch))
                {
                    self.error_at(
                        &diagnostics::This_character_cannot_be_escaped_in_a_regular_expression,
                        start,
                        self.pos - start,
                        &[],
                    );
                }
                stringutil::encode_js_string_rune(ch)
            }
        }
    }

    /// `func (s *Scanner) scanUnicodeEscape` — known to be at `\u`.
    fn scan_unicode_escape(&mut self, should_emit_invalid_escape_error: bool) -> i32 {
        self.pos += 2;
        let start = self.pos;
        let extended = self.byte() == Some(b'{');
        let hex_digits = if extended {
            self.pos += 1;
            self.scan_hex_digits(1, true, false)
        } else {
            self.token_flags |= TokenFlags::UNICODE_ESCAPE;
            self.scan_hex_digits(4, false, false)
        };
        if hex_digits.is_empty() {
            self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
            if should_emit_invalid_escape_error {
                self.error(&diagnostics::Hexadecimal_digit_expected);
            }
            return -1;
        }
        // Go: `strconv.ParseInt(hexDigits, 16, 32)` — the error is ignored;
        // on overflow ParseInt yields the clamped max.
        let hex_value = i64::from_str_radix(std::str::from_utf8(&hex_digits).unwrap_or(""), 16)
            .unwrap_or(i64::MAX);
        if extended {
            let mut is_invalid_extended_escape = false;
            if hex_value > 0x10FFFF {
                if should_emit_invalid_escape_error {
                    self.error_at(&diagnostics::An_extended_Unicode_escape_value_must_be_between_0x0_and_0x10FFFF_inclusive, start + 1, self.pos - start - 1, &[]);
                }
                is_invalid_extended_escape = true;
            }
            if self.pos >= self.end {
                if should_emit_invalid_escape_error {
                    self.error(&diagnostics::Unexpected_end_of_text);
                }
                is_invalid_extended_escape = true;
            } else if self.byte() == Some(b'}') {
                self.pos += 1;
            } else {
                if should_emit_invalid_escape_error {
                    self.error(&diagnostics::Unterminated_Unicode_escape_sequence);
                }
                is_invalid_extended_escape = true;
            }
            if is_invalid_extended_escape {
                self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                return -1;
            }
            self.token_flags |= TokenFlags::EXTENDED_UNICODE_ESCAPE;
        }
        hex_value as i32
    }

    /// `func (s *Scanner) scanLowSurrogateEscape`
    ///
    /// Attempts to consume a low-surrogate Unicode escape (either '\uLow' or
    /// '\u{Low}') immediately following an already-scanned high surrogate and
    /// combine them into a single supplementary code point. `None` mirrors
    /// Go's `(0, false)` and leaves pos/tokenFlags restored.
    fn scan_low_surrogate_escape(&mut self, high: i32) -> Option<i32> {
        if self.char() != i32::from(b'\\') || self.char_at_offset(1) != i32::from(b'u') {
            return None;
        }
        let saved_pos = self.pos;
        let saved_token_flags = self.token_flags;
        // Speculatively scan the escape with diagnostics suppressed: if it isn't a
        // low surrogate we rewind below, and the caller re-scans the same escape and
        // reports any error then, so reporting here would duplicate diagnostics.
        let low = self.scan_unicode_escape(false);
        if stringutil::is_low_surrogate(low) {
            return Some(stringutil::surrogate_pair_to_code_point(high, low));
        }
        self.pos = saved_pos;
        self.token_flags = saved_token_flags;
        None
    }

    /// `func (s *Scanner) peekUnicodeEscape`
    ///
    /// Current character is known to be a backslash. Check for Unicode escape of the form '\uXXXX'
    /// or '\u{XXXXXX}' and return code point value if valid Unicode escape is found. Otherwise return -1.
    fn peek_unicode_escape(&mut self) -> i32 {
        if self.char_at_offset(1) == i32::from(b'u') {
            let save_pos = self.pos;
            let save_token_flags = self.token_flags;
            let code_point = self.scan_unicode_escape(false);
            self.pos = save_pos;
            self.token_flags = save_token_flags;
            return code_point;
        }
        -1
    }

    /// `func (s *Scanner) scanHexDigits`
    fn scan_hex_digits(
        &mut self,
        min_count: usize,
        scan_as_many_as_possible: bool,
        can_have_separators: bool,
    ) -> Vec<u8> {
        let mut digit_count = 0;
        let start = self.pos;
        let mut allow_separator = false;
        let mut is_previous_token_separator = false;
        while digit_count < min_count || scan_as_many_as_possible {
            let ch = self.char();
            if is_hex_digit(ch) {
                allow_separator = can_have_separators;
                is_previous_token_separator = false;
                digit_count += 1;
            } else if can_have_separators && ch == i32::from(b'_') {
                self.token_flags |= TokenFlags::CONTAINS_SEPARATOR;
                if allow_separator {
                    allow_separator = false;
                    is_previous_token_separator = true;
                } else if is_previous_token_separator {
                    self.error_at(
                        &diagnostics::Multiple_consecutive_numeric_separators_are_not_permitted,
                        self.pos,
                        1,
                        &[],
                    );
                } else {
                    self.error_at(
                        &diagnostics::Numeric_separators_are_not_allowed_here,
                        self.pos,
                        1,
                        &[],
                    );
                }
            } else {
                break;
            }
            self.pos += 1;
        }
        if is_previous_token_separator {
            self.error_at(
                &diagnostics::Numeric_separators_are_not_allowed_here,
                self.pos - 1,
                1,
                &[],
            );
        }
        if digit_count < min_count {
            return Vec::new();
        }
        // PORT: Go's `s.hexDigitCache` memoization is dropped — the transform
        // is pure and cheap, so the digits are recomputed on every call.
        let mut digits = self.text()[start..self.pos].to_vec();
        if self.token_flags.intersects(TokenFlags::CONTAINS_SEPARATOR) {
            digits.retain(|&b| b != b'_');
        }
        digits.make_ascii_lowercase(); // standardize hex literals to lowercase
        digits
    }
}

// =============================================================================
// PORT: identifier/UTF-8 free helpers from scanner.go + unicode/utf8.
// =============================================================================

/// `func isWordCharacter(ch rune) bool` — Section 6.1.4
pub(crate) fn is_word_character(ch: i32) -> bool {
    is_ascii_letter(ch) || is_digit(ch) || ch == i32::from(b'_')
}

/// `func IsIdentifierStart(ch rune) bool`
pub(crate) fn is_identifier_start(ch: i32) -> bool {
    is_ascii_letter(ch)
        || ch == i32::from(b'_')
        || ch == i32::from(b'$')
        || ch >= RUNE_SELF
            && char::from_u32(ch as u32).is_some_and(stringutil::is_unicode_identifier_start)
}

/// `func IsIdentifierPart(ch rune) bool`
pub(crate) fn is_identifier_part(ch: i32) -> bool {
    is_identifier_part_ex(ch, LanguageVariant::Standard)
}

/// `func IsIdentifierPartEx(ch rune, languageVariant core.LanguageVariant) bool`
pub(crate) fn is_identifier_part_ex(ch: i32, language_variant: LanguageVariant) -> bool {
    is_word_character(ch)
        || ch == i32::from(b'$')
        || ch >= RUNE_SELF
            && char::from_u32(ch as u32).is_some_and(stringutil::is_unicode_identifier_part)
        || language_variant == LanguageVariant::Jsx && ch == i32::from(b'-') // ":" is part of JSXNamespacedName, but not JSXIdentifier.
}

/// `stringutil.IsASCIILetter` on a Go rune (byte or decoded code point; -1 = EOF).
fn is_ascii_letter(ch: i32) -> bool {
    matches!(u8::try_from(ch), Ok(b'a'..=b'z' | b'A'..=b'Z'))
}

/// `stringutil.IsDigit` on a Go rune.
fn is_digit(ch: i32) -> bool {
    matches!(u8::try_from(ch), Ok(b'0'..=b'9'))
}

/// `stringutil.IsOctalDigit` on a Go rune.
fn is_octal_digit(ch: i32) -> bool {
    matches!(u8::try_from(ch), Ok(b'0'..=b'7'))
}

/// `stringutil.IsHexDigit` on a Go rune.
fn is_hex_digit(ch: i32) -> bool {
    matches!(
        u8::try_from(ch),
        Ok(b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F')
    )
}

const RUNE_ERROR: i32 = 0xFFFD; // utf8.RuneError — U+FFFD
const RUNE_SELF: i32 = 0x80; // utf8.RuneSelf

/// `utf16.RuneLen` — 1 for values below 0x10000, 2 for non-BMP code points,
/// -1 for out-of-range values.
fn utf16_rune_len(ch: i32) -> i32 {
    if !(0..=0x10FFFF).contains(&ch) {
        -1
    } else if ch < 0x10000 {
        1
    } else {
        2
    }
}

/// Go `string(ch)` where a rune becomes a diagnostic arg — the UTF-8 encoding
/// of the code point; invalid runes give U+FFFD like Go.
fn rune_to_string(ch: i32) -> String {
    char::from_u32(ch as u32).unwrap_or('\u{FFFD}').to_string()
}

/// PORT: mirrors Go's utf8.DecodeRuneInString (RFC 3629-strict decoding):
/// empty input -> (RuneError, 0); invalid encoding -> (RuneError, 1);
/// otherwise the decoded rune and its width in bytes. Local copy — the
/// decoder in tsc-stringutil is crate-private (glob.rs keeps an identical
/// local port returning `char` instead of i32).
fn decode_rune_in_string(s: &[u8]) -> (i32, usize) {
    if s.is_empty() {
        return (RUNE_ERROR, 0);
    }
    let p0 = s[0];
    if p0 < 0x80 {
        return (i32::from(p0), 1);
    }
    // (size, accept range for the first continuation byte)
    let (size, lo, hi): (usize, u8, u8) = match p0 {
        0xC2..=0xDF => (2, 0x80, 0xBF),
        0xE0 => (3, 0xA0, 0xBF),
        0xE1..=0xEC => (3, 0x80, 0xBF),
        0xED => (3, 0x80, 0x9F),
        0xEE..=0xEF => (3, 0x80, 0xBF),
        0xF0 => (4, 0x90, 0xBF),
        0xF1..=0xF3 => (4, 0x80, 0xBF),
        0xF4 => (4, 0x80, 0x8F),
        _ => return (RUNE_ERROR, 1),
    };
    if s.len() < size {
        return (RUNE_ERROR, 1);
    }
    let b1 = s[1];
    if !(lo..=hi).contains(&b1) {
        return (RUNE_ERROR, 1);
    }
    let mut r = match size {
        2 => u32::from(p0 & 0x1F),
        3 => u32::from(p0 & 0x0F),
        _ => u32::from(p0 & 0x07),
    };
    r = (r << 6) | u32::from(b1 & 0x3F);
    for &b in &s[2..size] {
        if !(0x80..=0xBF).contains(&b) {
            return (RUNE_ERROR, 1);
        }
        r = (r << 6) | u32::from(b & 0x3F);
    }
    // The accept ranges above exclude surrogates and out-of-range code points.
    (char::from_u32(r).map_or(RUNE_ERROR, |c| c as i32), size)
}

#[cfg(test)]
mod tests;
