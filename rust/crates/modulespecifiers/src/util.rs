// Ported from tsc/internal/modulespecifiers/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{LazyLock, RwLock};

use rustc_hash::FxHashMap;
use tsc_collections::OrderedMap;
use tsc_core::core::index_after;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::TS_TRUE;
use tsc_module as module;
use tsc_module::Ending;
use tsc_packagejson::ExportsOrImports;
use tsc_tspath::{
    self as tspath, CaseSensitivity, ModuleSpecifier, RelativePath, RootedDirectoryPath,
    RootedFilePath, RootedPath,
};

use crate::specifiers::{get_all_module_paths, get_info, try_get_module_name_as_node_module};
use crate::types::{
    ModulePath, ModuleSpecifierEnding, ModuleSpecifierGenerationHost, ModuleSpecifierOptions,
    SourceFileForSpecifierGeneration, UserPreferences,
};

/// `type regexPatternCacheKey struct`.
#[derive(PartialEq, Eq, Hash)]
struct RegexPatternCacheKey {
    pattern: String,
    case_insensitive: bool,
}

static REGEX_PATTERN_CACHE: LazyLock<RwLock<FxHashMap<RegexPatternCacheKey, Option<Regex>>>> =
    LazyLock::new(|| RwLock::new(FxHashMap::default()));

/// `func comparePathsByRedirect(a, b ModulePath, caseSensitivity) int`.
pub(crate) fn compare_paths_by_redirect(
    a: &ModulePath,
    b: &ModulePath,
    case_sensitivity: CaseSensitivity,
) -> i32 {
    // Redirects sort first, matching Strada's compareBooleans(b.isRedirect, a.isRedirect).
    let c = tsc_core::core::compare_booleans(b.is_redirect, a.is_redirect);
    if c != 0 {
        return c;
    }
    let c = (a.file_name.directory_separator_count() as i32)
        .cmp(&(b.file_name.directory_separator_count() as i32)) as i32;
    if c != 0 {
        return c;
    }
    // Strada relies on Map insertion order to break remaining ties deterministically;
    // Go maps are unordered, so compare paths to keep the ordering stable.
    case_sensitivity.compare_file_paths(&a.file_name, &b.file_name)
}

/// `func PathIsBareSpecifier(path tspath.ModuleSpecifier) bool`.
pub fn path_is_bare_specifier(path: &ModuleSpecifier) -> bool {
    !path.is_absolute() && !path.is_relative()
}

/// `func IsExcludedByRegex(moduleSpecifier string, excludes []string) bool`.
pub fn is_excluded_by_regex(module_specifier: &str, excludes: &[String]) -> bool {
    for pattern in excludes {
        let Some(re) = string_to_regex(pattern) else {
            continue;
        };
        if re.is_match(module_specifier) {
            return true;
        }
    }
    false
}

fn string_to_regex(pattern: &str) -> Option<Regex> {
    let mut case_insensitive = false;
    let mut pattern = pattern.to_string();

    if pattern.len() > 2 && pattern.starts_with('/') {
        if let Some(last_slash) = pattern.rfind('/') {
            if last_slash > 0 {
                let bytes = pattern.as_bytes();
                let mut has_unescaped_middle_slash = false;
                let mut i = 1;
                while i < last_slash {
                    if bytes[i] == b'/' && (i == 0 || bytes[i - 1] != b'\\') {
                        has_unescaped_middle_slash = true;
                        break;
                    }
                    i += 1;
                }

                if !has_unescaped_middle_slash {
                    let flags = &pattern[last_slash + 1..];
                    for flag in flags.chars() {
                        if flag == 'i' {
                            case_insensitive = true;
                        }
                    }
                    pattern = pattern[1..last_slash].to_string();
                }
            }
        }
    }

    let key = RegexPatternCacheKey {
        pattern,
        case_insensitive,
    };

    if let Some(re) = REGEX_PATTERN_CACHE.read().unwrap().get(&key) {
        return re.clone();
    }

    let mut cache = REGEX_PATTERN_CACHE.write().unwrap();
    if let Some(re) = cache.get(&key) {
        return re.clone();
    }

    if cache.len() > 1000 {
        cache.clear();
    }

    let compiled = Regex::compile(&key.pattern, key.case_insensitive).ok();
    cache.insert(key, compiled.clone());
    compiled
}

// MARK: - minimal regex engine

// PORT: Go's `stringToRegex` compiles user-supplied exclude patterns with
// `regexp.Compile` (RE2 syntax) and `IsExcludedByRegex` calls `MatchString`.
// The `regex` crate is forbidden (SPEC §5.11), so this is a small
// Thompson-NFA (Pike VM) engine over a practical RE2 subset: literals, `.`,
// character classes (ranges, negation, `[:posix:]`, `\d\w\s` shorthands),
// `*` `+` `?` `{n,m}` quantifiers (lazy suffixes accepted — greediness is
// irrelevant for a boolean match), alternation, capturing/`(?:)`/`(?flags)`/
// `(?flags:)` groups (i, m, s, U), `^` `$` `\A` `\z` anchors, `\b` `\B`,
// `\Q...\E` quoting, and `\xHH`/`\x{...}`/octal/`\cX` escapes. Patterns using
// anything else (`\p{...}` unicode classes, octal-only quirks) fail
// compilation and are skipped, matching Go's nil-regexp skip.

#[derive(Clone)]
struct Regex {
    prog: Vec<Inst>,
}

#[derive(Clone)]
enum Inst {
    Char {
        ch: char,
        ci: bool,
    },
    /// `.` — any char except '\n' unless `nl`.
    Any {
        nl: bool,
    },
    Class {
        items: Vec<ClassItem>,
        negated: bool,
        ci: bool,
    },
    Split(usize, usize),
    Jmp(usize),
    AssertStartText,
    AssertStartLine,
    AssertEndText,
    AssertEndLine,
    WordBoundary,
    NotWordBoundary,
    Match,
}

/// One entry in a character class; `negated` entries (from `\D`/`\W`/`\S`)
/// match a char that is NOT in `ranges`.
#[derive(Clone)]
struct ClassItem {
    ranges: Vec<(char, char)>,
    negated: bool,
}

impl Regex {
    fn compile(pattern: &str, case_insensitive: bool) -> Result<Regex, ()> {
        let mut parser = Parser {
            chars: pattern.chars().collect(),
            pos: 0,
            flags: Flags {
                i: case_insensitive,
                m: false,
                s: false,
            },
        };
        let ast = parser.parse()?;
        if parser.pos != parser.chars.len() {
            return Err(());
        }
        let mut prog = Vec::new();
        emit(&ast, &mut prog);
        prog.push(Inst::Match);
        Ok(Regex { prog })
    }

    /// `re.MatchString` — unanchored search.
    fn is_match(&self, text: &str) -> bool {
        let input: Vec<char> = text.chars().collect();
        let n = input.len();
        let m = self.prog.len();
        let mut clist: Vec<usize> = Vec::new();
        let mut cmark = vec![false; m];
        let mut nlist: Vec<usize> = Vec::new();
        let mut nmark = vec![false; m];
        for pos in 0..=n {
            // Seed an unanchored start thread at this position.
            add_thread(&self.prog, &input, &mut clist, &mut cmark, 0, pos);
            for &pc in &clist {
                match &self.prog[pc] {
                    Inst::Char { ch, ci } => {
                        if pos < n && char_matches(*ch, input[pos], *ci) {
                            add_thread(&self.prog, &input, &mut nlist, &mut nmark, pc + 1, pos + 1);
                        }
                    }
                    Inst::Any { nl } => {
                        if pos < n && (*nl || input[pos] != '\n') {
                            add_thread(&self.prog, &input, &mut nlist, &mut nmark, pc + 1, pos + 1);
                        }
                    }
                    Inst::Class { items, negated, ci } => {
                        if pos < n && class_matches(items, *negated, *ci, input[pos]) {
                            add_thread(&self.prog, &input, &mut nlist, &mut nmark, pc + 1, pos + 1);
                        }
                    }
                    Inst::Match => return true,
                    _ => unreachable!("non-atom inst in thread list"),
                }
            }
            clist.clear();
            cmark.fill(false);
            std::mem::swap(&mut clist, &mut nlist);
            std::mem::swap(&mut cmark, &mut nmark);
        }
        false
    }
}

fn add_thread(
    prog: &[Inst],
    input: &[char],
    list: &mut Vec<usize>,
    mark: &mut [bool],
    pc: usize,
    pos: usize,
) {
    if mark[pc] {
        return;
    }
    mark[pc] = true;
    match &prog[pc] {
        Inst::Jmp(next) => add_thread(prog, input, list, mark, *next, pos),
        Inst::Split(a, b) => {
            add_thread(prog, input, list, mark, *a, pos);
            add_thread(prog, input, list, mark, *b, pos);
        }
        Inst::AssertStartText => {
            if pos == 0 {
                add_thread(prog, input, list, mark, pc + 1, pos);
            }
        }
        Inst::AssertStartLine => {
            if pos == 0 || input[pos - 1] == '\n' {
                add_thread(prog, input, list, mark, pc + 1, pos);
            }
        }
        Inst::AssertEndText => {
            if pos == input.len() {
                add_thread(prog, input, list, mark, pc + 1, pos);
            }
        }
        Inst::AssertEndLine => {
            if pos == input.len() || input[pos] == '\n' {
                add_thread(prog, input, list, mark, pc + 1, pos);
            }
        }
        Inst::WordBoundary => {
            if word_boundary(input, pos) {
                add_thread(prog, input, list, mark, pc + 1, pos);
            }
        }
        Inst::NotWordBoundary => {
            if !word_boundary(input, pos) {
                add_thread(prog, input, list, mark, pc + 1, pos);
            }
        }
        _ => list.push(pc),
    }
}

fn is_word_char(c: char) -> bool {
    matches!(c, '0'..='9' | 'A'..='Z' | 'a'..='z' | '_')
}

fn word_boundary(input: &[char], pos: usize) -> bool {
    let before = pos > 0 && is_word_char(input[pos - 1]);
    let after = pos < input.len() && is_word_char(input[pos]);
    before != after
}

/// Unicode-aware equality approximation for `(?i)` matching: compare the
/// simple lowercase fold of both chars (sufficient for the RE2 subset here).
fn fold(c: char) -> char {
    c.to_lowercase().next().unwrap_or(c)
}

fn char_matches(ch: char, input: char, ci: bool) -> bool {
    ch == input || (ci && fold(ch) == fold(input))
}

fn class_matches(items: &[ClassItem], negated: bool, ci: bool, c: char) -> bool {
    let mut matched = false;
    for item in items {
        let mut in_ranges = item.ranges.iter().any(|&(lo, hi)| lo <= c && c <= hi);
        if !in_ranges && ci {
            let c = fold(c);
            in_ranges = item
                .ranges
                .iter()
                .any(|&(lo, hi)| fold(lo) <= c && c <= fold(hi));
        }
        if in_ranges != item.negated {
            matched = true;
            break;
        }
    }
    matched != negated
}

// === regex AST / parser ===

#[derive(Clone, Copy)]
struct Flags {
    i: bool,
    m: bool,
    s: bool,
}

enum Ast {
    Empty,
    Char {
        ch: char,
        ci: bool,
    },
    Any {
        nl: bool,
    },
    Class {
        items: Vec<ClassItem>,
        negated: bool,
        ci: bool,
    },
    AssertStart {
        line: bool,
    },
    AssertEnd {
        line: bool,
    },
    WordBoundary(bool),
    Concat(Vec<Ast>),
    Alt(Vec<Ast>),
    Repeat {
        node: Box<Ast>,
        min: u32,
        max: Option<u32>,
    },
}

struct Parser {
    chars: Vec<char>,
    pos: usize,
    flags: Flags,
}

impl Parser {
    fn parse(&mut self) -> Result<Ast, ()> {
        self.parse_alt()
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += 1;
        Some(c)
    }

    fn parse_alt(&mut self) -> Result<Ast, ()> {
        let mut branches = vec![self.parse_concat()?];
        while self.peek() == Some('|') {
            self.pos += 1;
            branches.push(self.parse_concat()?);
        }
        if branches.len() == 1 {
            Ok(branches.pop().unwrap())
        } else {
            Ok(Ast::Alt(branches))
        }
    }

    fn parse_concat(&mut self) -> Result<Ast, ()> {
        let mut items = Vec::new();
        while let Some(c) = self.peek() {
            if c == ')' || c == '|' {
                break;
            }
            items.push(self.parse_repeat()?);
        }
        Ok(Ast::Concat(items))
    }

    fn parse_repeat(&mut self) -> Result<Ast, ()> {
        let atom = self.parse_atom()?;
        let (min, max) = match self.peek() {
            Some('*') => {
                self.pos += 1;
                (0, None)
            }
            Some('+') => {
                self.pos += 1;
                (1, None)
            }
            Some('?') => {
                self.pos += 1;
                (0, Some(1))
            }
            Some('{') => {
                // A '{' that does not introduce a valid counted repetition is
                // an error in RE2 (it is not a literal).
                match self.try_parse_counted_repeat() {
                    Some(bounds) => bounds,
                    None => return Err(()),
                }
            }
            _ => return Ok(atom),
        };
        // A trailing '?' makes the quantifier lazy; irrelevant for boolean matching.
        if self.peek() == Some('?') {
            self.pos += 1;
        }
        if min == 1 && max == Some(1) {
            return Ok(atom);
        }
        Ok(Ast::Repeat {
            node: Box::new(atom),
            min,
            max,
        })
    }

    fn try_parse_counted_repeat(&mut self) -> Option<(u32, Option<u32>)> {
        let save = self.pos;
        self.pos += 1; // '{'
        let min = self.parse_decimal()?;
        let max = match self.peek() {
            Some('}') => {
                self.pos += 1;
                Some(min)
            }
            Some(',') => {
                self.pos += 1;
                if self.peek() == Some('}') {
                    self.pos += 1;
                    None
                } else {
                    let hi = self.parse_decimal()?;
                    if self.peek() == Some('}') {
                        self.pos += 1;
                        Some(hi)
                    } else {
                        self.pos = save;
                        return None;
                    }
                }
            }
            _ => {
                self.pos = save;
                return None;
            }
        };
        // RE2 rejects counts above 1000.
        if min > 1000 || max.is_some_and(|m| m > 1000 || m < min) {
            return None;
        }
        Some((min, max))
    }

    fn parse_decimal(&mut self) -> Option<u32> {
        let mut value = 0u32;
        let mut digits = 0;
        while let Some(c) = self.peek() {
            if !c.is_ascii_digit() {
                break;
            }
            self.pos += 1;
            digits += 1;
            value = value.checked_mul(10)?.checked_add(c as u32 - '0' as u32)?;
            if value > 100_000 {
                return None;
            }
        }
        if digits == 0 { None } else { Some(value) }
    }

    fn parse_atom(&mut self) -> Result<Ast, ()> {
        let c = self.bump().ok_or(())?;
        match c {
            '(' => self.parse_group(),
            '[' => self.parse_class(),
            '.' => Ok(Ast::Any { nl: self.flags.s }),
            '^' => Ok(Ast::AssertStart { line: self.flags.m }),
            '$' => Ok(Ast::AssertEnd { line: self.flags.m }),
            '\\' => self.parse_escape(false),
            // Quantifiers without an argument are an error in RE2.
            '*' | '+' | '?' | '{' | '}' => Err(()),
            _ => Ok(Ast::Char {
                ch: c,
                ci: self.flags.i,
            }),
        }
    }

    fn parse_group(&mut self) -> Result<Ast, ()> {
        let saved_flags = self.flags;
        if self.peek() == Some('?') {
            // (?:...), (?flags), (?flags:...)
            self.pos += 1;
            let mut negate = false;
            let mut flags = self.flags;
            let mut saw_flag = false;
            loop {
                match self.bump() {
                    Some('i') => {
                        flags.i = !negate;
                        saw_flag = true;
                    }
                    Some('m') => {
                        flags.m = !negate;
                        saw_flag = true;
                    }
                    Some('s') => {
                        flags.s = !negate;
                        saw_flag = true;
                    }
                    // RE2's U (ungreedy) is accepted but meaningless for a
                    // boolean match.
                    Some('U') => saw_flag = true,
                    Some('-') if !negate => negate = true,
                    Some(':') => {
                        self.flags = flags;
                        let inner = self.parse_alt()?;
                        if self.bump() != Some(')') {
                            return Err(());
                        }
                        self.flags = saved_flags;
                        return Ok(inner);
                    }
                    Some(')') => {
                        // `(?flags)` sets flags for the rest of the enclosing
                        // group — mutate self.flags and do not restore the
                        // flag change itself (only non-flag syntax restores).
                        self.flags = flags;
                        if !saw_flag {
                            // `(?-...)`-only or empty: still legal flag-only form.
                        }
                        return Ok(Ast::Empty);
                    }
                    _ => return Err(()),
                }
            }
        }
        let inner = self.parse_alt()?;
        if self.bump() != Some(')') {
            return Err(());
        }
        // Flags set inside the group do not escape it.
        self.flags = saved_flags;
        Ok(inner)
    }

    /// Parses a `\`-escape. `in_class` selects whether the result feeds a
    /// character class (where `\d` etc. produce class items instead of atoms).
    fn parse_escape(&mut self, in_class: bool) -> Result<Ast, ()> {
        let c = self.bump().ok_or(())?;
        let shorthand = |ranges: Vec<(char, char)>, negated: bool| Ast::Class {
            items: vec![ClassItem { ranges, negated }],
            negated: false,
            ci: self.flags.i,
        };
        match c {
            'a' => Ok(Ast::Char {
                ch: '\x07',
                ci: false,
            }),
            'f' => Ok(Ast::Char {
                ch: '\x0c',
                ci: false,
            }),
            'n' => Ok(Ast::Char {
                ch: '\n',
                ci: false,
            }),
            'r' => Ok(Ast::Char {
                ch: '\r',
                ci: false,
            }),
            't' => Ok(Ast::Char {
                ch: '\t',
                ci: false,
            }),
            'v' => Ok(Ast::Char {
                ch: '\x0b',
                ci: false,
            }),
            'A' if !in_class => Ok(Ast::AssertStart { line: false }),
            'z' if !in_class => Ok(Ast::AssertEnd { line: false }),
            'b' if !in_class => Ok(Ast::WordBoundary(true)),
            'B' if !in_class => Ok(Ast::WordBoundary(false)),
            'd' => Ok(shorthand(vec![('0', '9')], false)),
            'D' => Ok(shorthand(vec![('0', '9')], true)),
            's' => Ok(shorthand(
                vec![('\t', '\n'), ('\x0b', '\r'), (' ', ' ')],
                false,
            )),
            'S' => Ok(shorthand(
                vec![('\t', '\n'), ('\x0b', '\r'), (' ', ' ')],
                true,
            )),
            'w' => Ok(shorthand(
                vec![('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')],
                false,
            )),
            'W' => Ok(shorthand(
                vec![('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')],
                true,
            )),
            'x' => self.parse_hex_escape().map(|ch| Ast::Char {
                ch,
                ci: self.flags.i,
            }),
            'c' => {
                // `\cX` control character.
                let x = self.bump().ok_or(())?;
                if !x.is_ascii_alphabetic() {
                    return Err(());
                }
                Ok(Ast::Char {
                    ch: char::from_u32((x as u32) & 0x1f).unwrap(),
                    ci: false,
                })
            }
            'Q' => {
                // \Q...\E — literal quoting.
                let mut items = Vec::new();
                loop {
                    match self.bump() {
                        None => break,
                        Some('\\') if self.peek() == Some('E') => {
                            self.pos += 1;
                            break;
                        }
                        Some(lit) => items.push(Ast::Char {
                            ch: lit,
                            ci: self.flags.i,
                        }),
                    }
                }
                Ok(Ast::Concat(items))
            }
            '0'..='7' => {
                // Octal escape: RE2 requires exactly 3 digits (`\ooo`) with a
                // value <= 0o377; shorter forms like `\1` are (invalid)
                // backreferences, not octal.
                let mut value = c as u32 - '0' as u32;
                for _ in 0..2 {
                    match self.peek() {
                        Some(d @ '0'..='7') => {
                            self.pos += 1;
                            value = value * 8 + (d as u32 - '0' as u32);
                        }
                        _ => return Err(()),
                    }
                }
                if value > 0o377 {
                    return Err(());
                }
                let ch = char::from_u32(value).ok_or(())?;
                Ok(Ast::Char {
                    ch,
                    ci: self.flags.i,
                })
            }
            'p' | 'P' => {
                // `\p{Name}` unicode classes are outside the supported subset.
                Err(())
            }
            '1'..='9' => {
                // Backreferences are not valid RE2.
                Err(())
            }
            // Escaped punctuation/other non-word chars are literals.
            _ if !c.is_alphanumeric() => Ok(Ast::Char {
                ch: c,
                ci: self.flags.i,
            }),
            _ => Err(()),
        }
    }

    fn parse_hex_escape(&mut self) -> Result<char, ()> {
        if self.peek() == Some('{') {
            self.pos += 1;
            let mut value = 0u32;
            let mut digits = 0;
            while let Some(c) = self.peek() {
                if c == '}' {
                    break;
                }
                let d = c.to_digit(16).ok_or(())?;
                self.pos += 1;
                digits += 1;
                value = value
                    .checked_mul(16)
                    .and_then(|v| v.checked_add(d))
                    .ok_or(())?;
            }
            if digits == 0 || self.bump() != Some('}') {
                return Err(());
            }
            char::from_u32(value).ok_or(())
        } else {
            // Exactly two hex digits.
            let mut value = 0u32;
            for _ in 0..2 {
                let c = self.bump().ok_or(())?;
                value = value * 16 + c.to_digit(16).ok_or(())?;
            }
            char::from_u32(value).ok_or(())
        }
    }

    fn parse_class(&mut self) -> Result<Ast, ()> {
        let mut negated = false;
        if self.peek() == Some('^') {
            self.pos += 1;
            negated = true;
        }
        let mut items: Vec<ClassItem> = Vec::new();
        let mut pending: Option<char> = None;
        let mut first = true;
        loop {
            let c = self.bump().ok_or(())?;
            if c == ']' && !first {
                break;
            }
            first = false;
            // POSIX class [:alpha:]
            if c == '[' && self.peek() == Some(':') {
                let save = self.pos;
                self.pos += 1;
                let mut posix_negated = false;
                if self.peek() == Some('^') {
                    self.pos += 1;
                    posix_negated = true;
                }
                let name_start = self.pos;
                while matches!(self.peek(), Some(c) if c.is_ascii_alphabetic()) {
                    self.pos += 1;
                }
                let name: String = self.chars[name_start..self.pos].iter().collect();
                if self.peek() == Some(':') && self.chars.get(self.pos + 1) == Some(&']') {
                    self.pos += 2;
                    if let Some(ranges) = posix_class_ranges(&name) {
                        items.push(ClassItem {
                            ranges,
                            negated: posix_negated,
                        });
                        if let Some(lo) = pending.take() {
                            items.insert(
                                items.len() - 1,
                                ClassItem {
                                    ranges: vec![(lo, lo)],
                                    negated: false,
                                },
                            );
                        }
                        continue;
                    }
                }
                // Not a POSIX class — rewind and treat '[' as a literal.
                self.pos = save;
                if let Some(lo) = pending.take() {
                    items.push(ClassItem {
                        ranges: vec![(lo, lo)],
                        negated: false,
                    });
                }
                pending = Some('[');
                continue;
            }
            let lo = if c == '\\' {
                match self.parse_escape(true)? {
                    Ast::Char { ch, .. } => ch,
                    Ast::Class {
                        items: sub_items,
                        negated: false,
                        ..
                    } => {
                        // \d \w \s (and negated forms) inside a class merge
                        // into the item list.
                        if let Some(prev) = pending.take() {
                            items.push(ClassItem {
                                ranges: vec![(prev, prev)],
                                negated: false,
                            });
                        }
                        items.extend(sub_items);
                        continue;
                    }
                    _ => return Err(()),
                }
            } else {
                c
            };
            // Range?
            if self.peek() == Some('-')
                && self.chars.get(self.pos + 1).is_some()
                && self.chars[self.pos + 1] != ']'
            {
                self.pos += 1;
                let hi_c = self.bump().unwrap();
                let hi = if hi_c == '\\' {
                    match self.parse_escape(true)? {
                        Ast::Char { ch, .. } => ch,
                        _ => return Err(()),
                    }
                } else {
                    hi_c
                };
                if let Some(prev) = pending.take() {
                    items.push(ClassItem {
                        ranges: vec![(prev, prev)],
                        negated: false,
                    });
                }
                if hi < lo {
                    return Err(());
                }
                items.push(ClassItem {
                    ranges: vec![(lo, hi)],
                    negated: false,
                });
            } else if let Some(prev) = pending.replace(lo) {
                items.push(ClassItem {
                    ranges: vec![(prev, prev)],
                    negated: false,
                });
            }
        }
        if let Some(lo) = pending.take() {
            items.push(ClassItem {
                ranges: vec![(lo, lo)],
                negated: false,
            });
        }
        if items.is_empty() {
            return Err(());
        }
        Ok(Ast::Class {
            items,
            negated,
            ci: self.flags.i,
        })
    }
}

fn posix_class_ranges(name: &str) -> Option<Vec<(char, char)>> {
    let ranges = match name {
        "alnum" => vec![('0', '9'), ('A', 'Z'), ('a', 'z')],
        "alpha" => vec![('A', 'Z'), ('a', 'z')],
        "ascii" => vec![('\x00', '\x7f')],
        "blank" => vec![('\t', '\t'), (' ', ' ')],
        "cntrl" => vec![('\x00', '\x1f'), ('\x7f', '\x7f')],
        "digit" => vec![('0', '9')],
        "graph" => vec![('!', '~')],
        "lower" => vec![('a', 'z')],
        "print" => vec![(' ', '~')],
        "punct" => vec![('!', '/'), (':', '@'), ('[', '`'), ('{', '~')],
        "space" => vec![('\t', '\r'), (' ', ' ')],
        "upper" => vec![('A', 'Z')],
        "word" => vec![('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')],
        "xdigit" => vec![('0', '9'), ('A', 'F'), ('a', 'f')],
        _ => return None,
    };
    Some(ranges)
}

// === compiler: AST -> program ===

fn emit(ast: &Ast, prog: &mut Vec<Inst>) {
    match ast {
        Ast::Empty => {}
        Ast::Char { ch, ci } => prog.push(Inst::Char { ch: *ch, ci: *ci }),
        Ast::Any { nl } => prog.push(Inst::Any { nl: *nl }),
        Ast::Class { items, negated, ci } => prog.push(Inst::Class {
            items: items.clone(),
            negated: *negated,
            ci: *ci,
        }),
        Ast::AssertStart { line } => prog.push(if *line {
            Inst::AssertStartLine
        } else {
            Inst::AssertStartText
        }),
        Ast::AssertEnd { line } => prog.push(if *line {
            Inst::AssertEndLine
        } else {
            Inst::AssertEndText
        }),
        Ast::WordBoundary(yes) => prog.push(if *yes {
            Inst::WordBoundary
        } else {
            Inst::NotWordBoundary
        }),
        Ast::Concat(items) => {
            for item in items {
                emit(item, prog);
            }
        }
        Ast::Alt(branches) => {
            let mut jmp_pcs = Vec::new();
            for (i, branch) in branches.iter().enumerate() {
                if i + 1 < branches.len() {
                    let split_pc = prog.len();
                    prog.push(Inst::Split(usize::MAX, usize::MAX));
                    let body = prog.len();
                    emit(branch, prog);
                    jmp_pcs.push(prog.len());
                    prog.push(Inst::Jmp(usize::MAX));
                    prog[split_pc] = Inst::Split(body, prog.len());
                } else {
                    emit(branch, prog);
                }
            }
            let after = prog.len();
            for pc in jmp_pcs {
                prog[pc] = Inst::Jmp(after);
            }
        }
        Ast::Repeat { node, min, max } => {
            for _ in 0..*min {
                emit(node, prog);
            }
            match max {
                None => {
                    // loop: split(body, after); body; jmp loop; after:
                    let loop_pc = prog.len();
                    prog.push(Inst::Split(usize::MAX, usize::MAX));
                    let body = prog.len();
                    emit(node, prog);
                    prog.push(Inst::Jmp(loop_pc));
                    prog[loop_pc] = Inst::Split(body, prog.len());
                }
                Some(max) => {
                    let mut splits = Vec::new();
                    for _ in *min..*max {
                        let split_pc = prog.len();
                        prog.push(Inst::Split(usize::MAX, usize::MAX));
                        splits.push(split_pc);
                        emit(node, prog);
                    }
                    let after = prog.len();
                    for pc in splits {
                        let Inst::Split(a, _) = prog[pc] else {
                            unreachable!()
                        };
                        prog[pc] = Inst::Split(a, after);
                    }
                }
            }
        }
    }
}

// MARK: - exported helpers

/// `func GetJSExtensionForDeclarationFileExtension(ext string) string`.
pub fn get_js_extension_for_declaration_file_extension(ext: &str) -> &str {
    match ext {
        tspath::EXTENSION_DTS => tspath::EXTENSION_JS,
        tspath::EXTENSION_DMTS => tspath::EXTENSION_MJS,
        tspath::EXTENSION_DCTS => tspath::EXTENSION_CJS,
        // .d.json.ts and the like
        _ => &ext[".d".len()..ext.len() - tspath::EXTENSION_TS.len()],
    }
}

/// TryGetRealFileNameForNonJSDeclarationFileName remaps files like `foo.d.json.ts` or
/// `foo.module.d.css.ts` back to their real non-JS names.
///
// PORT: the Go original returns a freshly-built `before + ext` string, so
// this returns `String` ("" when not a non-JS declaration file name).
pub fn try_get_real_file_name_for_non_js_declaration_file_name(file_name: &str) -> String {
    let base_name = tspath::get_base_file_name(file_name);
    // Ends with .ts, contains ".d.", and is NOT a standard .d.ts file
    if !file_name.ends_with(tspath::EXTENSION_TS)
        || !base_name.contains(".d.")
        || base_name.ends_with(tspath::EXTENSION_DTS)
    {
        return String::new();
    }
    let no_extension = tspath::remove_extension(file_name, tspath::EXTENSION_TS);
    let last_dot_index = no_extension.rfind('.').unwrap();
    let ext = &no_extension[last_dot_index..];
    let before = match no_extension.split_once(".d.") {
        Some((before, _)) => before,
        None => no_extension,
    };
    format!("{before}{ext}")
}

pub(crate) fn get_js_extension_for_file(file_name: &str, options: &CompilerOptions) -> String {
    let result = module::try_get_js_extension_for_file(file_name, options);
    if result.is_empty() {
        panic!(
            "Extension {} is unsupported:: FileName:: {}",
            extension_from_path(file_name),
            file_name
        );
    }
    result.to_string()
}

pub(crate) fn get_js_extension_for_file_name(
    file_name: &RootedFilePath,
    options: &CompilerOptions,
) -> String {
    let result = module::try_get_js_extension_for_file_name(file_name, options);
    if result.is_empty() {
        panic!(
            "Extension {} is unsupported:: FileName:: {}",
            file_name.extension(),
            file_name.as_string()
        );
    }
    result.to_string()
}

/// Gets the extension from a path.
/// Path must have a valid extension.
pub(crate) fn extension_from_path(path: &str) -> &str {
    let ext = tspath::try_get_extension_from_path(path);
    if ext.is_empty() {
        panic!("File {path} has unknown extension.");
    }
    ext
}

pub(crate) fn try_get_any_file_from_path<H: ModuleSpecifierGenerationHost>(
    host: &H,
    path: &RootedFilePath,
) -> bool {
    // !!! TODO: shouldn't this use readdir instead of fileexists for perf?
    // We check all js, `node` and `json` extensions in addition to TS, since node module resolution would also choose those over the directory
    let options = CompilerOptions {
        allow_js: TS_TRUE,
        ..Default::default()
    };
    let extra: [String; 2] = [".node".to_string(), tspath::EXTENSION_JSON.to_string()];
    for exts in tsc_tsoptions::tsconfigparsing::get_supported_extensions(&options, &extra) {
        for e in &exts {
            if host.file_exists(&path.append_suffix(e)) {
                return true;
            }
        }
    }
    false
}

pub(crate) fn get_paths_relative_to_root_dirs(
    path: &RootedFilePath,
    root_dirs: &[RootedDirectoryPath],
    case_sensitivity: CaseSensitivity,
) -> Vec<RelativePath> {
    let mut results = Vec::new();
    for root_dir in root_dirs {
        let relative_path = get_relative_path_if_in_same_volume(path, root_dir, case_sensitivity);
        if !is_path_relative_to_parent(&relative_path) {
            results.push(relative_path);
        }
    }
    results
}

pub(crate) fn is_path_relative_to_parent(path: &RelativePath) -> bool {
    path.is_parent_relative()
}

pub(crate) fn get_relative_path_if_in_same_volume(
    path: &RootedFilePath,
    directory_path: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> RelativePath {
    match case_sensitivity.relative_path_from_directory(directory_path, path) {
        Some(relative_path) => relative_path,
        None => RelativePath::default(),
    }
}

pub(crate) fn resolve_path_pattern_if_in_same_volume(
    path: &str,
    directory_path: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> String {
    let relative_path = tspath::resolve_relative_path_to_directory_or_url(
        directory_path.as_string(),
        path,
        false,
        directory_path,
        case_sensitivity,
    );

    if tspath::is_rooted_disk_path(&relative_path) {
        return String::new();
    }
    relative_path
}

pub(crate) fn package_json_paths_are_equal(
    a: &RootedDirectoryPath,
    b: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> bool {
    if a == b {
        return true;
    }
    if a.is_empty() || b.is_empty() {
        return false;
    }
    case_sensitivity.compare_paths(&a.as_path(), &b.as_path()) == 0
}

pub(crate) fn prefers_ts_extension(allowed_endings: &[ModuleSpecifierEnding]) -> bool {
    let js_priority = allowed_endings
        .iter()
        .position(|&e| e == ModuleSpecifierEnding::JsExtension)
        .map(|p| p as i32)
        .unwrap_or(-1);
    let ts_priority = allowed_endings
        .iter()
        .position(|&e| e == ModuleSpecifierEnding::TsExtension)
        .map(|p| p as i32)
        .unwrap_or(-1);
    if ts_priority > -1 {
        return ts_priority < js_priority;
    }
    false
}

pub(crate) fn replace_first_star(s: &str, replacement: &str) -> String {
    s.replacen('*', replacement, 1)
}

/// `type NodeModulePathParts struct`.
#[derive(Debug, Default)]
pub struct NodeModulePathParts {
    /// `TopLevelNodeModulesSearchRoot`.
    pub top_level_node_modules_search_root: RootedDirectoryPath,
    /// `TopLevelNodeModulesDirectory`.
    pub top_level_node_modules_directory: RootedDirectoryPath,
    /// `PackageRootDirectory`.
    pub package_root_directory: RootedDirectoryPath,
    /// `PackageName`.
    pub package_name: String,
    /// `PackageRelativePath`.
    pub package_relative_path: RelativePath,
    /// `HasNestedNodeModules`.
    pub has_nested_node_modules: bool,
    /// `IsDirectNodeModulesFile`.
    pub is_direct_node_modules_file: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum NodeModulesPathParseState {
    BeforeNodeModules,
    NodeModules,
    Scope,
    PackageContent,
}

/// `func GetNodeModulePathParts(fileName tspath.RootedFilePath) *NodeModulePathParts`.
pub fn get_node_module_path_parts(file_name: &RootedFilePath) -> Option<NodeModulePathParts> {
    let full_path = file_name.as_string();
    let mut top_level_node_modules_index: i64 = -1;
    let mut package_name_start: i64 = -1;
    let mut package_root_index: i64 = -1;
    let mut has_nested_node_modules = false;
    let mut part_end: i64 = 0;
    let mut state = NodeModulesPathParseState::BeforeNodeModules;

    while part_end >= 0 {
        let part_start = part_end;
        part_end = index_after(full_path, "/", (part_start + 1) as usize) as i64;
        match state {
            NodeModulesPathParseState::BeforeNodeModules => {
                if full_path[part_start as usize..].starts_with("/node_modules/") {
                    top_level_node_modules_index = part_start;
                    state = NodeModulesPathParseState::NodeModules;
                }
            }
            NodeModulesPathParseState::NodeModules => {
                package_name_start = part_start + 1;
                if package_name_start as usize >= full_path.len() {
                    return None;
                }
                if full_path.as_bytes()[package_name_start as usize] == b'@' {
                    state = NodeModulesPathParseState::Scope;
                } else {
                    package_root_index = part_end;
                    state = NodeModulesPathParseState::PackageContent;
                }
            }
            NodeModulesPathParseState::Scope => {
                package_root_index = part_end;
                state = NodeModulesPathParseState::PackageContent;
            }
            NodeModulesPathParseState::PackageContent => {
                if full_path[part_start as usize..].starts_with("/node_modules/") {
                    has_nested_node_modules = true;
                    state = NodeModulesPathParseState::NodeModules;
                }
            }
        }
    }

    if top_level_node_modules_index == -1 || package_name_start == -1 {
        return None;
    }

    let root_length = file_name.root_length();
    let search_root_end = (top_level_node_modules_index as usize).max(root_length);
    let top_level_node_modules_search_root =
        tspath::rooted_directory_path_from_normalized(&full_path[..search_root_end]);
    let top_level_node_modules_directory = tspath::rooted_directory_path_from_normalized(
        &full_path[..top_level_node_modules_index as usize + "/node_modules".len()],
    );
    if package_root_index == -1 {
        return Some(NodeModulePathParts {
            top_level_node_modules_search_root,
            top_level_node_modules_directory,
            package_name: full_path[package_name_start as usize..].to_string(),
            has_nested_node_modules,
            is_direct_node_modules_file: true,
            ..Default::default()
        });
    }
    let package_root_directory =
        tspath::rooted_directory_path_from_normalized(&full_path[..package_root_index as usize]);
    Some(NodeModulePathParts {
        top_level_node_modules_search_root,
        top_level_node_modules_directory,
        package_root_directory,
        package_name: full_path[package_name_start as usize..package_root_index as usize]
            .to_string(),
        package_relative_path: tspath::relative_path_from_normalized(
            &full_path[package_root_index as usize + 1..],
        ),
        has_nested_node_modules,
        is_direct_node_modules_file: false,
    })
}

/// `func GetNodeModulesPackageName(...)`.
pub fn get_node_modules_package_name<S, H>(
    compiler_options: &CompilerOptions,
    importing_source_file: &S,
    node_modules_file_name: &RootedFilePath,
    host: &H,
    preferences: &UserPreferences,
    options: &ModuleSpecifierOptions,
    nodes: &[tsc_ast::ast::Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifier
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let info = get_info(importing_source_file.file_name(), host);
    let module_paths = get_all_module_paths(
        &info,
        node_modules_file_name,
        host,
        compiler_options,
        preferences,
        options,
    );
    for module_path in &module_paths {
        let result = try_get_module_name_as_node_module(
            module_path,
            &info,
            importing_source_file,
            host,
            compiler_options,
            preferences,
            true, // packageNameOnly
            options.override_import_mode,
            nodes,
            resolve,
        );
        if !result.is_empty() {
            return result;
        }
    }
    ModuleSpecifier::default()
}

// `func allKeysStartWithDot(obj) bool` — dead code in the Go source (no
// callers); ported for completeness.
#[allow(dead_code)]
fn all_keys_start_with_dot(obj: &OrderedMap<String, ExportsOrImports>) -> bool {
    for k in obj.keys() {
        if !k.starts_with('.') {
            return false;
        }
    }
    true
}

/// `func GetPackageNameFromDirectory(path tspath.RootedPath) string`.
pub fn get_package_name_from_directory(path: &RootedPath) -> &str {
    let file_or_directory_path = path.as_string();
    let Some((_, basename)) = file_or_directory_path.rsplit_once("/node_modules/") else {
        return "";
    };

    if basename.as_bytes()[0] == b'.' {
        return "";
    }

    let Some(next_slash) = basename.find('/') else {
        return basename;
    };

    if basename.as_bytes()[0] != b'@' || next_slash == basename.len() - 1 {
        return &basename[..next_slash];
    }

    let Some(second_slash) = basename[next_slash + 1..].find('/') else {
        return basename;
    };

    &basename[..next_slash + 1 + second_slash]
}

/// ProcessEntrypointEnding processes a pre-computed module specifier from a package.json exports
/// entrypoint according to the entrypoint's Ending type and the user's preferred endings.
///
/// `func ProcessEntrypointEnding(...)`.
pub fn process_entrypoint_ending<S, H>(
    entrypoint: &module::ResolvedEntrypoint,
    prefs: &UserPreferences,
    host: &H,
    options: &CompilerOptions,
    importing_source_file: &S,
    allowed_endings: &[ModuleSpecifierEnding],
    nodes: &[tsc_ast::ast::Node],
    resolve: crate::types::NodeResolver,
) -> ModuleSpecifier
where
    S: SourceFileForSpecifierGeneration,
    H: ModuleSpecifierGenerationHost,
{
    let mut specifier = entrypoint.module_specifier.as_string().to_string();
    if entrypoint.ending == Ending::Fixed {
        return entrypoint.module_specifier.clone();
    }

    let allowed_endings = if allowed_endings.is_empty() {
        crate::preferences::get_allowed_endings_in_preferred_order(
            prefs,
            host,
            options,
            importing_source_file,
            "",
            host.get_default_resolution_mode_for_file(importing_source_file),
            nodes,
            resolve,
        )
    } else {
        allowed_endings.to_vec()
    };

    let preferred_ending = allowed_endings[0];

    // Handle declaration file extensions
    let dts_extension = tspath::get_declaration_file_extension(&specifier);
    if !dts_extension.is_empty() {
        match preferred_ending {
            ModuleSpecifierEnding::TsExtension | ModuleSpecifierEnding::JsExtension => {
                // Map .d.ts -> .js, .d.mts -> .mjs, .d.cts -> .cjs
                let js_extension = get_js_extension_for_declaration_file_extension(&dts_extension);
                return tspath::to_module_specifier(&tspath::change_any_extension(
                    &specifier,
                    js_extension,
                    &[&dts_extension],
                    CaseSensitivity::CaseSensitive,
                ));
            }
            ModuleSpecifierEnding::Minimal | ModuleSpecifierEnding::Index => {
                if entrypoint.ending == Ending::Changeable {
                    // .d.mts/.d.cts must keep an extension; rewrite to .mjs/.cjs instead of dropping
                    if dts_extension == tspath::EXTENSION_DTS {
                        specifier =
                            tspath::remove_extension(&specifier, &dts_extension).to_string();
                        if preferred_ending == ModuleSpecifierEnding::Minimal {
                            specifier = specifier
                                .strip_suffix("/index")
                                .unwrap_or(&specifier)
                                .to_string();
                        }
                        return tspath::to_module_specifier(&specifier);
                    }
                    let js_extension =
                        get_js_extension_for_declaration_file_extension(&dts_extension);
                    return tspath::to_module_specifier(&tspath::change_any_extension(
                        &specifier,
                        js_extension,
                        &[&dts_extension],
                        CaseSensitivity::CaseSensitive,
                    ));
                }
                // EndingExtensionChangeable - can only change extension, not remove it
                let js_extension = get_js_extension_for_declaration_file_extension(&dts_extension);
                return tspath::to_module_specifier(&tspath::change_any_extension(
                    &specifier,
                    js_extension,
                    &[&dts_extension],
                    CaseSensitivity::CaseSensitive,
                ));
            }
        }
    }

    // Handle .ts/.tsx/.mts/.cts extensions
    if tspath::file_extension_is_one_of(
        &specifier,
        &[
            tspath::EXTENSION_TS,
            tspath::EXTENSION_TSX,
            tspath::EXTENSION_MTS,
            tspath::EXTENSION_CTS,
        ],
    ) {
        match preferred_ending {
            ModuleSpecifierEnding::TsExtension => {
                return tspath::to_module_specifier(&specifier);
            }
            ModuleSpecifierEnding::JsExtension => {
                let js_extension = module::try_get_js_extension_for_file(&specifier, options);
                if !js_extension.is_empty() {
                    return tspath::to_module_specifier(&format!(
                        "{}{}",
                        tspath::remove_file_extension(&specifier),
                        js_extension
                    ));
                }
                return tspath::to_module_specifier(&specifier);
            }
            ModuleSpecifierEnding::Minimal | ModuleSpecifierEnding::Index => {
                if entrypoint.ending == Ending::Changeable {
                    specifier = tspath::remove_file_extension(&specifier).to_string();
                    if preferred_ending == ModuleSpecifierEnding::Minimal {
                        specifier = specifier
                            .strip_suffix("/index")
                            .unwrap_or(&specifier)
                            .to_string();
                    }
                    return tspath::to_module_specifier(&specifier);
                }
                // EndingExtensionChangeable - can only change extension, not remove it
                let js_extension = module::try_get_js_extension_for_file(&specifier, options);
                if !js_extension.is_empty() {
                    return tspath::to_module_specifier(&format!(
                        "{}{}",
                        tspath::remove_file_extension(&specifier),
                        js_extension
                    ));
                }
                return tspath::to_module_specifier(&specifier);
            }
        }
    }

    // Handle .js/.jsx/.mjs/.cjs extensions
    if tspath::file_extension_is_one_of(
        &specifier,
        &[
            tspath::EXTENSION_JS,
            tspath::EXTENSION_JSX,
            tspath::EXTENSION_MJS,
            tspath::EXTENSION_CJS,
        ],
    ) {
        match preferred_ending {
            ModuleSpecifierEnding::TsExtension | ModuleSpecifierEnding::JsExtension => {
                return tspath::to_module_specifier(&specifier);
            }
            ModuleSpecifierEnding::Minimal | ModuleSpecifierEnding::Index => {
                if entrypoint.ending == Ending::Changeable {
                    specifier = tspath::remove_file_extension(&specifier).to_string();
                    if preferred_ending == ModuleSpecifierEnding::Minimal {
                        specifier = specifier
                            .strip_suffix("/index")
                            .unwrap_or(&specifier)
                            .to_string();
                    }
                    return tspath::to_module_specifier(&specifier);
                }
                // EndingExtensionChangeable - keep the extension
                return tspath::to_module_specifier(&specifier);
            }
        }
    }

    // For other extensions (like .json), return as-is
    tspath::to_module_specifier(&specifier)
}
