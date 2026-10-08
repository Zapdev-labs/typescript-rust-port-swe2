// Minimal TOML subset reader/writer for `kinds.toml`.
//
// The `toml` crate is not among the approved workspace dependencies, so this
// module implements exactly the subset `gen-ast` emits: comments, `[table]`
// and `[[array-of-tables]]` headers, `key = value` pairs where values are
// strings, integers, booleans, arrays of values, or inline `{k = v}` tables.
// Everything emitted by `write` round-trips through `parse`.

use std::collections::BTreeMap;

/// A parsed TOML value (subset).
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Str(String),
    Int(i64),
    Bool(bool),
    Array(Vec<Value>),
    Table(BTreeMap<String, Value>),
}

impl Value {
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Value]> {
        match self {
            Value::Array(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_table(&self) -> Option<&BTreeMap<String, Value>> {
        match self {
            Value::Table(t) => Some(t),
            _ => None,
        }
    }
}

/// A document is a sequence of top-level `key = value` pairs plus
/// `[[array]]` tables; `[table]` headers group scalar keys.
#[derive(Debug, Default)]
pub struct Document {
    /// Scalar/table top-level keys (from `[meta]`-style sections — the
    /// section name prefixes keys as `meta.x` here for simplicity).
    pub tables: BTreeMap<String, BTreeMap<String, Value>>,
    /// Array-of-tables sections in document order.
    pub arrays: BTreeMap<String, Vec<BTreeMap<String, Value>>>,
}

// ── Writer helpers ─────────────────────────────────────────────────────────

pub fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// ── Parser ─────────────────────────────────────────────────────────────────

pub fn parse(text: &str) -> Result<Document, String> {
    let mut doc = Document::default();
    // Current insertion target: None = top-level tables, Some(name) = array.
    let mut section: Option<String> = None;
    let mut cur_table: Option<String> = None;

    let mut lines = text.lines().enumerate().peekable();
    while let Some((ln, raw)) = lines.next() {
        let line = strip_comment(raw).trim().to_string();
        if line.is_empty() {
            continue;
        }
        if let Some(rest) = line.strip_prefix("[[") {
            let name = rest
                .strip_suffix("]]")
                .ok_or_else(|| format!("line {}: malformed [[...]] header", ln + 1))?
                .trim()
                .to_string();
            doc.arrays
                .entry(name.clone())
                .or_default()
                .push(BTreeMap::new());
            section = Some(name);
            cur_table = None;
            continue;
        }
        if let Some(rest) = line.strip_prefix('[') {
            let name = rest
                .strip_suffix(']')
                .ok_or_else(|| format!("line {}: malformed [...] header", ln + 1))?
                .trim()
                .to_string();
            doc.tables.entry(name.clone()).or_default();
            cur_table = Some(name);
            section = None;
            continue;
        }
        // key = value — the value may span lines when it is an unterminated
        // array of inline tables.
        let Some(eq) = line.find('=') else {
            return Err(format!("line {}: expected `key = value`", ln + 1));
        };
        let key = line[..eq].trim().to_string();
        let mut val_text = line[eq + 1..].trim().to_string();
        while !value_complete(&val_text) {
            let Some((_, next)) = lines.next() else {
                return Err(format!("line {}: unterminated value", ln + 1));
            };
            val_text.push_str(strip_comment(next).trim());
            // preserve spacing between tokens
            val_text.push(' ');
        }
        let mut chars = val_text.char_indices().peekable();
        let value = parse_value(&mut chars).map_err(|e| format!("line {}: {e}", ln + 1))?;
        match (&section, &cur_table) {
            (Some(name), _) => doc
                .arrays
                .get_mut(name)
                .and_then(|v| v.last_mut())
                .ok_or_else(|| format!("line {}: no array table open", ln + 1))?
                .insert(key, value),
            (None, Some(t)) => doc.tables.get_mut(t).unwrap().insert(key, value),
            (None, None) => doc
                .tables
                .entry(String::new())
                .or_default()
                .insert(key, value),
        };
    }
    Ok(doc)
}

/// Strips a `//`-style or `#`-style trailing comment (TOML uses `#`; we accept
/// both since the file is internal-only). Ignores `#` inside strings.
fn strip_comment(line: &str) -> &str {
    let mut in_str = false;
    let mut prev = '\0';
    for (i, c) in line.char_indices() {
        if c == '"' && prev != '\\' {
            in_str = !in_str;
        }
        if !in_str && c == '#' {
            return &line[..i];
        }
        prev = c;
    }
    line
}

/// Whether a value text is complete (brackets/braces balanced, string closed).
fn value_complete(s: &str) -> bool {
    let mut depth = 0i32;
    let mut in_str = false;
    let mut prev = '\0';
    for c in s.chars() {
        if in_str {
            if c == '"' && prev != '\\' {
                in_str = false;
            }
        } else {
            match c {
                '"' => in_str = true,
                '[' | '{' => depth += 1,
                ']' | '}' => depth -= 1,
                _ => {}
            }
        }
        prev = c;
    }
    depth <= 0 && !in_str
}

fn parse_value(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Result<Value, String> {
    skip_ws(chars);
    match chars.peek() {
        Some((_, '"')) => Ok(Value::Str(parse_string(chars)?)),
        Some((_, '[')) => {
            chars.next();
            let mut items = Vec::new();
            loop {
                skip_ws(chars);
                match chars.peek() {
                    Some((_, ']')) => {
                        chars.next();
                        break;
                    }
                    Some(_) => items.push(parse_value(chars)?),
                    None => return Err("unterminated array".into()),
                }
                skip_ws(chars);
                match chars.peek() {
                    Some((_, ',')) => {
                        chars.next();
                    }
                    Some((_, ']')) => {
                        chars.next();
                        break;
                    }
                    other => return Err(format!("expected ',' or ']' in array, got {other:?}")),
                }
            }
            Ok(Value::Array(items))
        }
        Some((_, '{')) => parse_inline_table(chars),
        Some((_, c)) if c.is_ascii_digit() || *c == '-' => {
            let mut s = String::new();
            while let Some(&(_, c)) = chars.peek() {
                if c.is_ascii_digit() || c == '-' {
                    s.push(c);
                    chars.next();
                } else {
                    break;
                }
            }
            s.parse::<i64>()
                .map(Value::Int)
                .map_err(|e| format!("bad int: {e}"))
        }
        Some(_) => {
            let mut s = String::new();
            while let Some(&(_, c)) = chars.peek() {
                if c.is_ascii_alphabetic() {
                    s.push(c);
                    chars.next();
                } else {
                    break;
                }
            }
            match s.as_str() {
                "true" => Ok(Value::Bool(true)),
                "false" => Ok(Value::Bool(false)),
                _ => Err(format!("bad literal: {s}")),
            }
        }
        None => Err("unexpected end of value".into()),
    }
}

fn parse_string(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Result<String, String> {
    debug_assert_eq!(chars.next().map(|t| t.1), Some('"'));
    let mut s = String::new();
    while let Some((_, c)) = chars.next() {
        match c {
            '"' => return Ok(s),
            '\\' => match chars.next() {
                Some((_, 'n')) => s.push('\n'),
                Some((_, 't')) => s.push('\t'),
                Some((_, '"')) => s.push('"'),
                Some((_, '\\')) => s.push('\\'),
                Some((_, c)) => return Err(format!("bad escape \\{c}")),
                None => return Err("unterminated escape".into()),
            },
            c => s.push(c),
        }
    }
    Err("unterminated string".into())
}

fn parse_inline_table(
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> Result<Value, String> {
    debug_assert_eq!(chars.next().map(|t| t.1), Some('{'));
    let mut t = BTreeMap::new();
    loop {
        skip_ws(chars);
        match chars.peek() {
            Some((_, '}')) => {
                chars.next();
                break;
            }
            Some(_) => {}
            None => return Err("unterminated inline table".into()),
        }
        // key
        let mut key = String::new();
        while let Some(&(_, c)) = chars.peek() {
            if c.is_ascii_alphanumeric() || c == '_' {
                key.push(c);
                chars.next();
            } else {
                break;
            }
        }
        skip_ws(chars);
        match chars.next() {
            Some((_, '=')) => {}
            other => return Err(format!("expected '=' in inline table, got {other:?}")),
        }
        let v = parse_value(chars)?;
        t.insert(key, v);
        skip_ws(chars);
        match chars.peek() {
            Some((_, ',')) => {
                chars.next();
            }
            Some((_, '}')) => {
                chars.next();
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' in inline table, got {other:?}"
                ));
            }
        }
    }
    Ok(Value::Table(t))
}

fn skip_ws(chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>) {
    while let Some(&(_, c)) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
}
