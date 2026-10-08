// Go-source bootstrap: parses tsc/internal/ast/{kind_generated.go,
// ast_generated.go, ast.go} into the `Schema` model, which is then written as
// `kinds.toml`. This runs once (`gen-ast bootstrap`); afterwards the TOML is
// the source of truth.
//
// The parser is line-oriented — the generated Go files are emitted by
// tools/scripts/tsc/generate-go-ast.ts in a fixed style: one field per line,
// one statement per line, method bodies that always `return` a single
// expression. Anything it can't classify is a hard error rather than a guess.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use crate::model::*;

pub fn bootstrap(dir: &Path) -> Result<Schema, String> {
    let mut schema = Schema::default();
    let kind_src = std::fs::read_to_string(dir.join("kind_generated.go"))
        .map_err(|e| format!("kind_generated.go: {e}"))?;
    let ast_src = std::fs::read_to_string(dir.join("ast_generated.go"))
        .map_err(|e| format!("ast_generated.go: {e}"))?;
    let ast_hand = std::fs::read_to_string(dir.join("ast.go"))
        .map_err(|e| format!("ast.go: {e}"))?;

    parse_kinds(&kind_src, &mut schema)?;
    parse_ast(&ast_src, &mut schema)?;
    parse_hand(&ast_hand, &mut schema)?;
    postprocess(&mut schema)?;
    Ok(schema)
}

// ── kind_generated.go ──────────────────────────────────────────────────────

fn parse_kinds(src: &str, schema: &mut Schema) -> Result<(), String> {
    let mut in_const = false;
    let mut in_type = false;
    for (ln, raw) in src.lines().enumerate() {
        let line = raw.trim_end();
        let code = line.split("//").next().unwrap_or("").trim();
        if code.is_empty() {
            continue;
        }
        if code == "const (" {
            in_const = true;
            continue;
        }
        if code == "type (" {
            in_type = true;
            continue;
        }
        if code == ")" {
            in_const = false;
            in_type = false;
            continue;
        }
        if in_const {
            // `KindUnknown Kind = iota` | `KindEndOfFile` | `KindFirstX = KindY`
            if let Some(eq) = code.find('=') {
                let lhs = code[..eq].trim();
                let rhs = code[eq + 1..].trim();
                let lhs = lhs.split_whitespace().next().unwrap_or(lhs);
                if rhs == "iota" {
                    push_kind(schema, lhs, ln)?;
                } else {
                    schema.kind_consts.push(KindConst {
                        name: lhs.to_string(),
                        value: rhs.strip_prefix("Kind").unwrap_or(rhs).to_string(),
                    });
                }
            } else {
                push_kind(schema, code, ln)?;
            }
        } else if in_type {
            // `TokenSyntaxKind = Kind // KindX | KindY ...`
            let Some(eq) = code.find('=') else {
                return Err(format!("kind_generated.go:{} bad type alias: {code}", ln + 1));
            };
            let name = code[..eq].trim().to_string();
            let kinds: Vec<String> = raw
                .split("//")
                .nth(1)
                .map(|c| {
                    c.split('|')
                        .map(|k| k.trim().strip_prefix("Kind").unwrap_or(k.trim()).to_string())
                        .filter(|k| !k.is_empty())
                        .collect()
                })
                .unwrap_or_default();
            schema.kind_aliases.push(KindAlias { name, kinds });
        }
    }
    if schema.kinds.is_empty() {
        return Err("kind_generated.go: no kinds found".into());
    }
    Ok(())
}

fn push_kind(schema: &mut Schema, name: &str, ln: usize) -> Result<(), String> {
    let Some(short) = name.strip_prefix("Kind") else {
        return Err(format!("kind_generated.go:{} bad kind name {name}", ln + 1));
    };
    schema.kinds.push(short.to_string());
    Ok(())
}

// ── name/type helpers ──────────────────────────────────────────────────────

/// Go type string → `FieldType` (+ whether `*Node`-like).
fn go_field_type(ty: &str) -> FieldType {
    match ty {
        "string" => FieldType::Str,
        "bool" => FieldType::Bool,
        "int" | "int32" | "int64" => FieldType::Int,
        "NodeFlags" => FieldType::NodeFlags,
        "TokenFlags" => FieldType::TokenFlags,
        "any" => FieldType::Any,
        "atomic.Uint32" => FieldType::AtomicU32,
        "SymbolTable" => FieldType::SymbolTable,
        "*Symbol" => FieldType::Symbol,
        "*FlowNode" | "*FlowLabel" => FieldType::FlowNode,
        "*FlowList" => FieldType::FlowList,
        "[]*Node" => FieldType::NodeSlice,
        "[]string" => FieldType::StringSlice,
        "*ModifierList" => FieldType::ModifierList,
        t if t.starts_with('*') => {
            let inner = &t[1..];
            // `*TypeNode`, `*Expression` etc. are `= Node` aliases; `*XxxList`
            // are `= NodeList` aliases — except ModifierList handled above.
            if inner.ends_with("List") {
                FieldType::NodeList
            } else {
                FieldType::Node
            }
        }
        t if t.ends_with("SyntaxKind")
            || matches!(
                t,
                "Kind"
                    | "PostfixUnaryOperator"
                    | "PrefixUnaryOperator"
                    | "BinaryOperator"
                    | "AssignmentOperator"
                    | "ExponentiationOperator"
                    | "MultiplicativeOperator"
                    | "MultiplicativeOperatorOrHigher"
                    | "AdditiveOperator"
                    | "AdditiveOperatorOrHigher"
                    | "ShiftOperator"
                    | "ShiftOperatorOrHigher"
                    | "RelationalOperator"
                    | "RelationalOperatorOrHigher"
                    | "EqualityOperator"
                    | "EqualityOperatorOrHigher"
                    | "BitwiseOperator"
                    | "BitwiseOperatorOrHigher"
                    | "LogicalOperator"
                    | "LogicalOperatorOrHigher"
                    | "CompoundAssignmentOperator"
                    | "AssignmentOperatorOrHigher"
                    | "LogicalOrCoalescingAssignmentOperator"
                    | "ImportPhaseModifierSyntaxKind"
                    | "JSDocNodeSyntaxKind"
            ) =>
        {
            FieldType::Kind
        }
        _ => FieldType::Other,
    }
}

/// Go identifier → Rust snake_case. Exported or not, fields use this for
/// their `name`. Rust keywords get a `_` suffix.
pub fn rust_name(go: &str) -> String {
    let mut out = String::with_capacity(go.len() + 4);
    let bytes = go.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        let c = b as char;
        if c.is_ascii_uppercase() {
            // Boundary: lower→upper always; upper→upper only when the next
            // char is lowercase (acronym end): "JSDocText" → "jsdoc_text",
            // "TypeArguments" → "type_arguments", "EndOfFile" → "end_of_file".
            let prev_lower = i > 0 && bytes[i - 1].is_ascii_lowercase();
            let acronym_end = i > 0
                && i + 1 < bytes.len()
                && bytes[i + 1].is_ascii_lowercase()
                && bytes[i - 1].is_ascii_uppercase();
            if i > 0 && (prev_lower || acronym_end) {
                out.push('_');
            }
            out.push(c.to_ascii_lowercase());
        } else {
            out.push(c);
        }
    }
    match out.as_str() {
        "type" => "type_".into(),
        "mod" | "ref" | "box" | "loop" | "move" | "self" | "super" | "crate" | "fn" | "for"
        | "if" | "in" | "let" | "match" | "pub" | "struct" | "enum" | "const" | "static"
        | "trait" | "impl" | "use" | "while" | "yield" | "mut" | "extern" | "unsafe"
        | "return" | "break" | "continue" | "else" | "as" | "where" | "async" | "await"
        | "dyn" | "gen" => format!("{out}_"),
        _ => out,
    }
}

/// Splits `s` on `sep` at paren/bracket/brace depth 0.
fn split_top_level(s: &str, sep: char) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
        if c == sep && depth == 0 {
            out.push(std::mem::take(&mut cur));
        } else {
            cur.push(c);
        }
    }
    out.push(cur);
    out
}

/// Splits on a multi-char operator like `||` or `&&` at depth 0.
fn split_top_level_op(s: &str, op: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    let mut i = 0;
    while i < s.len() {
        let c = s.as_bytes()[i] as char;
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
        if depth == 0 && s[i..].starts_with(op) {
            out.push(std::mem::take(&mut cur));
            i += op.len();
            continue;
        }
        cur.push(c);
        i += 1;
    }
    out.push(cur);
    out
}

/// Finds the byte index of the `)` matching the `(` at byte index `open`.
fn matching_paren(s: &str, open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, b) in s.bytes().enumerate().skip(open) {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Extracts the argument list of the first `marker(...)` call in `text`.
fn extract_call(text: &str, marker: &str) -> Option<(String, Vec<String>)> {
    let pos = text.find(marker)?;
    let open = pos + marker.len();
    if text.as_bytes().get(open) != Some(&b'(') {
        return None;
    }
    let close = matching_paren(text, open)?;
    let args = split_top_level(&text[open + 1..close], ',')
        .into_iter()
        .map(|a| a.trim().to_string())
        .collect();
    Some((marker.to_string(), args))
}

struct FuncSig {
    recv_ty: String,
    name: String,
    args: Vec<(String, String)>,
    body: String,
}

/// Splits `a T, b U` into name/type pairs.
fn split_args(args: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for part in split_top_level(args, ',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let mut it = part.rsplitn(2, ' ');
        let ty = it.next().unwrap_or("").trim();
        let name = it.next().unwrap_or("").trim();
        for n in name.split(',') {
            out.push((n.trim().to_string(), ty.to_string()));
        }
    }
    out
}

/// Collects a top-level `func` starting at line `start`. Returns the sig and
/// the index of the closing `}` line.
fn read_func(lines: &[&str], start: usize) -> Result<(FuncSig, usize), String> {
    let header = lines[start].trim();
    // Single-line body: `func (x *T) M() R { return x.f }`. The `{...}` body
    // must be peeled off so the signature loop below doesn't eat the next
    // function header while hunting for a trailing `{`.
    if !header.ends_with('{')
        && let Some(open) = header.find('{')
        && header.ends_with('}')
    {
        let sig = header[..open].trim().strip_prefix("func ").unwrap_or(header[..open].trim());
        let (recv_ty, rest) = if let Some(r) = sig.strip_prefix('(') {
            let close = r.find(')').ok_or("bad receiver")?;
            let recv = &r[..close];
            let ty = recv.rsplit(' ').next().unwrap_or("").trim_start_matches('*');
            (ty.to_string(), r[close + 1..].trim().to_string())
        } else {
            (String::new(), sig.to_string())
        };
        let paren = rest.find('(').ok_or("bad func sig")?;
        let name = rest[..paren].trim().to_string();
        let args_end = matching_paren(&rest, paren).ok_or("bad func args")?;
        let args = split_args(&rest[paren + 1..args_end]);
        let body = format!("{}\n", header[open + 1..header.len() - 1].trim());
        return Ok((FuncSig { recv_ty, name, args, body }, start));
    }
    let (sig, body_start) = if header.ends_with('{') {
        (header[..header.len() - 1].trim().to_string(), start + 1)
    } else {
        // multi-line signature — join until `{`
        let mut s = header.to_string();
        let mut i = start + 1;
        while !s.ends_with('{') {
            s.push(' ');
            s.push_str(lines[i].trim());
            i += 1;
        }
        s = s[..s.len() - 1].trim().to_string();
        (s, i)
    };
    let sig = sig.strip_prefix("func ").unwrap_or(&sig).to_string();
    let (recv_ty, rest) = if let Some(r) = sig.strip_prefix('(') {
        let close = r.find(')').ok_or("bad receiver")?;
        let recv = &r[..close];
        let ty = recv.rsplit(' ').next().unwrap_or("").trim_start_matches('*');
        (ty.to_string(), r[close + 1..].trim().to_string())
    } else {
        (String::new(), sig)
    };
    let paren = rest.find('(').ok_or("bad func sig")?;
    let name = rest[..paren].trim().to_string();
    let args_end = matching_paren(&rest, paren).ok_or("bad func args")?;
    let args = split_args(&rest[paren + 1..args_end]);
    let mut body = String::new();
    let mut i = body_start;
    while i < lines.len() {
        let l = lines[i];
        if l == "}" {
            break;
        }
        body.push_str(l.trim());
        body.push('\n');
        i += 1;
    }
    Ok((FuncSig { recv_ty, name, args, body }, i))
}

fn parse_field(line: &str, ln: usize) -> Result<Field, String> {
    // `Name Type // Optional` | `EmbeddedBase` | `Name Type`
    let (code, optional) = match line.split_once("//") {
        Some((c, comment)) => (c.trim(), comment.trim() == "Optional"),
        None => (line.trim(), false),
    };
    let mut parts = code.split_whitespace();
    let first = parts.next().unwrap_or("");
    let second = parts.next();
    let (go_name, ty) = match second {
        None => (first, ""), // embedded
        Some(t) => (first, t),
    };
    if ty.is_empty() {
        return Ok(Field {
            go_name: go_name.to_string(),
            name: rust_name(go_name),
            ty: FieldType::Embed,
            embed: Some(go_name.to_string()),
            optional,
            exported: go_name.chars().next().is_some_and(|c| c.is_ascii_uppercase()),
            rust_ty: None,
        });
    }
    let fty = go_field_type(ty);
    if fty == FieldType::Other {
        // Unknown field types are hard errors in generated code — extend
        // `go_field_type`.
        return Err(format!("line {ln}: unhandled field type `{ty}` for {go_name}"));
    }
    Ok(Field {
        go_name: go_name.to_string(),
        name: rust_name(go_name),
        ty: fty,
        embed: None,
        optional,
        exported: go_name.chars().next().is_some_and(|c| c.is_ascii_uppercase()),
        rust_ty: None,
    })
}

/// Collects `type X struct { ... }` fields. Caller positioned on the header
/// line; returns (fields, index of `}` line).
fn read_struct_fields(lines: &[&str], header_idx: usize) -> Result<(Vec<Field>, usize), String> {
    let mut fields = Vec::new();
    let mut i = header_idx + 1;
    while i < lines.len() && lines[i].trim() != "}" {
        let fl = lines[i].trim();
        if !fl.is_empty() && !fl.starts_with("//") {
            fields.push(parse_field(fl, i + 1)?);
        }
        i += 1;
    }
    Ok((fields, i))
}

// ── ast_generated.go ───────────────────────────────────────────────────────

fn parse_ast(src: &str, schema: &mut Schema) -> Result<(), String> {
    let lines: Vec<&str> = src.lines().collect();
    let mut i = 0;
    let mut structs: Vec<(String, Vec<Field>)> = Vec::new();
    let mut funcs: Vec<FuncSig> = Vec::new();
    while i < lines.len() {
        let t = lines[i].trim();
        if t.starts_with("type ") && t.ends_with("struct {") {
            let name = t[5..t.len() - 8].trim().to_string();
            if name == "NodeFactory" {
                // arenas/hooks — skip without field parsing
                while lines[i].trim() != "}" {
                    i += 1;
                }
                i += 1;
                continue;
            }
            let (fields, end) = read_struct_fields(&lines, i)?;
            structs.push((name, fields));
            i = end + 1;
            continue;
        }
        if t.starts_with("func ") {
            let (sig, end) = read_func(&lines, i)?;
            funcs.push(sig);
            i = end + 1;
            continue;
        }
        i += 1;
    }

    for (name, fields) in &structs {
        if name == "NodeFactory" || name == "NodeList" || name == "ModifierList" {
            continue;
        }
        if name.ends_with("Base") {
            schema.bases.push(BaseDef {
                name: name.clone(),
                fields: fields.clone(),
            });
        } else {
            schema.nodes.push(NodeDef {
                name: name.clone(),
                rust_name: None,
                kinds: Vec::new(),
                bases: fields
                    .iter()
                    .filter(|f| f.ty == FieldType::Embed)
                    .map(|f| f.embed.clone().unwrap())
                    .collect(),
                fields: fields
                    .iter()
                    .filter(|f| f.ty != FieldType::Embed)
                    .cloned()
                    .collect(),
                ..Default::default()
            });
        }
    }

    let node_idx: BTreeMap<String, usize> = schema
        .nodes
        .iter()
        .enumerate()
        .map(|(i, n)| (n.name.clone(), i))
        .collect();

    for f in &funcs {
        if f.recv_ty == "NodeFactory" {
            parse_factory_fn(f, schema, &node_idx)?;
        } else if f.recv_ty.is_empty() && f.name.starts_with("Is") {
            parse_is_fn(f, schema, &node_idx)?;
        } else if node_idx.contains_key(&f.recv_ty) {
            let ni = node_idx[&f.recv_ty];
            match f.name.as_str() {
                "ForEachChild" => parse_for_each_child(f, &mut schema.nodes[ni])?,
                "VisitEachChild" => parse_visit_each_child(f, &mut schema.nodes[ni])?,
                "Clone" => parse_clone(f, &mut schema.nodes[ni])?,
                "computeSubtreeFacts" => parse_compute(f, &mut schema.nodes[ni])?,
                "propagateSubtreeFacts" => parse_propagate(f, &mut schema.nodes[ni])?,
                "Name" | "Modifiers" | "setModifiers" | "IsAccessorDeclaration" => {}
                other => return Err(format!("unhandled method {other} on {}", f.recv_ty)),
            }
        }
        // Base methods (`Modifiers()` etc.) are emitted generically.
    }
    Ok(())
}

/// `data := f.xxxArena.New()` → struct name `Xxx`.
fn arena_target(l: &str) -> Result<String, String> {
    let rest = l
        .strip_prefix("data := f.")
        .and_then(|r| r.strip_suffix(".New()"))
        .ok_or_else(|| format!("bad arena alloc `{l}`"))?;
    let short = rest.strip_suffix("Arena").unwrap_or(rest);
    let mut c = short.chars();
    Ok(c.next().unwrap().to_ascii_uppercase().to_string() + c.as_str())
}

fn parse_factory_fn(
    f: &FuncSig,
    schema: &mut Schema,
    idx: &BTreeMap<String, usize>,
) -> Result<(), String> {
    if f.name.starts_with("New") {
        let body = &f.body;
        let mut target: Option<String> = None;
        let mut assigns: Vec<(String, String)> = Vec::new();
        let mut kind_expr: Option<String> = None;
        let mut post: Vec<CtorPost> = Vec::new();
        let mut counts_text = false;
        let mut counts_identifier = false;
        for line in body.lines() {
            let l = line.trim();
            if l.is_empty() {
                continue;
            }
            if let Some(rest) = l.strip_prefix("data := &") {
                target = Some(rest.trim_end_matches("{}").to_string());
            } else if l.starts_with("data := f.") {
                target = Some(arena_target(l)?);
            } else if let Some(rest) = l.strip_prefix("data.") {
                let Some(eq) = rest.find('=') else {
                    return Err(format!("{}: bad assign `{l}`", f.name));
                };
                assigns.push((rest[..eq].trim().to_string(), rest[eq + 1..].trim().to_string()));
            } else if l == "f.textCount++" {
                counts_text = true;
            } else if l == "f.identifierCount++" {
                counts_identifier = true;
            } else if let Some(rest) = l.strip_prefix("return f.newNode(") {
                let inner = rest.trim_end_matches(')');
                kind_expr = Some(inner.split(',').next().unwrap().trim().to_string());
            } else if let Some(rest) = l.strip_prefix("node := f.newNode(") {
                let inner = rest.trim_end_matches(')');
                kind_expr = Some(inner.split(',').next().unwrap().trim().to_string());
            } else if let Some(rest) = l.strip_prefix("node.Flags = ") {
                post.push(CtorPost::SetFlags {
                    arg: rest.trim().to_string(),
                });
            } else if let Some(expr) = l.strip_prefix("node.Flags |=") {
                let Some((arg, mask)) = expr.trim().split_once('&') else {
                    return Err(format!("{}: bad flags-or `{l}`", f.name));
                };
                if mask.trim() != "NodeFlagsOptionalChain" {
                    return Err(format!("{}: unexpected flags mask `{l}`", f.name));
                }
                post.push(CtorPost::OrOptionalChain {
                    arg: arg.trim().to_string(),
                });
            } else if l == "return node" {
                // end of `node := ...` form
            } else {
                return Err(format!("{}: unhandled stmt `{l}`", f.name));
            }
        }
        let Some(target) = target else {
            return Err(format!("{}: no data := for New fn", f.name));
        };
        let Some(&ni) = idx.get(&target) else {
            // e.g. NewNodeList/NewModifierList — handled by hand-written core.
            return Ok(());
        };
        let node = &mut schema.nodes[ni];
        let (kind, kind_arg) = match kind_expr.as_deref() {
            Some("kind") => (None, Some("kind".to_string())),
            Some(k) => (
                Some(k.strip_prefix("Kind").unwrap_or(k).to_string()),
                None,
            ),
            None => return Err(format!("{}: no newNode call", f.name)),
        };
        let mut args: Vec<CtorArg> = Vec::new();
        for (aname, aty) in &f.args {
            let mut field = None;
            let mut init_mask = None;
            for (fname, expr) in &assigns {
                if expr == aname {
                    field = Some(rust_name(fname));
                } else if let Some((lhs, mask)) = expr.split_once('&') {
                    if lhs.trim() == aname {
                        field = Some(rust_name(fname));
                        init_mask = Some(mask.trim().to_string());
                    }
                }
            }
            args.push(CtorArg {
                name: aname.clone(),
                ty: go_field_type(aty),
                field,
                init_mask,
                go_ty: aty.clone(),
            });
        }
        // Non-arg-derived assignments (literals): record for the emitter.
        for (fname, expr) in &assigns {
            if args.iter().any(|a| a.field.as_deref() == Some(&rust_name(fname))) {
                continue;
            }
            args.push(CtorArg {
                name: format!("__lit_{}", rust_name(fname)),
                ty: FieldType::Other,
                field: Some(rust_name(fname)),
                init_mask: Some(format!("lit:{expr}")),
                go_ty: String::new(),
            });
        }
        node.news.push(CtorDef {
            name: f.name.clone(),
            kind,
            kind_arg,
            args,
            post,
            counts_text,
            counts_identifier,
        });
        return Ok(());
    }
    if f.name.starts_with("Update") {
        let (recv_name, recv_ty) = f
            .args
            .first()
            .ok_or_else(|| format!("{}: no node arg", f.name))?;
        if recv_name != "node" || !recv_ty.starts_with('*') {
            return Err(format!("{}: bad update signature", f.name));
        }
        let target = recv_ty.trim_start_matches('*').to_string();
        let Some(&ni) = idx.get(&target) else {
            return Ok(()); // e.g. UpdateNodeList — not generated
        };
        let node = &mut schema.nodes[ni];
        let body = f.body.trim().to_string();
        let body = body
            .strip_prefix("if ")
            .ok_or_else(|| format!("{}: no if", f.name))?;
        let brace = body.find('{').ok_or_else(|| format!("{}: no if body", f.name))?;
        let cond = body[..brace].trim().to_string();
        let mut compares = Vec::new();
        for term in split_top_level_op(&cond, "||") {
            let term = term.trim();
            if let Some(inner) = term
                .strip_prefix("!")
                .and_then(|t| t.strip_prefix("core.Same("))
                .and_then(|t| t.strip_suffix(')'))
            {
                let mut parts = split_top_level(inner, ',');
                let lhs = parts.remove(0).trim().to_string();
                let rhs = parts.remove(0).trim().to_string();
                let field = rhs.strip_prefix("node.").unwrap_or(&rhs);
                compares.push(UpdateCompare {
                    lhs,
                    field: rust_name(field),
                    op: "same".into(),
                });
            } else if let Some((lhs, rhs)) = term.split_once("!=") {
                let lhs = lhs.trim().to_string();
                let rhs = rhs.trim().to_string();
                let field = rhs.strip_prefix("node.").unwrap_or(&rhs);
                compares.push(UpdateCompare {
                    lhs,
                    field: rust_name(field),
                    op: "neq".into(),
                });
            } else {
                return Err(format!("{}: unhandled compare `{term}`", f.name));
            }
        }
        // `return updateNode(f.NewY(args), node.AsNode(), f.hooks)`
        let Some((_, call_args)) = extract_call(&body, "updateNode") else {
            return Err(format!("{}: no updateNode", f.name));
        };
        let new_call = call_args.first().cloned().unwrap_or_default();
        let new_call = new_call
            .strip_prefix("f.AsNodeFactory().")
            .or_else(|| new_call.strip_prefix("f."))
            .unwrap_or(&new_call)
            .to_string();
        let open = new_call
            .find('(')
            .ok_or_else(|| format!("{}: bad rebuild call `{new_call}`", f.name))?;
        let new_fn = new_call[..open].to_string();
        let new_args: Vec<String> = split_top_level(&new_call[open + 1..new_call.len() - 1], ',')
            .into_iter()
            .map(|a| a.trim().to_string())
            .filter(|a| !a.is_empty())
            .collect();
        let args: Vec<UpdateArg> = f
            .args
            .iter()
            .skip(1)
            .map(|(n, t)| UpdateArg {
                name: n.clone(),
                ty: go_field_type(t),
            })
            .collect();
        node.update = Some(UpdateDef {
            name: f.name.clone(),
            args,
            compares,
            new_fn,
            new_args,
        });
        return Ok(());
    }
    // NewNodeList/NewModifierList/etc. — hand-written.
    Ok(())
}

fn parse_is_fn(f: &FuncSig, schema: &mut Schema, idx: &BTreeMap<String, usize>) -> Result<(), String> {
    let body = f.body.trim().to_string();
    let arg_ty = f.args.first().map(|a| a.1.as_str()).unwrap_or("");

    // Collect `node.Kind == KindX || ...` / `switch`-case kind lists, ranges,
    // and `return IsXKind(<arg>.Kind)` delegates — for both `*Node` and `Kind`
    // receivers. `expr_src` is "node.Kind" or "kind" depending on the arg.
    let mut kinds: Vec<String> = Vec::new();
    let mut range: Option<[String; 2]> = None;
    let mut delegate: Option<String> = None;
    let ret = body.strip_prefix("return ").unwrap_or(&body);
    if body.starts_with("switch") {
        for line in body.lines() {
            let l = line.trim();
            if let Some(rest) = l.strip_prefix("case ") {
                for k in rest.trim_end_matches(':').split(',') {
                    kinds.push(
                        k.trim()
                            .strip_prefix("Kind")
                            .unwrap_or(k.trim())
                            .to_string(),
                    );
                }
            }
        }
    } else if let Some(rest) = ret.strip_prefix("Is") {
        if let Some(inner) = rest.strip_suffix("(node.Kind)").or_else(|| rest.strip_suffix("(kind)")) {
            delegate = Some(format!("Is{inner}"));
        }
    }
    if delegate.is_none() && !body.starts_with("switch") {
        // `a >= KindX && a <= KindY` or `a == KindX || a == KindY ...`
        let lhs = if arg_ty == "Kind" { "kind" } else { "node.Kind" };
        if let Some(rest) = ret.strip_prefix(&format!("{lhs} >= ")) {
            if let Some((lo, rest2)) = rest.split_once(&format!("&& {lhs} <= ")) {
                range = Some([
                    lo.trim().strip_prefix("Kind").unwrap_or(lo.trim()).to_string(),
                    rest2.trim().strip_prefix("Kind").unwrap_or(rest2.trim()).to_string(),
                ]);
            }
        } else {
            for term in split_top_level_op(ret, "||") {
                let term = term.trim();
                if let Some(eq) = term.strip_prefix(&format!("{lhs} == ")) {
                    kinds.push(
                        eq.trim()
                            .strip_prefix("Kind")
                            .unwrap_or(eq.trim())
                            .to_string(),
                    );
                } else {
                    // unparseable — drop to hand-written utilities
                    kinds.clear();
                    eprintln!(
                        "gen-ast bootstrap: skipping unparseable Is body `{}`: {}",
                        f.name, body
                    );
                    break;
                }
            }
        }
    }

    if arg_ty == "Kind" {
        schema.kind_preds.push(KindPred {
            name: f.name.clone(),
            range,
            kinds,
            delegate,
        });
        return Ok(());
    }

    // Node-level `IsX` — attach to the node struct of the same name.
    let target = f.name.strip_prefix("Is").unwrap_or(&f.name).to_string();
    if let Some(&i) = idx.get(&target) {
        let node = &mut schema.nodes[i];
        node.is_fn = Some(f.name.clone());
        if node.kinds.is_empty() && !kinds.is_empty() {
            node.kinds = kinds;
        }
    } else {
        schema.node_preds.push(KindPred {
            name: f.name.clone(),
            range,
            kinds,
            delegate,
        });
    }
    Ok(())
}

fn parse_for_each_child(f: &FuncSig, node: &mut NodeDef) -> Result<(), String> {
    let body = f.body.trim().to_string();
    if body.starts_with("return forEachChild_") || body.contains("forEachChild_") {
        node.custom.push("for_each_child".into());
        return Ok(());
    }
    let Some(expr) = body.strip_prefix("return ") else {
        return Err(format!("{}: bad forEachChild body `{body}`", f.name));
    };
    if expr == "false" {
        return Ok(());
    }
    for term in split_top_level_op(expr, "||") {
        let term = term.trim().trim_end_matches(';').trim();
        // Generated style puts each op on its own line possibly wrapped in
        // parens: `(a && visit(v, node.x))` — strip outer parens.
        let term = term
            .strip_prefix('(')
            .and_then(|t| t.strip_suffix(')'))
            .unwrap_or(term)
            .trim();
        // `visit(v, node.F)` etc; parenthesized `cond &&` prefixes for
        // conditional children (none in generated code today).
        let Some(open) = term.find('(') else {
            return Err(format!("ForEachChild {}: bad term `{term}`", node.name));
        };
        let op = term[..open].trim().to_string();
        let arg = term[open + 1..].trim_end_matches(')');
        let field = arg
            .split(',')
            .nth(1)
            .ok_or_else(|| format!("ForEachChild {}: bad arg `{term}`", node.name))?
            .trim()
            .strip_prefix("node.")
            .unwrap_or("")
            .to_string();
        let op = match op.as_str() {
            "visit" => "visit",
            "visitNodes" => "visitNodes",
            "visitNodeList" => "visitNodeList",
            "visitModifiers" => "visitModifiers",
            o => return Err(format!("ForEachChild {}: unknown op `{o}`", node.name)),
        };
        node.for_each_child.push(VisitOp {
            op: op.to_string(),
            field: rust_name(&field),
        });
    }
    Ok(())
}

fn parse_visit_each_child(f: &FuncSig, node: &mut NodeDef) -> Result<(), String> {
    let body = f.body.trim().to_string();
    if body.contains("visitEachChild_") {
        node.custom.push("visit_each_child".into());
        return Ok(());
    }
    // `x := core.SameMap(node.F, ...)` locals → `sameMap` args by var name.
    let mut same_map_vars: BTreeMap<String, String> = BTreeMap::new();
    for line in body.lines() {
        let l = line.trim();
        if l.contains("core.SameMap(") {
            let var = l.split(":=").next().unwrap().trim().to_string();
            let open = l.find("core.SameMap(").unwrap();
            let inner = &l[open + "core.SameMap(".len()..];
            let field = inner.split(',').next().unwrap().trim().to_string();
            let field = field.strip_prefix("node.").unwrap_or(&field).to_string();
            same_map_vars.insert(var, rust_name(&field));
        }
    }
    let Some(update_pos) = body.find("v.Factory.Update") else {
        return Err(format!("{}: bad visitEachChild `{body}`", f.name));
    };
    let call = &body[update_pos + "v.Factory.".len()..];
    let open = call
        .find('(')
        .ok_or_else(|| format!("{}: bad call", f.name))?;
    let close = matching_paren(call, open).ok_or_else(|| format!("{}: bad call", f.name))?;
    let args = &call[open + 1..close];
    let mut first = true;
    for arg in split_top_level(args, ',') {
        let arg = arg.trim().to_string();
        if first {
            first = false;
            if arg != "node" {
                return Err(format!("{}: visitEachChild first arg `{arg}`", f.name));
            }
            continue;
        }
        if let Some(field) = same_map_vars.get(&arg) {
            node.visit_each_child.push(VisitArg {
                op: "sameMap".into(),
                field: Some(field.clone()),
            });
            continue;
        }
        node.visit_each_child.push(classify_visit_arg(&arg)?);
    }
    Ok(())
}

fn classify_visit_arg(arg: &str) -> Result<VisitArg, String> {
    for (prefix, op) in [
        ("v.visitEmbeddedStatement(", "visitEmbeddedStatement"),
        ("v.visitIterationBody(", "visitIterationBody"),
        ("v.visitParameters(", "visitParameters"),
        ("v.visitFunctionBody(", "visitFunctionBody"),
        ("v.visitTopLevelStatements(", "visitTopLevelStatements"),
        ("v.visitModifiers(", "visitModifiers"),
        ("v.visitToken(", "visitToken"),
        ("v.visitNodes(", "visitNodes"),
        ("v.visitNode(", "visitNode"),
    ] {
        if let Some(rest) = arg.strip_prefix(prefix) {
            let inner = rest.trim_end_matches(')');
            let field = inner.strip_prefix("node.").unwrap_or(inner);
            return Ok(VisitArg {
                op: op.to_string(),
                field: Some(rust_name(field)),
            });
        }
    }
    match arg {
        "node.Kind" => Ok(VisitArg { op: "kind".into(), field: None }),
        "node.Flags" => Ok(VisitArg { op: "flags".into(), field: None }),
        a if a.starts_with("node.") => Ok(VisitArg {
            op: "field".into(),
            field: Some(rust_name(&a["node.".len()..])),
        }),
        _ => Err(format!("unhandled visitEachChild arg `{arg}`")),
    }
}

fn parse_clone(f: &FuncSig, node: &mut NodeDef) -> Result<(), String> {
    let body = f.body.trim().to_string();
    if body.starts_with("return cloneNode(") {
        node.clone = vec![parse_clone_call(&body)?];
        return Ok(());
    }
    if body.starts_with("switch node.Kind") {
        node.clone = parse_clone_switch(&body)?;
        return Ok(());
    }
    if body.starts_with("panic") || body == "return nil" {
        return Ok(());
    }
    Err(format!("{}: unhandled clone body `{body}`", f.name))
}

fn parse_clone_call(body: &str) -> Result<CloneArm, String> {
    let open = body.find("cloneNode(").ok_or("no cloneNode")?;
    let inner = &body[open + "cloneNode(".len()..];
    // inner: `f.AsNodeFactory().NewX(args), node.AsNode(), f.AsNodeFactory().hooks)`
    let p = inner.find("New").ok_or_else(|| format!("bad clone `{body}`"))?;
    let call = &inner[p..];
    let open = call.find('(').ok_or("bad clone call")?;
    let end = matching_paren(call, open).ok_or("bad clone call")?;
    let new_fn = call[..open].to_string();
    let args: Vec<String> = split_top_level(&call[open + 1..end], ',')
        .into_iter()
        .map(|a| clone_arg(a.trim()))
        .collect();
    Ok(CloneArm {
        kind: None,
        new_fn,
        args,
    })
}

fn clone_arg(a: &str) -> String {
    match a {
        "node.Modifiers()" => "modifiers()".into(),
        "node.Kind" => "kind".into(),
        "node.Flags" => "flags".into(),
        _ => {
            if let Some(f) = a.strip_prefix("node.") {
                format!("field:{}", rust_name(f))
            } else {
                format!("expr:{a}")
            }
        }
    }
}

fn parse_clone_switch(body: &str) -> Result<Vec<CloneArm>, String> {
    let mut arms = Vec::new();
    let mut cur_kind: Option<String> = None;
    for line in body.lines() {
        let l = line.trim();
        if let Some(rest) = l.strip_prefix("case ") {
            cur_kind = Some(
                rest.trim_end_matches(':')
                    .trim()
                    .strip_prefix("Kind")
                    .unwrap_or(rest.trim_end_matches(':').trim())
                    .to_string(),
            );
        } else if l.contains("cloneNode(") {
            let mut arm = parse_clone_call(l)?;
            arm.kind = cur_kind.take();
            arms.push(arm);
        }
    }
    Ok(arms)
}

fn parse_compute(f: &FuncSig, node: &mut NodeDef) -> Result<(), String> {
    let body = f.body.trim().to_string();
    let Some(expr) = body.strip_prefix("return ") else {
        node.facts_mode = "custom".into();
        return Ok(());
    };
    let mut ops = Vec::new();
    let mut simple = true;
    for term in split_top_level_op(expr, "|") {
        let term = term.trim();
        if let Some(inner) = term
            .strip_prefix("propagateSubtreeFacts(")
            .and_then(|t| t.strip_suffix(')'))
        {
            ops.push(FactOp {
                op: "propagate".into(),
                field: Some(rust_name(inner.strip_prefix("node.").unwrap_or(inner))),
                value: None,
            });
        } else if let Some(inner) = term
            .strip_prefix("propagateNodeListSubtreeFacts(")
            .and_then(|t| t.strip_suffix(')'))
        {
            let field = split_top_level(inner, ',')
                .into_iter()
                .next()
                .unwrap_or_default()
                .trim()
                .strip_prefix("node.")
                .unwrap_or("")
                .to_string();
            ops.push(FactOp {
                op: "propagateList".into(),
                field: Some(rust_name(&field)),
                value: None,
            });
        } else if let Some(inner) = term
            .strip_prefix("propagateModifierListSubtreeFacts(")
            .and_then(|t| t.strip_suffix(')'))
        {
            ops.push(FactOp {
                op: "propagateModifierList".into(),
                field: Some(rust_name(inner.strip_prefix("node.").unwrap_or(inner))),
                value: None,
            });
        } else if term.starts_with("Subtree") {
            ops.push(FactOp {
                op: "const".into(),
                field: None,
                value: Some(term.to_string()),
            });
        } else {
            simple = false;
        }
    }
    if !simple {
        node.facts_mode = "custom".into();
        return Ok(());
    }
    node.facts = ops;
    node.facts_mode = "generated".into();
    Ok(())
}

/// `return node.SubtreeFacts() & ^SubtreeExclusionsX [| propagateSubtreeFacts(node.f)]`
/// — called on bodies parsed from ast.go (all overrides live there).
fn parse_propagate_body(body: &str, node: &mut NodeDef) -> Result<(), String> {
    let body = body.trim();
    let Some(rest) = body.strip_prefix("return node.SubtreeFacts()") else {
        node.propagate_mode = "custom".into();
        return Ok(());
    };
    let rest = rest.trim();
    if let Some(exc) = rest.strip_prefix("& ^") {
        // `SubtreeExclusionsX | propagateSubtreeFacts(node.f) ...`
        let mut terms = split_top_level_op(exc, "|").into_iter();
        let first = terms.next().unwrap_or_default().trim().to_string();
        node.propagate_mode = "exclusions".into();
        node.propagate_exclusions = Some(first);
        for term in terms {
            let term = term.trim();
            if let Some(inner) = term
                .strip_prefix("propagateSubtreeFacts(")
                .and_then(|t| t.strip_suffix(')'))
            {
                node.propagate_fields
                    .push(rust_name(inner.strip_prefix("node.").unwrap_or(inner)));
            } else {
                node.propagate_mode = "custom".into();
                return Ok(());
            }
        }
        return Ok(());
    }
    if rest.is_empty() {
        node.propagate_mode = "default".into();
        return Ok(());
    }
    node.propagate_mode = "custom".into();
    Ok(())
}

fn parse_propagate(f: &FuncSig, node: &mut NodeDef) -> Result<(), String> {
    parse_propagate_body(&f.body, node)
}

// ── ast.go (hand-written) — extra payloads + subtree-fact overrides ────────

fn parse_hand(src: &str, schema: &mut Schema) -> Result<(), String> {
    let lines: Vec<&str> = src.lines().collect();
    let node_idx: BTreeMap<String, usize> = schema
        .nodes
        .iter()
        .enumerate()
        .map(|(i, n)| (n.name.clone(), i))
        .collect();
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        if t.starts_with("func ") {
            let (sig, end) = read_func(&lines, i)?;
            if let Some(&ni) = node_idx.get(&sig.recv_ty) {
                match sig.name.as_str() {
                    "propagateSubtreeFacts" => {
                        parse_propagate_body(&sig.body, &mut schema.nodes[ni])?;
                    }
                    "computeSubtreeFacts" => {
                        // Hand-written computes are non-trivial (switches,
                        // conditionals) — mark for the hand port in
                        // subtreefacts.rs.
                        schema.nodes[ni].facts_mode = "custom".into();
                        schema.nodes[ni].facts.clear();
                    }
                    "ForEachChild" | "VisitEachChild" | "Clone" => {
                        // e.g. SourceFile — hand-written traversal.
                    }
                    _ => {}
                }
            }
            i = end + 1;
            continue;
        }
        if t.starts_with("type ")
            && t.ends_with("struct {")
            && ["SourceFile", "FlowSwitchClauseData", "FlowReduceLabelData"]
                .iter()
                .any(|n| t[5..t.len() - 8].trim() == *n)
        {
            let name = t[5..t.len() - 8].trim().to_string();
            let (fields, end) = read_struct_fields_lenient(&lines, i)?;
            i = end + 1;
            match name.as_str() {
                "SourceFile" => push_source_file(schema),
                _ => schema.nodes.push(NodeDef {
                    name,
                    bases: fields
                        .iter()
                        .filter(|f| f.ty == FieldType::Embed)
                        .map(|f| f.embed.clone().unwrap())
                        .collect(),
                    fields: fields
                        .into_iter()
                        .filter(|f| f.ty != FieldType::Embed)
                        .collect(),
                    facts_mode: "none".into(),
                    propagate_mode: "default".into(),
                    extra: true,
                    kinds: vec![],
                    ..Default::default()
                }),
            }
            continue;
        }
        i += 1;
    }
    Ok(())
}

/// Like `read_struct_fields` but drops fields whose types we don't model —
/// used for hand-written structs with rich dependency types.
fn read_struct_fields_lenient(
    lines: &[&str],
    header_idx: usize,
) -> Result<(Vec<Field>, usize), String> {
    let mut fields = Vec::new();
    let mut i = header_idx + 1;
    while i < lines.len() && lines[i].trim() != "}" {
        let fl = lines[i].trim();
        if !fl.is_empty() && !fl.starts_with("//") {
            if let Ok(f) = parse_field(fl, i + 1) {
                fields.push(f);
            }
        }
        i += 1;
    }
    Ok((fields, i))
}

/// Curated minimal `SourceFile` payload — the Go struct carries dozens of
/// binder/parser/checker fields; the port keeps the core set and grows it in
/// `kinds.toml` as needed. `Other`-typed fields carry `rust_ty`.
fn push_source_file(schema: &mut Schema) {
    let field = |name: &str, ty: FieldType, rust_ty: Option<&str>| Field {
        go_name: name.to_string(),
        name: rust_name(name),
        ty,
        embed: None,
        optional: true,
        exported: true,
        rust_ty: rust_ty.map(|s| s.to_string()),
    };
    schema.nodes.push(NodeDef {
        name: "SourceFile".into(),
        kinds: vec!["SourceFile".into()],
        // Go: NodeBase (header — outside NodeData) + DeclarationBase +
        // LocalsContainerBase + CompositeBase.
        bases: vec![
            "DeclarationBase".into(),
            "LocalsContainerBase".into(),
            "CompositeBase".into(),
        ],
        fields: vec![
            field("fileName", FieldType::Other, Some("String")),
            field("text", FieldType::Str, None),
            field("statements", FieldType::NodeList, None),
            field("endOfFileToken", FieldType::Node, None),
            field("languageVariant", FieldType::Other, Some("tsc_core::LanguageVariant")),
            field("scriptKind", FieldType::Other, Some("tsc_core::ScriptKind")),
            field("isDeclarationFile", FieldType::Bool, None),
            field(
                "usesUriStyleNodeCoreModules",
                FieldType::Other,
                Some("tsc_core::Tristate"),
            ),
            field("identifierCount", FieldType::Int, None),
            field("imports", FieldType::NodeSlice, None),
            field("moduleAugmentations", FieldType::NodeSlice, None),
            field("ambientModuleNames", FieldType::StringSlice, None),
            field(
                "commentDirectives",
                FieldType::Other,
                Some("Box<[crate::ast::CommentDirective]>"),
            ),
            field(
                "pragmas",
                FieldType::Other,
                Some("Box<[crate::ast::Pragma]>"),
            ),
            field(
                "referencedFiles",
                FieldType::Other,
                Some("Box<[crate::ast::FileReference]>"),
            ),
            field(
                "typeReferenceDirectives",
                FieldType::Other,
                Some("Box<[crate::ast::FileReference]>"),
            ),
            field(
                "libReferenceDirectives",
                FieldType::Other,
                Some("Box<[crate::ast::FileReference]>"),
            ),
            field(
                "checkJsDirective",
                FieldType::Other,
                Some("Option<crate::ast::CheckJsDirective>"),
            ),
            field("nodeCount", FieldType::Int, None),
            field("textCount", FieldType::Int, None),
            field("commonJSModuleIndicator", FieldType::Node, None),
            field("externalModuleIndicator", FieldType::Node, None),
            field("symbolCount", FieldType::Int, None),
            field(
                "patternAmbientModules",
                FieldType::Other,
                Some("Box<[crate::ast::PatternAmbientModule]>"),
            ),
            field("globalExports", FieldType::SymbolTable, None),
            field("reparsedClones", FieldType::NodeSlice, None),
        ],
        // `computeSubtreeFacts` = propagateNodeListSubtreeFacts(Statements).
        facts: vec![FactOp {
            op: "propagateList".into(),
            field: Some("statements".into()),
            value: None,
        }],
        facts_mode: "generated".into(),
        propagate_mode: "default".into(),
        custom: vec![
            "ctor".into(),
            "for_each_child".into(),
            "visit_each_child".into(),
            "clone".into(),
            "update".into(),
        ],
        extra: true,
        ..Default::default()
    });
}

// ── postprocess ────────────────────────────────────────────────────────────

fn postprocess(schema: &mut Schema) -> Result<(), String> {
    let alias_kinds: BTreeMap<String, Vec<String>> = schema
        .kind_aliases
        .iter()
        .map(|a| (a.name.clone(), a.kinds.clone()))
        .collect();

    // snapshot for immutable lookups during the mutable pass
    let nodes_snapshot: Vec<NodeDef> = schema.nodes.clone();
    let ts_bases: Vec<bool> = nodes_snapshot
        .iter()
        .map(|n| schema.has_base(&n.bases, "TypeSyntaxBase"))
        .collect();
    let clike_bases: Vec<bool> = nodes_snapshot
        .iter()
        .map(|n| schema.has_base(&n.bases, "ClassLikeBase"))
        .collect();
    let accessor_bases: Vec<bool> = nodes_snapshot
        .iter()
        .map(|n| schema.has_base(&n.bases, "AccessorDeclarationBase"))
        .collect();
    for (i, node) in schema.nodes.iter_mut().enumerate() {
        let snap = &nodes_snapshot[i];
        if node.kinds.is_empty() {
            if !node.news.is_empty() && node.news.iter().all(|n| n.kind.is_some()) {
                let mut ks: Vec<String> = node
                    .news
                    .iter()
                    .filter_map(|n| n.kind.clone())
                    .collect();
                ks.sort();
                ks.dedup();
                node.kinds = ks;
            } else if let Some(ctor) = node.news.iter().find(|n| n.kind_arg.is_some()) {
                // kind-parameterized ctor — resolve via the `*SyntaxKind`
                // alias on the kind arg's Go type.
                let go_ty = ctor
                    .args
                    .iter()
                    .find(|a| Some(&a.name) == ctor.kind_arg.as_ref())
                    .map(|a| a.go_ty.clone())
                    .unwrap_or_default();
                if let Some(ks) = alias_kinds.get(&go_ty) {
                    node.kinds = ks.clone();
                }
            }
            if node.kinds.is_empty() {
                // The ctor's `kind` param is the bare `Kind` type, so no
                // alias documents the set — use the `IsX` predicates' known
                // members (verified against utilities.go / ast_generated.go).
                node.kinds = match node.name.as_str() {
                    "ForInOrOfStatement" => {
                        vec!["ForInStatement".into(), "ForOfStatement".into()]
                    }
                    "CaseOrDefaultClause" => {
                        vec!["CaseClause".into(), "DefaultClause".into()]
                    }
                    "BindingPattern" => {
                        vec!["ObjectBindingPattern".into(), "ArrayBindingPattern".into()]
                    }
                    "JSDocParameterOrPropertyTag" => {
                        vec!["JSDocParameterTag".into(), "JSDocPropertyTag".into()]
                    }
                    _ => vec![],
                };
            }
        }
        if node.facts_mode.is_empty() {
            node.facts_mode = if !node.facts.is_empty() {
                "generated"
            } else if ts_bases[i] {
                "typescript"
            } else if clike_bases[i] || accessor_bases[i] {
                // ClassLikeBase/AccessorDeclarationBase have hand-written
                // computeSubtreeFacts in ast.go.
                "custom"
            } else {
                "none"
            }
            .into();
        }
        if node.propagate_mode.is_empty() {
            if accessor_bases[i] {
                // AccessorDeclarationBase::propagateSubtreeFacts is hand-written.
                node.propagate_mode = "exclusions".into();
                node.propagate_exclusions = Some("SubtreeExclusionsAccessor".into());
                node.propagate_fields = vec!["name".into()];
            } else {
                node.propagate_mode = if ts_bases[i] { "typescript" } else { "default" }.into();
            }
        }
        let _ = snap;
    }

    // `IsX(node)` preds recorded before their target node existed
    // (SourceFile is parsed from ast.go) — re-attach.
    let node_names: BTreeSet<String> = schema.nodes.iter().map(|n| n.name.clone()).collect();
    let mut keep = Vec::new();
    for p in std::mem::take(&mut schema.node_preds) {
        let target = p.name.strip_prefix("Is").unwrap_or(&p.name);
        if node_names.contains(target) {
            let ni = schema.nodes.iter().position(|n| n.name == target).unwrap();
            let node = &mut schema.nodes[ni];
            node.is_fn = Some(p.name.clone());
            if node.kinds.is_empty() && !p.kinds.is_empty() {
                node.kinds = p.kinds.clone();
            }
        } else {
            keep.push(p);
        }
    }
    schema.node_preds = keep;

    // Every node needs kinds for the as_* accessors — extras excepted
    // (dispatched by data variant, not kind).
    let missing: Vec<&str> = schema
        .nodes
        .iter()
        .filter(|n| n.kinds.is_empty() && !n.extra)
        .map(|n| n.name.as_str())
        .collect();
    if !missing.is_empty() {
        eprintln!(
            "gen-ast bootstrap: {} nodes without kinds (defaulting to empty): {}",
            missing.len(),
            missing.join(", ")
        );
    }
    Ok(())
}

fn snap_bases_have(schema: &Schema, bases: &[String], target: &str) -> bool {
    schema.has_base(bases, target)
}

/// Helper for tests — verifies name lists dedup cleanly.
#[allow(dead_code)]
pub fn dedup_check(v: &mut Vec<String>) {
    let mut seen = BTreeSet::new();
    v.retain(|x| seen.insert(x.clone()));
}
