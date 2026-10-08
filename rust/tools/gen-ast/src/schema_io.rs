// `kinds.toml` read/write — serializes `Schema` to TOML text (deterministic
// key order, hand-formatted) and parses it back via `toml.rs`.
//
// Section layout:
//   [kinds]                names = [...]
//   [[kind_consts]]        name / value
//   [[kind_aliases]]       name / kinds
//   [[kind_preds]]         name / range | kinds | delegate
//   [[node_preds]]         same shape
//   [[bases]]              name / fields
//   [[nodes]]              the big one — see `write_node`

use crate::model::*;
use crate::toml::{self, Document, Value};

// ── FieldType tags ─────────────────────────────────────────────────────────

fn ty_tag(ty: FieldType) -> &'static str {
    match ty {
        FieldType::Embed => "embed",
        FieldType::Node => "node",
        FieldType::NodeList => "node_list",
        FieldType::ModifierList => "modifier_list",
        FieldType::NodeSlice => "node_slice",
        FieldType::StringSlice => "string_slice",
        FieldType::Str => "str",
        FieldType::Bool => "bool",
        FieldType::Int => "int",
        FieldType::Kind => "kind",
        FieldType::TokenFlags => "token_flags",
        FieldType::NodeFlags => "node_flags",
        FieldType::Symbol => "symbol",
        FieldType::SymbolTable => "symbol_table",
        FieldType::FlowNode => "flow_node",
        FieldType::FlowList => "flow_list",
        FieldType::AtomicU32 => "atomic_u32",
        FieldType::Any => "any",
        FieldType::Other => "other",
    }
}

fn ty_from_tag(tag: &str) -> Result<FieldType, String> {
    Ok(match tag {
        "embed" => FieldType::Embed,
        "node" => FieldType::Node,
        "node_list" => FieldType::NodeList,
        "modifier_list" => FieldType::ModifierList,
        "node_slice" => FieldType::NodeSlice,
        "string_slice" => FieldType::StringSlice,
        "str" => FieldType::Str,
        "bool" => FieldType::Bool,
        "int" => FieldType::Int,
        "kind" => FieldType::Kind,
        "token_flags" => FieldType::TokenFlags,
        "node_flags" => FieldType::NodeFlags,
        "symbol" => FieldType::Symbol,
        "symbol_table" => FieldType::SymbolTable,
        "flow_node" => FieldType::FlowNode,
        "flow_list" => FieldType::FlowList,
        "atomic_u32" => FieldType::AtomicU32,
        "any" => FieldType::Any,
        "other" => FieldType::Other,
        _ => return Err(format!("unknown field type tag `{tag}`")),
    })
}

// ── write ──────────────────────────────────────────────────────────────────

fn str_array(items: &[String]) -> String {
    let inner: Vec<String> = items.iter().map(|s| toml::escape(s)).collect();
    format!("[{}]", inner.join(", "))
}

fn field_inline(f: &Field) -> String {
    let mut out = format!(
        "{{ name = {}, ty = {}",
        toml::escape(&f.name),
        toml::escape(ty_tag(f.ty))
    );
    if let Some(e) = &f.embed {
        out.push_str(&format!(", embed = {}", toml::escape(e)));
    }
    if f.go_name != f.name {
        out.push_str(&format!(", go_name = {}", toml::escape(&f.go_name)));
    }
    if f.optional {
        out.push_str(", optional = true");
    }
    if !f.exported {
        out.push_str(", exported = false");
    }
    if let Some(t) = &f.rust_ty {
        out.push_str(&format!(", rust_ty = {}", toml::escape(t)));
    }
    out.push_str(" }");
    out
}

fn write_fields(out: &mut String, key: &str, fields: &[Field]) {
    out.push_str(&format!("{key} = [\n"));
    for f in fields {
        out.push_str(&format!("    {},\n", field_inline(f)));
    }
    out.push_str("]\n");
}

fn ctor_arg_inline(a: &CtorArg) -> String {
    let mut out = format!(
        "{{ name = {}, ty = {}",
        toml::escape(&a.name),
        toml::escape(ty_tag(a.ty))
    );
    if let Some(f) = &a.field {
        out.push_str(&format!(", field = {}", toml::escape(f)));
    }
    if let Some(m) = &a.init_mask {
        out.push_str(&format!(", mask = {}", toml::escape(m)));
    }
    if !a.go_ty.is_empty() {
        out.push_str(&format!(", go_ty = {}", toml::escape(&a.go_ty)));
    }
    out.push_str(" }");
    out
}

/// `news = [ {…}, {…} ]` — one array per node.
fn write_news(out: &mut String, news: &[CtorDef]) {
    if news.is_empty() {
        return;
    }
    out.push_str("news = [\n");
    for c in news {
        let mut line = format!("    {{ name = {}", toml::escape(&c.name));
        if let Some(k) = &c.kind {
            line.push_str(&format!(", kind = {}", toml::escape(k)));
        }
        if let Some(k) = &c.kind_arg {
            line.push_str(&format!(", kind_arg = {}", toml::escape(k)));
        }
        line.push_str(", args = [");
        for (i, a) in c.args.iter().enumerate() {
            if i > 0 {
                line.push_str(", ");
            }
            line.push_str(&ctor_arg_inline(a));
        }
        line.push(']');
        if !c.post.is_empty() {
            let posts: Vec<String> = c
                .post
                .iter()
                .map(|p| match p {
                    CtorPost::SetFlags { arg } => format!("set_flags:{arg}"),
                    CtorPost::OrOptionalChain { arg } => format!("or_optional_chain:{arg}"),
                })
                .map(|s| toml::escape(&s))
                .collect();
            line.push_str(&format!(", post = [{}]", posts.join(", ")));
        }
        if c.counts_text {
            line.push_str(", counts_text = true");
        }
        if c.counts_identifier {
            line.push_str(", counts_identifier = true");
        }
        line.push_str(" },\n");
        out.push_str(&line);
    }
    out.push_str("]\n");
}

fn write_update(out: &mut String, u: &UpdateDef) {
    let mut line = format!("update = {{ name = {}", toml::escape(&u.name));
    line.push_str(", args = [");
    for (i, a) in u.args.iter().enumerate() {
        if i > 0 {
            line.push_str(", ");
        }
        line.push_str(&format!(
            "{{ name = {}, ty = {} }}",
            toml::escape(&a.name),
            toml::escape(ty_tag(a.ty))
        ));
    }
    line.push_str("], compares = [");
    for (i, c) in u.compares.iter().enumerate() {
        if i > 0 {
            line.push_str(", ");
        }
        line.push_str(&format!(
            "{{ lhs = {}, field = {}, op = {} }}",
            toml::escape(&c.lhs),
            toml::escape(&c.field),
            toml::escape(&c.op)
        ));
    }
    line.push_str(&format!("], new_fn = {}", toml::escape(&u.new_fn)));
    line.push_str(&format!(", new_args = {}", str_array(&u.new_args)));
    line.push_str(" }\n");
    out.push_str(&line);
}

fn write_visit_ops(out: &mut String, key: &str, ops: &[VisitOp]) {
    if ops.is_empty() {
        return;
    }
    out.push_str(&format!("{key} = [\n"));
    for op in ops {
        out.push_str(&format!(
            "    {{ op = {}, field = {} }},\n",
            toml::escape(&op.op),
            toml::escape(&op.field)
        ));
    }
    out.push_str("]\n");
}

fn write_visit_args(out: &mut String, key: &str, args: &[VisitArg]) {
    if args.is_empty() {
        return;
    }
    out.push_str(&format!("{key} = [\n"));
    for a in args {
        let mut line = format!("    {{ op = {}", toml::escape(&a.op));
        if let Some(f) = &a.field {
            line.push_str(&format!(", field = {}", toml::escape(f)));
        }
        line.push_str(" },\n");
        out.push_str(&line);
    }
    out.push_str("]\n");
}

fn write_clone(out: &mut String, arms: &[CloneArm]) {
    if arms.is_empty() {
        return;
    }
    out.push_str("clone = [\n");
    for a in arms {
        let mut line = format!("    {{ new_fn = {}", toml::escape(&a.new_fn));
        if let Some(k) = &a.kind {
            line.push_str(&format!(", kind = {}", toml::escape(k)));
        }
        line.push_str(&format!(", args = {} }},\n", str_array(&a.args)));
        out.push_str(&line);
    }
    out.push_str("]\n");
}

fn write_facts(out: &mut String, facts: &[FactOp]) {
    if facts.is_empty() {
        return;
    }
    out.push_str("facts = [\n");
    for f in facts {
        let mut line = format!("    {{ op = {}", toml::escape(&f.op));
        if let Some(x) = &f.field {
            line.push_str(&format!(", field = {}", toml::escape(x)));
        }
        if let Some(v) = &f.value {
            line.push_str(&format!(", value = {}", toml::escape(v)));
        }
        line.push_str(" },\n");
        out.push_str(&line);
    }
    out.push_str("]\n");
}

pub fn write_schema(schema: &Schema) -> String {
    let mut out = String::new();
    out.push_str(
        "# kinds.toml — authored AST schema for the Rust tsc-ast crate.\n\
         # Bootstrapped from tsc/internal/ast @ ec47d33c by `gen-ast bootstrap`;\n\
         # `gen-ast generate` reads ONLY this file. Re-running bootstrap\n\
         # overwrites it — hand edits belong here, not in the Go parser.\n\n",
    );
    out.push_str("[kinds]\nnames = [\n");
    for (i, k) in schema.kinds.iter().enumerate() {
        let sep = if (i + 1) % 8 == 0 || i + 1 == schema.kinds.len() {
            "\n"
        } else {
            " "
        };
        out.push_str(&format!("    {},{}", toml::escape(k), sep));
    }
    out.push_str("]\n\n");

    for c in &schema.kind_consts {
        out.push_str("[[kind_consts]]\n");
        out.push_str(&format!("name = {}\n", toml::escape(&c.name)));
        out.push_str(&format!("value = {}\n\n", toml::escape(&c.value)));
    }
    for a in &schema.kind_aliases {
        out.push_str("[[kind_aliases]]\n");
        out.push_str(&format!("name = {}\n", toml::escape(&a.name)));
        out.push_str(&format!("kinds = {}\n\n", str_array(&a.kinds)));
    }
    for (section, preds) in [
        ("kind_preds", &schema.kind_preds),
        ("node_preds", &schema.node_preds),
    ] {
        for p in preds {
            out.push_str(&format!("[[{section}]]\n"));
            out.push_str(&format!("name = {}\n", toml::escape(&p.name)));
            if let Some([lo, hi]) = &p.range {
                out.push_str(&format!(
                    "range = [{}, {}]\n",
                    toml::escape(lo),
                    toml::escape(hi)
                ));
            }
            if !p.kinds.is_empty() {
                out.push_str(&format!("kinds = {}\n", str_array(&p.kinds)));
            }
            if let Some(d) = &p.delegate {
                out.push_str(&format!("delegate = {}\n", toml::escape(d)));
            }
            out.push('\n');
        }
    }
    for b in &schema.bases {
        out.push_str("[[bases]]\n");
        out.push_str(&format!("name = {}\n", toml::escape(&b.name)));
        write_fields(&mut out, "fields", &b.fields);
        out.push('\n');
    }
    for n in &schema.nodes {
        let mut body = String::new();
        write_node_body(&mut body, n);
        out.push_str(&body);
        out.push('\n');
    }
    out
}

fn write_node_body(out: &mut String, n: &NodeDef) {
    out.push_str("[[nodes]]\n");
    out.push_str(&format!("name = {}\n", toml::escape(&n.name)));
    if let Some(r) = &n.rust_name {
        out.push_str(&format!("rust_name = {}\n", toml::escape(r)));
    }
    if !n.kinds.is_empty() {
        out.push_str(&format!("kinds = {}\n", str_array(&n.kinds)));
    }
    if !n.bases.is_empty() {
        out.push_str(&format!("bases = {}\n", str_array(&n.bases)));
    }
    if let Some(is) = &n.is_fn {
        out.push_str(&format!("is_fn = {}\n", toml::escape(is)));
    }
    if !n.custom.is_empty() {
        out.push_str(&format!("custom = {}\n", str_array(&n.custom)));
    }
    if n.extra {
        out.push_str("extra = true\n");
    }
    if !n.facts_mode.is_empty() {
        out.push_str(&format!("facts_mode = {}\n", toml::escape(&n.facts_mode)));
    }
    if !n.propagate_mode.is_empty() && n.propagate_mode != "default" {
        out.push_str(&format!("propagate_mode = {}\n", toml::escape(&n.propagate_mode)));
    }
    if let Some(e) = &n.propagate_exclusions {
        out.push_str(&format!("propagate_exclusions = {}\n", toml::escape(e)));
    }
    if !n.propagate_fields.is_empty() {
        out.push_str(&format!("propagate_fields = {}\n", str_array(&n.propagate_fields)));
    }
    write_fields(out, "fields", &n.fields);
    write_news(out, &n.news);
    if let Some(u) = &n.update {
        write_update(out, u);
    }
    write_visit_ops(out, "for_each_child", &n.for_each_child);
    write_visit_args(out, "visit_each_child", &n.visit_each_child);
    write_clone(out, &n.clone);
    write_facts(out, &n.facts);
}

// ── read ───────────────────────────────────────────────────────────────────

fn get_str<'a>(t: &'a std::collections::BTreeMap<String, Value>, key: &str) -> Option<&'a str> {
    t.get(key).and_then(|v| v.as_str())
}

fn get_strs(t: &std::collections::BTreeMap<String, Value>, key: &str) -> Vec<String> {
    t.get(key)
        .and_then(|v| v.as_array())
        .map(|a| a.iter().filter_map(|v| v.as_str().map(|s| s.to_string())).collect())
        .unwrap_or_default()
}

fn get_bool(t: &std::collections::BTreeMap<String, Value>, key: &str) -> bool {
    t.get(key).and_then(|v| v.as_bool()).unwrap_or(false)
}

fn get_tables<'a>(
    t: &'a std::collections::BTreeMap<String, Value>,
    key: &str,
) -> Vec<&'a std::collections::BTreeMap<String, Value>> {
    t.get(key)
        .and_then(|v| v.as_array())
        .map(|a| a.iter().filter_map(|v| v.as_table()).collect())
        .unwrap_or_default()
}

fn get_table<'a>(
    t: &'a std::collections::BTreeMap<String, Value>,
    key: &str,
) -> Option<&'a std::collections::BTreeMap<String, Value>> {
    t.get(key).and_then(|v| v.as_table())
}

fn read_field(t: &std::collections::BTreeMap<String, Value>) -> Result<Field, String> {
    let name = get_str(t, "name").ok_or("field missing name")?.to_string();
    let ty = ty_from_tag(get_str(t, "ty").ok_or("field missing ty")?)?;
    Ok(Field {
        name,
        go_name: get_str(t, "go_name").unwrap_or("").to_string(),
        ty,
        embed: get_str(t, "embed").map(|s| s.to_string()),
        optional: get_bool(t, "optional"),
        exported: !t.contains_key("exported") || get_bool(t, "exported"),
        rust_ty: get_str(t, "rust_ty").map(|s| s.to_string()),
    })
}

fn read_fields(t: &std::collections::BTreeMap<String, Value>, key: &str) -> Result<Vec<Field>, String> {
    get_tables(t, key).iter().map(|f| read_field(f)).collect()
}

fn read_pred(t: &std::collections::BTreeMap<String, Value>) -> Result<KindPred, String> {
    let range = get_strs(t, "range");
    let range = if range.is_empty() {
        None
    } else {
        Some([range[0].clone(), range[1].clone()])
    };
    Ok(KindPred {
        name: get_str(t, "name").ok_or("pred missing name")?.to_string(),
        range,
        kinds: get_strs(t, "kinds"),
        delegate: get_str(t, "delegate").map(|s| s.to_string()),
    })
}

fn read_ctor(t: &std::collections::BTreeMap<String, Value>) -> Result<CtorDef, String> {
    let mut args = Vec::new();
    for a in get_tables(t, "args") {
        args.push(CtorArg {
            name: get_str(a, "name").ok_or("ctor arg missing name")?.to_string(),
            ty: ty_from_tag(get_str(a, "ty").ok_or("ctor arg missing ty")?)?,
            field: get_str(a, "field").map(|s| s.to_string()),
            init_mask: get_str(a, "mask").map(|s| s.to_string()),
            go_ty: get_str(a, "go_ty").unwrap_or("").to_string(),
        });
    }
    let post: Vec<CtorPost> = get_strs(t, "post")
        .iter()
        .filter_map(|p| {
            if let Some(a) = p.strip_prefix("set_flags:") {
                Some(CtorPost::SetFlags { arg: a.to_string() })
            } else {
                p.strip_prefix("or_optional_chain:")
                    .map(|a| CtorPost::OrOptionalChain { arg: a.to_string() })
            }
        })
        .collect();
    Ok(CtorDef {
        name: get_str(t, "name").ok_or("ctor missing name")?.to_string(),
        kind: get_str(t, "kind").map(|s| s.to_string()),
        kind_arg: get_str(t, "kind_arg").map(|s| s.to_string()),
        args,
        post,
        counts_text: get_bool(t, "counts_text"),
        counts_identifier: get_bool(t, "counts_identifier"),
    })
}

fn read_update(t: &std::collections::BTreeMap<String, Value>) -> Result<UpdateDef, String> {
    let mut args = Vec::new();
    for a in get_tables(t, "args") {
        args.push(UpdateArg {
            name: get_str(a, "name").ok_or("update arg missing name")?.to_string(),
            ty: ty_from_tag(get_str(a, "ty").ok_or("update arg missing ty")?)?,
        });
    }
    let mut compares = Vec::new();
    for c in get_tables(t, "compares") {
        compares.push(UpdateCompare {
            lhs: get_str(c, "lhs").ok_or("compare missing lhs")?.to_string(),
            field: get_str(c, "field").ok_or("compare missing field")?.to_string(),
            op: get_str(c, "op").ok_or("compare missing op")?.to_string(),
        });
    }
    Ok(UpdateDef {
        name: get_str(t, "name").ok_or("update missing name")?.to_string(),
        args,
        compares,
        new_fn: get_str(t, "new_fn").ok_or("update missing new_fn")?.to_string(),
        new_args: get_strs(t, "new_args"),
    })
}

fn read_visit_ops(t: &std::collections::BTreeMap<String, Value>, key: &str) -> Vec<VisitOp> {
    get_tables(t, key)
        .iter()
        .filter_map(|o| {
            Some(VisitOp {
                op: get_str(o, "op")?.to_string(),
                field: get_str(o, "field")?.to_string(),
            })
        })
        .collect()
}

fn read_visit_args(t: &std::collections::BTreeMap<String, Value>, key: &str) -> Vec<VisitArg> {
    get_tables(t, key)
        .iter()
        .filter_map(|o| {
            Some(VisitArg {
                op: get_str(o, "op")?.to_string(),
                field: get_str(o, "field").map(|s| s.to_string()),
            })
        })
        .collect()
}

fn read_clone(t: &std::collections::BTreeMap<String, Value>) -> Vec<CloneArm> {
    get_tables(t, "clone")
        .iter()
        .filter_map(|a| {
            Some(CloneArm {
                kind: get_str(a, "kind").map(|s| s.to_string()),
                new_fn: get_str(a, "new_fn")?.to_string(),
                args: get_strs(a, "args"),
            })
        })
        .collect()
}

fn read_facts(t: &std::collections::BTreeMap<String, Value>) -> Vec<FactOp> {
    get_tables(t, "facts")
        .iter()
        .filter_map(|o| {
            Some(FactOp {
                op: get_str(o, "op")?.to_string(),
                field: get_str(o, "field").map(|s| s.to_string()),
                value: get_str(o, "value").map(|s| s.to_string()),
            })
        })
        .collect()
}

fn defaults_apply(schema: &mut Schema) {
    // Mirror `postprocess` defaults for keys omitted from the TOML.
    let ts_bases: Vec<bool> = schema
        .nodes
        .iter()
        .map(|n| schema.has_base(&n.bases, "TypeSyntaxBase"))
        .collect();
    for (i, node) in schema.nodes.iter_mut().enumerate() {
        if node.facts_mode.is_empty() {
            node.facts_mode = if !node.facts.is_empty() {
                "generated"
            } else if ts_bases[i] {
                "typescript"
            } else {
                "none"
            }
            .into();
        }
        if node.propagate_mode.is_empty() {
            node.propagate_mode = if ts_bases[i] { "typescript" } else { "default" }.into();
        }
    }
}

pub fn read_schema(doc: &Document) -> Result<Schema, String> {
    let mut schema = Schema::default();
    let kinds_table = doc
        .tables
        .get("kinds")
        .ok_or("missing [kinds] section")?;
    schema.kinds = get_strs(kinds_table, "names");
    if schema.kinds.is_empty() {
        return Err("[kinds].names is empty".into());
    }
    for t in doc.arrays.get("kind_consts").cloned().unwrap_or_default() {
        schema.kind_consts.push(KindConst {
            name: get_str(&t, "name").ok_or("kind_const missing name")?.to_string(),
            value: get_str(&t, "value").ok_or("kind_const missing value")?.to_string(),
        });
    }
    for t in doc.arrays.get("kind_aliases").cloned().unwrap_or_default() {
        schema.kind_aliases.push(KindAlias {
            name: get_str(&t, "name").ok_or("kind_alias missing name")?.to_string(),
            kinds: get_strs(&t, "kinds"),
        });
    }
    for t in doc.arrays.get("kind_preds").cloned().unwrap_or_default() {
        schema.kind_preds.push(read_pred(&t)?);
    }
    for t in doc.arrays.get("node_preds").cloned().unwrap_or_default() {
        schema.node_preds.push(read_pred(&t)?);
    }
    for t in doc.arrays.get("bases").cloned().unwrap_or_default() {
        schema.bases.push(BaseDef {
            name: get_str(&t, "name").ok_or("base missing name")?.to_string(),
            fields: read_fields(&t, "fields")?,
        });
    }
    for t in doc.arrays.get("nodes").cloned().unwrap_or_default() {
        let mut news = Vec::new();
        for c in get_tables(&t, "news") {
            news.push(read_ctor(c)?);
        }
        schema.nodes.push(NodeDef {
            name: get_str(&t, "name").ok_or("node missing name")?.to_string(),
            rust_name: get_str(&t, "rust_name").map(|s| s.to_string()),
            kinds: get_strs(&t, "kinds"),
            bases: get_strs(&t, "bases"),
            fields: read_fields(&t, "fields")?,
            news,
            update: match get_table(&t, "update") {
                Some(u) => Some(read_update(u)?),
                None => None,
            },
            for_each_child: read_visit_ops(&t, "for_each_child"),
            visit_each_child: read_visit_args(&t, "visit_each_child"),
            clone: read_clone(&t),
            facts: read_facts(&t),
            facts_mode: get_str(&t, "facts_mode").unwrap_or("").to_string(),
            propagate_mode: get_str(&t, "propagate_mode").unwrap_or("").to_string(),
            propagate_exclusions: get_str(&t, "propagate_exclusions").map(|s| s.to_string()),
            propagate_fields: get_strs(&t, "propagate_fields"),
            is_fn: get_str(&t, "is_fn").map(|s| s.to_string()),
            custom: get_strs(&t, "custom"),
            extra: get_bool(&t, "extra"),
        });
    }
    defaults_apply(&mut schema);
    Ok(schema)
}

pub fn load_schema(path: &std::path::Path) -> Result<Schema, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let doc = toml::parse(&text)?;
    read_schema(&doc)
}
