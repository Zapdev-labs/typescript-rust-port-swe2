// Emits `ast_generated.rs` from the schema: payload structs (with nested base
// fields), the `NodeData` enum and its dispatch methods, factory `new_*` /
// `update_*` / `clone_node`, `for_each_child`, `visit_each_child`, node
// accessors (`as_*`), `is_*` predicates, and subtree-facts plumbing.
//
// Conventions established by the hand-written core (ast.rs, visitor.rs):
//   - `*Node` fields → `Option<NodeId>`; `*NodeList` → `Option<NodeList>`;
//     `*ModifierList` → `Option<ModifierList>`; `[]*Node` → `Box<[NodeId]>`.
//   - Embedded bases are nested fields named `snake_case(BaseName)`.
//   - Factory methods take `nodes: &mut Vec<Node>` first; updates return
//     `Option<NodeId>` where `None` = unchanged.
//   - `visit_each_child` is a free fn taking `&mut VisitorCx`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::goparse::rust_name;
use crate::model::*;

pub struct Emitter<'a> {
    schema: &'a Schema,
    base_map: BTreeMap<&'a str, &'a BaseDef>,
    node_map: BTreeMap<&'a str, &'a NodeDef>,
}

/// `SubtreeContainsTypeScript` → `SubtreeFacts::CONTAINS_TYPE_SCRIPT`.
fn facts_const(name: &str) -> String {
    let short = name.strip_prefix("Subtree").unwrap_or(name);
    let mut out = String::new();
    for (i, c) in short.chars().enumerate() {
        if c.is_ascii_uppercase() && i > 0 {
            out.push('_');
        }
        out.push(c.to_ascii_uppercase());
    }
    format!("SubtreeFacts::{out}")
}

/// `TokenFlagsStringLiteralFlags` → `TokenFlags::STRING_LITERAL_FLAGS`;
/// `NodeFlagsOptionalChain` → `NodeFlags::OPTIONAL_CHAIN`.
fn flags_const(name: &str) -> String {
    for prefix in ["NodeFlags", "TokenFlags", "ModifierFlags"] {
        if let Some(rest) = name.strip_prefix(prefix) {
            let mut out = String::new();
            for (i, c) in rest.chars().enumerate() {
                if c.is_ascii_uppercase() && i > 0 {
                    out.push('_');
                }
                out.push(c.to_ascii_uppercase());
            }
            return format!("{prefix}::{out}");
        }
    }
    name.to_string()
}

/// Rust type of a field.
fn field_ty(f: &Field) -> String {
    match f.ty {
        FieldType::Embed => f.embed.clone().unwrap_or_default(),
        FieldType::Node => "Option<NodeId>".into(),
        FieldType::NodeList => "Option<NodeList>".into(),
        FieldType::ModifierList => "Option<ModifierList>".into(),
        FieldType::NodeSlice => "Box<[NodeId]>".into(),
        FieldType::StringSlice => "Box<[String]>".into(),
        FieldType::Str => "String".into(),
        FieldType::Bool => "bool".into(),
        FieldType::Int => "i32".into(),
        FieldType::Kind => "Kind".into(),
        FieldType::TokenFlags => "TokenFlags".into(),
        FieldType::NodeFlags => "NodeFlags".into(),
        FieldType::Symbol => "Option<SymbolId>".into(),
        FieldType::SymbolTable => "SymbolTable".into(),
        FieldType::FlowNode => "Option<FlowNodeId>".into(),
        FieldType::FlowList => "Option<FlowListId>".into(),
        FieldType::AtomicU32 => "Cell<u32>".into(),
        FieldType::Any => "Option<u64>".into(),
        FieldType::Other => f
            .rust_ty
            .clone()
            .unwrap_or_else(|| "()".into()),
    }
}

/// Rust type of a ctor/update parameter.
fn arg_ty(ty: FieldType, name: &str, rust_ty: Option<&str>) -> String {
    match ty {
        FieldType::Node => "Option<NodeId>".into(),
        FieldType::NodeList => "Option<NodeList>".into(),
        FieldType::ModifierList => "Option<ModifierList>".into(),
        FieldType::NodeSlice => "&[NodeId]".into(),
        FieldType::StringSlice => "&[String]".into(),
        FieldType::Str => "&str".into(),
        FieldType::Bool => "bool".into(),
        FieldType::Int => "i32".into(),
        FieldType::Kind => "Kind".into(),
        FieldType::TokenFlags => "TokenFlags".into(),
        FieldType::NodeFlags => "NodeFlags".into(),
        FieldType::Symbol => "Option<SymbolId>".into(),
        FieldType::SymbolTable => "SymbolTable".into(),
        FieldType::FlowNode => "Option<FlowNodeId>".into(),
        FieldType::FlowList => "Option<FlowListId>".into(),
        FieldType::AtomicU32 => "u32".into(),
        FieldType::Any => "Option<u64>".into(),
        FieldType::Other => rust_ty
            .map(|s| s.to_string())
            .unwrap_or_else(|| panic!("no rust_ty for Other arg {name}")),
        FieldType::Embed => unreachable!("embed arg"),
    }
}

impl<'a> Emitter<'a> {
    pub fn new(schema: &'a Schema) -> Emitter<'a> {
        Emitter {
            schema,
            base_map: schema.base_map(),
            node_map: schema.nodes.iter().map(|n| (n.name.as_str(), n)).collect(),
        }
    }

    /// A struct's own + embedded (base) fields: embeds stay as named fields.
    fn base_fields(&self, base: &str) -> &[Field] {
        self.base_map.get(base).map(|b| b.fields.as_slice()).unwrap_or(&[])
    }

    /// Breadth-first field-path resolution, mirroring Go promotion (shallower
    /// wins; own fields are depth 0). Returns the dotted path from `root`
    /// (e.g. `named_member_base.declaration_base.symbol`).
    fn resolve_field(&self, fields: &[Field], name: &str) -> Option<String> {
        for f in fields {
            if f.ty != FieldType::Embed && f.name == name {
                return Some(name.to_string());
            }
        }
        // BFS over bases.
        let mut queue: VecDeque<(String, String)> = VecDeque::new(); // (path, base)
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for f in fields {
            if f.ty == FieldType::Embed {
                if let Some(e) = &f.embed {
                    if seen.insert(e.clone()) {
                        queue.push_back((f.name.clone(), e.clone()));
                    }
                }
            }
        }
        while let Some((path, base)) = queue.pop_front() {
            for f in self.base_fields(&base) {
                if f.ty == FieldType::Embed {
                    if let Some(e) = &f.embed {
                        if seen.insert(e.clone()) {
                            queue.push_back((format!("{path}.{}", f.name), e.clone()));
                        }
                    }
                } else if f.name == name {
                    return Some(format!("{path}.{}", f.name));
                }
            }
        }
        None
    }

    /// Path to the embedded base struct `target` (e.g. `FlowNodeBase`),
    /// BFS over `fields`.
    fn resolve_base(&self, fields: &[Field], target: &str) -> Option<String> {
        let mut queue: VecDeque<(String, String)> = VecDeque::new();
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for f in fields {
            if f.ty == FieldType::Embed {
                if let Some(e) = &f.embed {
                    if e == target {
                        return Some(f.name.clone());
                    }
                    if seen.insert(e.clone()) {
                        queue.push_back((f.name.clone(), e.clone()));
                    }
                }
            }
        }
        while let Some((path, base)) = queue.pop_front() {
            for f in self.base_fields(&base) {
                if f.ty == FieldType::Embed {
                    if let Some(e) = &f.embed {
                        if e == target {
                            return Some(format!("{path}.{}", f.name));
                        }
                        if seen.insert(e.clone()) {
                            queue.push_back((format!("{path}.{}", f.name), e.clone()));
                        }
                    }
                }
            }
        }
        None
    }

    /// Whether the node's transitive bases include `target`.
    fn node_has_base(&self, node: &NodeDef, target: &str) -> bool {
        let fields: Vec<Field> = node
            .bases
            .iter()
            .map(|b| Field {
                go_name: b.clone(),
                name: rust_name(b),
                ty: FieldType::Embed,
                embed: Some(b.clone()),
                optional: false,
                exported: false,
                rust_ty: None,
            })
            .collect();
        self.resolve_base(&fields, target).is_some()
    }

    fn field_path(&self, node: &NodeDef, name: &str) -> String {
        // try own fields, then embeds (bases are themselves `embed` fields
        // once emitted — resolve against the synthetic field list).
        let fields = self.node_fields(node);
        self.resolve_field(&fields, name)
            .unwrap_or_else(|| panic!("{}: no field `{name}`", node.name))
    }

    /// Synthetic field list for a node: bases become `embed` fields.
    fn node_fields(&self, node: &NodeDef) -> Vec<Field> {
        let mut fields: Vec<Field> = node
            .bases
            .iter()
            .map(|b| Field {
                go_name: b.clone(),
                name: rust_name(b),
                ty: FieldType::Embed,
                embed: Some(b.clone()),
                optional: false,
                exported: false,
                rust_ty: None,
            })
            .collect();
        fields.extend(node.fields.iter().cloned());
        fields
    }

    fn base_path(&self, node: &NodeDef, target: &str) -> Option<String> {
        self.resolve_base(&self.node_fields(node), target)
    }

    // ── structs ─────────────────────────────────────────────────────────

    fn emit_struct(&self, out: &mut String, name: &str, fields: &[Field]) {
        out.push_str(&format!("/// `type {name} struct`.\n#[derive(Default)]\npub struct {name} {{\n"));
        for f in fields {
            if f.ty == FieldType::Embed {
                let base = f.embed.as_deref().unwrap_or("");
                if base == "NodeBase" || base == "NodeDefault" {
                    continue; // the Node header lives outside NodeData
                }
                out.push_str(&format!(
                    "    /// embedded `{}`\n    pub {}: {},\n",
                    base,
                    f.name,
                    base
                ));
            } else {
                out.push_str(&format!("    pub {}: {},\n", f.name, field_ty(f)));
            }
        }
        out.push_str("}\n\n");
    }

    // ── enum + dispatch ─────────────────────────────────────────────────

    fn variant_name(&self, node: &NodeDef) -> String {
        node.rust_name.clone().unwrap_or_else(|| node.name.clone())
    }

    pub fn emit(&self) -> String {
        let mut out = String::new();
        out.push_str(
            "// Code generated by `gen-ast` from kinds.toml; DO NOT EDIT.\n\
             // Mirrors tsc/internal/ast/ast_generated.go.\n\n\
             use std::cell::Cell;\n\n\
             use crate::ast::{ModifierList, Node, NodeFactory, NodeList, Visitor};\n\
             use crate::ids::{FlowListId, FlowNodeId, NodeId, SymbolId};\n\
             use crate::kind_generated::Kind;\n\
             use crate::modifierflags::ModifierFlags;\n\
             use crate::nodeflags::NodeFlags;\n\
             use crate::subtreefacts::SubtreeFacts;\n\
             use crate::symbol::SymbolTable;\n\
             use crate::tokenflags::TokenFlags;\n\
             use crate::visitor::{NodeVisitor, VisitorCx};\n\n",
        );

        for b in &self.schema.bases {
            if b.name == "NodeBase" || b.name == "NodeDefault" {
                continue;
            }
            self.emit_struct(&mut out, &b.name, &b.fields);
        }
        for n in &self.schema.nodes {
            let mut fields = self.node_fields(n);
            fields.retain(|f| {
                f.embed.as_deref() != Some("NodeBase") && f.embed.as_deref() != Some("NodeDefault")
            });
            let name = self.variant_name(n);
            self.emit_struct(&mut out, &name, &fields);
        }

        // NodeData enum.
        out.push_str("/// `nodeData` — the payload enum; every variant is a\n");
        out.push_str("/// generated or hand-authored node data struct.\n");
        out.push_str("pub enum NodeData {\n");
        for n in &self.schema.nodes {
            let v = self.variant_name(n);
            out.push_str(&format!("    {v}({v}),\n"));
        }
        out.push_str("}\n\n");

        self.emit_node_data_impl(&mut out);
        self.emit_node_accessors(&mut out);
        self.emit_is_fns(&mut out);
        self.emit_factory(&mut out);
        self.emit_clone_dispatch(&mut out);
        self.emit_visit_each_child(&mut out);
        self.emit_facts_helpers(&mut out);
        out
    }

    fn emit_node_data_impl(&self, out: &mut String) {
        out.push_str("impl NodeData {\n");
        // as_ / as_mut
        for n in &self.schema.nodes {
            let v = self.variant_name(n);
            let m = rust_name(&n.name);
            out.push_str(&format!(
                "    /// `n.As{name}()`.\n    pub fn as_{m}(&self) -> &{v} {{\n        match self {{\n            NodeData::{v}(d) => d,\n            _ => panic!(\"as_{m} on wrong data variant\"),\n        }}\n    }}\n\n",
                name = n.name
            ));
            out.push_str(&format!(
                "    /// mutable `As{name}()`.\n    pub fn as_{m}_mut(&mut self) -> &mut {v} {{\n        match self {{\n            NodeData::{v}(d) => d,\n            _ => panic!(\"as_{m}_mut on wrong data variant\"),\n        }}\n    }}\n\n",
                name = n.name
            ));
        }

        // for_each_child
        out.push_str(
            "    /// `data.ForEachChild(v)` — `true` stops traversal.\n    pub fn for_each_child(&self, visitor: &mut Visitor<'_>, nodes: &[Node]) -> bool {\n        match self {\n",
        );
        for n in &self.schema.nodes {
            let v = self.variant_name(n);
            if n.custom.iter().any(|c| c == "for_each_child") {
                out.push_str(&format!(
                    "            NodeData::{v}(d) => crate::ast::for_each_child_{}(d, visitor, nodes),\n",
                    rust_name(&n.name)
                ));
            } else if n.for_each_child.is_empty() {
                out.push_str(&format!("            NodeData::{v}(_) => false,\n"));
            } else {
                let mut terms = Vec::new();
                for op in &n.for_each_child {
                    let path = self.field_path(n, &op.field);
                    let expr = match op.op.as_str() {
                        "visit" => format!("crate::ast::visit(visitor, d.{path}, nodes)"),
                        "visitNodes" => {
                            format!("crate::ast::visit_nodes(visitor, &d.{path}, nodes)")
                        }
                        "visitNodeList" => {
                            format!("crate::ast::visit_node_list(visitor, &d.{path}, nodes)")
                        }
                        "visitModifiers" => {
                            format!("crate::ast::visit_modifiers(visitor, &d.{path}, nodes)")
                        }
                        o => panic!("unknown forEachChild op {o}"),
                    };
                    terms.push(expr);
                }
                out.push_str(&format!(
                    "            NodeData::{v}(d) => {},\n",
                    terms.join(" ||\n                ")
                ));
            }
        }
        out.push_str("        }\n    }\n\n");

        // modifiers / set_modifiers / name
        out.push_str(
            "    /// `data.Modifiers()` — the node's modifier list, when its\n    /// (transitive) bases declare one.\n    pub fn modifiers(&self) -> Option<&ModifierList> {\n        match self {\n",
        );
        for n in &self.schema.nodes {
            if let Some(path) = self.resolve_field(&self.node_fields(n), "modifiers") {
                let v = self.variant_name(n);
                out.push_str(&format!(
                    "            NodeData::{v}(d) => d.{path}.as_ref(),\n"
                ));
            }
        }
        out.push_str("            _ => None,\n        }\n    }\n\n");
        out.push_str(
            "    /// `data.setModifiers(m)`.\n    pub fn set_modifiers(&mut self, modifiers: Option<ModifierList>) {\n        match self {\n",
        );
        for n in &self.schema.nodes {
            if let Some(path) = self.resolve_field(&self.node_fields(n), "modifiers") {
                let v = self.variant_name(n);
                out.push_str(&format!(
                    "            NodeData::{v}(d) => d.{path} = modifiers,\n"
                ));
            }
        }
        out.push_str("            _ => {}\n        }\n    }\n\n");
        out.push_str(
            "    /// `data.Name()`.\n    pub fn name(&self) -> Option<NodeId> {\n        match self {\n",
        );
        for n in &self.schema.nodes {
            if let Some(path) = self.resolve_field(&self.node_fields(n), "name") {
                let v = self.variant_name(n);
                out.push_str(&format!("            NodeData::{v}(d) => d.{path},\n"));
            }
        }
        out.push_str("            _ => None,\n        }\n    }\n\n");

        // base-data accessors
        for (method, base, ret) in [
            ("flow_node_data", "FlowNodeBase", "FlowNodeBase"),
            ("declaration_data", "DeclarationBase", "DeclarationBase"),
            ("exportable_data", "ExportableBase", "ExportableBase"),
            ("locals_container_data", "LocalsContainerBase", "LocalsContainerBase"),
            ("function_like_data", "FunctionLikeBase", "FunctionLikeBase"),
            ("class_like_data", "ClassLikeBase", "ClassLikeBase"),
            ("body_data", "BodyBase", "BodyBase"),
            ("literal_like_data", "LiteralLikeNodeBase", "LiteralLikeNodeBase"),
            (
                "template_literal_like_data",
                "TemplateLiteralLikeNodeBase",
                "TemplateLiteralLikeNodeBase",
            ),
        ] {
            self.emit_base_accessor(out, method, base, ret, false);
            self.emit_base_accessor(out, &format!("{method}_mut"), base, ret, true);
        }

        // subtree facts
        out.push_str(
            "    /// `data.SubtreeFacts()` — cached for composite nodes,\n    /// computed on demand otherwise.\n    pub fn subtree_facts(&self, node: &Node, nodes: &[Node]) -> SubtreeFacts {\n        match self {\n",
        );
        for n in &self.schema.nodes {
            let v = self.variant_name(n);
            let compute = self.compute_expr(n);
            if let Some(cp) = self.base_path(n, "CompositeBase") {
                out.push_str(&format!(
                    "            NodeData::{v}(d) => {{\n                let cached = SubtreeFacts(d.{cp}.facts.get());\n                if !cached.intersects(SubtreeFacts::COMPUTED) {{\n                    let f = {compute} | SubtreeFacts::COMPUTED;\n                    d.{cp}.facts.set(f.0);\n                    return f.without(SubtreeFacts::COMPUTED);\n                }}\n                cached.without(SubtreeFacts::COMPUTED)\n            }},\n"
                ));
            } else {
                out.push_str(&format!("            NodeData::{v}(d) => {compute},\n"));
            }
        }
        out.push_str("        }\n    }\n\n");

        // propagate
        out.push_str(
            "    /// `data.propagateSubtreeFacts()` — subtree facts as seen by\n    /// this node's parent (exclusions applied).\n    pub fn propagate_subtree_facts(&self, node: &Node, nodes: &[Node]) -> SubtreeFacts {\n        match self {\n",
        );
        for n in &self.schema.nodes {
            let v = self.variant_name(n);
            let expr = self.propagate_expr(n);
            out.push_str(&format!("            NodeData::{v}(_d) => {expr},\n"));
        }
        out.push_str("        }\n    }\n");
        out.push_str("}\n\n");
    }

    /// Expression computing a node's own subtree facts (pre-cache).
    fn compute_expr(&self, n: &NodeDef) -> String {
        match n.facts_mode.as_str() {
            "typescript" => "SubtreeFacts::CONTAINS_TYPE_SCRIPT".into(),
            "custom" => format!("crate::subtreefacts::compute_{}(node, nodes)", rust_name(&n.name)),
            "generated" | "none" => {
                if n.facts.is_empty() {
                    "SubtreeFacts::NONE".into()
                } else {
                    let terms: Vec<String> = n
                        .facts
                        .iter()
                        .map(|op| match op.op.as_str() {
                            "propagate" => {
                                let p = self.field_path(n, op.field.as_deref().unwrap());
                                format!("propagate_subtree_facts_opt(nodes, d.{p})")
                            }
                            "propagateList" => {
                                let p = self.field_path(n, op.field.as_deref().unwrap());
                                format!("propagate_node_list_subtree_facts(nodes, &d.{p})")
                            }
                            "propagateModifierList" => {
                                let p = self.field_path(n, op.field.as_deref().unwrap());
                                format!("propagate_modifier_list_subtree_facts(nodes, &d.{p})")
                            }
                            "const" => facts_const(op.value.as_deref().unwrap()),
                            o => panic!("bad fact op {o}"),
                        })
                        .collect();
                    terms.join(" |\n                    ")
                }
            }
            other => panic!("bad facts_mode {other}"),
        }
    }

    fn propagate_expr(&self, n: &NodeDef) -> String {
        let mut expr = match n.propagate_mode.as_str() {
            "typescript" => "SubtreeFacts::CONTAINS_TYPE_SCRIPT".into(),
            "custom" => {
                return format!("crate::subtreefacts::propagate_{}(node, nodes)", rust_name(&n.name))
            }
            "exclusions" => {
                let exc = n.propagate_exclusions.as_deref().unwrap_or("SubtreeExclusionsNode");
                format!(
                    "node.subtree_facts(nodes).without({})",
                    facts_const(exc)
                )
            }
            _ => "node.subtree_facts(nodes).without(SubtreeFacts::EXCLUSIONS_NODE)".into(),
        };
        for f in &n.propagate_fields {
            let p = self.field_path(n, f);
            expr.push_str(&format!(" | propagate_subtree_facts_opt(nodes, _d.{p})"));
        }
        expr
    }

    fn emit_base_accessor(
        &self,
        out: &mut String,
        method: &str,
        base: &str,
        ret: &str,
        mutable: bool,
    ) {
        let amp = if mutable { "&mut " } else { "&" };
        out.push_str(&format!(
            "    /// `data.{}Data()` — the embedded `{base}` when present.\n    pub fn {method}(&{sm}self) -> Option<{amp}{ret}> {{\n        match self {{\n",
            base.trim_end_matches("Base"),
            sm = if mutable { "mut " } else { "" },
        ));
        for n in &self.schema.nodes {
            if let Some(path) = self.base_path(n, base) {
                let v = self.variant_name(n);
                let pat = if mutable {
                    format!("NodeData::{v}(d) => Some(&mut d.{path}),\n")
                } else {
                    format!("NodeData::{v}(d) => Some(&d.{path}),\n")
                };
                out.push_str(&format!("            {pat}"));
            }
        }
        out.push_str("            _ => None,\n        }\n    }\n\n");
    }

    fn emit_node_accessors(&self, out: &mut String) {
        out.push_str("// ── `n.AsX()` accessors ─────────────────────────────────────────────\n\n");
        out.push_str("impl Node {\n");
        for n in &self.schema.nodes {
            let v = self.variant_name(n);
            let m = rust_name(&n.name);
            out.push_str(&format!(
                "    /// `n.As{name}()` — panics on kind mismatch, like Go's\n    /// unchecked type assertion.\n    pub fn as_{m}(&self) -> &{v} {{\n        self.data.as_{m}()\n    }}\n\n    /// mutable `As{name}()`.\n    pub fn as_{m}_mut(&mut self) -> &mut {v} {{\n        self.data.as_{m}_mut()\n    }}\n",
                name = n.name
            ));
        }
        out.push_str("}\n\n");
    }

    fn emit_is_fns(&self, out: &mut String) {
        out.push_str("// ── `IsX(node)` predicates ────────────────────────────────────────\n\n");
        let mut emitted = BTreeSet::new();
        for n in &self.schema.nodes {
            let Some(is) = &n.is_fn else { continue };
            let name = rust_name(is);
            if !emitted.insert(name.clone()) {
                continue;
            }
            let cond = if n.kinds.len() == 1 {
                format!("node.kind == Kind::{}", n.kinds[0])
            } else if n.kinds.is_empty() {
                format!("let _ = node;\n    false // TODO: {is} hand-port")
            } else {
                let arms: Vec<String> = n.kinds.iter().map(|k| format!("Kind::{k}")).collect();
                format!("matches!(node.kind, {})", arms.join(" | "))
            };
            out.push_str(&format!(
                "/// `{is}`.\npub fn {name}(node: &Node) -> bool {{\n    {cond}\n}}\n\n"
            ));
        }
        for p in &self.schema.node_preds {
            let name = rust_name(&p.name);
            if !emitted.insert(name.clone()) {
                continue;
            }
            out.push_str(&format!("/// `{}`.\npub fn {name}(node: &Node) -> bool {{\n", p.name));
            if let Some(d) = &p.delegate {
                out.push_str(&format!("    node.kind.{}()\n", rust_name(d)));
            } else if let Some([lo, hi]) = &p.range {
                let lo_c = const_like(lo);
                let hi_c = const_like(hi);
                out.push_str(&format!(
                    "    node.kind >= Kind::{lo_c} && node.kind <= Kind::{hi_c}\n"
                ));
            } else if !p.kinds.is_empty() {
                let arms: Vec<String> = p.kinds.iter().map(|k| format!("Kind::{k}")).collect();
                out.push_str(&format!("    matches!(node.kind, {})\n", arms.join(" | ")));
            } else {
                out.push_str(&format!("    let _ = node;\n    false // TODO: {} hand-port\n", p.name));
            }
            out.push_str("}\n\n");
        }
    }

    // ── factory ─────────────────────────────────────────────────────────

    fn emit_factory(&self, out: &mut String) {
        out.push_str("// ── `NodeFactory` constructors / updates ──────────────────────────\n\n");
        out.push_str("impl NodeFactory<'_> {\n");
        for n in &self.schema.nodes {
            for ctor in &n.news {
                self.emit_ctor(out, n, ctor);
            }
            if let Some(u) = &n.update {
                if !n.custom.iter().any(|c| c == "update") {
                    self.emit_update(out, n, u);
                }
            }
        }
        out.push_str("}\n\n");
    }

    fn emit_ctor(&self, out: &mut String, n: &NodeDef, c: &CtorDef) {
        let fname = rust_name(&c.name);
        let mut params: Vec<String> = vec!["nodes: &mut Vec<Node>".into()];
        for a in &c.args {
            if a.name.starts_with("__lit_") {
                continue;
            }
            if Some(&a.name) == c.kind_arg.as_ref() {
                params.push(format!("{}: Kind", rust_name(&a.name)));
                continue;
            }
            params.push(format!("{}: {}", rust_name(&a.name), arg_ty(a.ty, &a.name, None)));
        }
        out.push_str(&format!(
            "    /// `{go}`.\n    pub fn {fname}(&mut self, {}) -> NodeId {{\n",
            params.join(", "),
            go = c.name
        ));
        let v = self.variant_name(n);
        out.push_str(&format!("        let mut data = {v}::default();\n"));
        for a in &c.args {
            let Some(field) = &a.field else { continue };
            let path = self.field_path(n, field);
            if let Some(mask) = &a.init_mask {
                if let Some(lit) = mask.strip_prefix("lit:") {
                    out.push_str(&format!("        data.{path} = {lit};\n"));
                } else {
                    out.push_str(&format!(
                        "        data.{path} = {} & {};\n",
                        rust_name(&a.name),
                        flags_const(mask)
                    ));
                }
            } else {
                let expr = match a.ty {
                    FieldType::Str => format!("{}.to_string()", rust_name(&a.name)),
                    FieldType::NodeSlice | FieldType::StringSlice => {
                        format!("{}.into()", rust_name(&a.name))
                    }
                    _ => rust_name(&a.name),
                };
                out.push_str(&format!("        data.{path} = {expr};\n"));
            }
        }
        if c.counts_text {
            out.push_str("        self.text_count += 1;\n");
        }
        if c.counts_identifier {
            out.push_str("        self.identifier_count += 1;\n");
        }
        let kind_expr = if let Some(k) = &c.kind {
            format!("Kind::{k}")
        } else {
            rust_name(c.kind_arg.as_deref().unwrap_or("kind"))
        };
        if c.post.is_empty() {
            out.push_str(&format!(
                "        self.new_node(nodes, {kind_expr}, NodeData::{v}(data))\n"
            ));
        } else {
            out.push_str(&format!(
                "        let node = self.new_node(nodes, {kind_expr}, NodeData::{v}(data));\n"
            ));
            for p in &c.post {
                match p {
                    CtorPost::SetFlags { arg } => {
                        out.push_str(&format!(
                            "        nodes[node].flags = {};\n",
                            rust_name(arg)
                        ));
                    }
                    CtorPost::OrOptionalChain { arg } => {
                        out.push_str(&format!(
                            "        nodes[node].flags.insert({} & NodeFlags::OPTIONAL_CHAIN);\n",
                            rust_name(arg)
                        ));
                    }
                }
            }
            out.push_str("        node\n");
        }
        out.push_str("    }\n\n");
    }

    fn emit_update(&self, out: &mut String, n: &NodeDef, u: &UpdateDef) {
        let fname = rust_name(&u.name);
        let mut params = vec!["nodes: &mut Vec<Node>".to_string(), "node: NodeId".to_string()];
        for a in &u.args {
            params.push(format!("{}: {}", rust_name(&a.name), arg_ty(a.ty, &a.name, None)));
        }
        out.push_str(&format!(
            "    /// `{go}` — `None` when nothing changed (Go returned the\n    /// input pointer).\n    pub fn {fname}(&mut self, {}) -> Option<NodeId> {{\n",
            params.join(", "),
            go = u.name
        ));
        // changed check under a scoped immutable borrow
        let m = rust_name(&n.name);
        out.push_str(&format!("        let changed = {{\n            let d = nodes[node].as_{m}();\n            "));
        let conds: Vec<String> = u
            .compares
            .iter()
            .map(|c| {
                if c.field == "flags" {
                    return format!("{} != nodes[node].flags", rust_name(&c.lhs));
                }
                if c.field == "kind" {
                    return format!("{} != nodes[node].kind", rust_name(&c.lhs));
                }
                let p = self.field_path(n, &c.field);
                let lhs = rust_name(&c.lhs);
                // Slice args (`&[NodeId]`, `&[String]`) compare against
                // `Box<[T]>` fields — dereference both sides.
                let lhs_is_slice = u.args.iter().any(|a| {
                    rust_name(&a.name) == lhs
                        && matches!(
                            a.ty,
                            FieldType::NodeSlice | FieldType::StringSlice
                        )
                });
                match (c.op.as_str(), lhs_is_slice) {
                    ("same" | "neq", false) => format!("{lhs} != d.{p}"),
                    ("same" | "neq", true) => format!("*{lhs} != *d.{p}"),
                    (o, _) => panic!("bad compare op {o}"),
                }
            })
            .collect();
        out.push_str(&conds.join(" || "));
        out.push_str("\n        };\n        if changed {\n");
        // rebuild args
        for (i, arg) in u.new_args.iter().enumerate() {
            if let Some(f) = arg.strip_prefix("node.") {
                if f == "Kind" {
                    out.push_str(&format!("            let a{i} = nodes[node].kind;\n"));
                } else if f == "Flags" {
                    out.push_str(&format!("            let a{i} = nodes[node].flags;\n"));
                } else if f == "Modifiers()" {
                    out.push_str(&format!(
                        "            let a{i} = nodes[node].modifiers().cloned();\n"
                    ));
                } else if f == "Name()" {
                    out.push_str(&format!("            let a{i} = nodes[node].name();\n"));
                } else {
                    let p = self.field_path(n, &rust_name(f));
                    out.push_str(&format!(
                        "            let a{i} = nodes[node].as_{m}().{p}.clone();\n"
                    ));
                }
            } else {
                out.push_str(&format!("            let a{i} = {};\n", rust_name(arg)));
            }
        }
        let call_args: Vec<String> = (0..u.new_args.len()).map(|i| format!("a{i}")).collect();
        let new_fn = rust_name(&u.new_fn);
        out.push_str(&format!(
            "            let updated = self.{new_fn}(nodes, {});\n            return Some(crate::ast::update_node(nodes, updated, node, &mut self.hooks));\n        }}\n        None\n    }}\n\n",
            call_args.join(", ")
        ));
    }

    fn emit_clone_dispatch(&self, out: &mut String) {
        out.push_str("impl NodeFactory<'_> {\n");
        out.push_str(
            "    /// `(node *X) Clone(f)` — rebuilds `node` shallowly through the\n    /// matching `new_*` constructor and preserves flags/loc.\n    pub fn clone_node(&mut self, nodes: &mut Vec<Node>, node: NodeId) -> NodeId {\n        match nodes[node].kind {\n",
        );
        // group clone arms by kind
        for n in &self.schema.nodes {
            if n.custom.iter().any(|c| c == "clone") {
                // Hand-written clone (e.g. SourceFile::copyFrom semantics).
                if !n.kinds.is_empty() {
                    let kinds = n
                        .kinds
                        .iter()
                        .map(|k| format!("Kind::{k}"))
                        .collect::<Vec<_>>()
                        .join(" | ");
                    out.push_str(&format!(
                        "            {kinds} => crate::ast::clone_{}(self, nodes, node),\n",
                        rust_name(&n.name)
                    ));
                }
                continue;
            }
            if n.clone.is_empty() {
                continue;
            }
            if n.clone.len() == 1 && n.clone[0].kind.is_none() {
                let arm = &n.clone[0];
                let kinds = if n.kinds.is_empty() {
                    format!("Kind::{}", "Unknown")
                } else {
                    n.kinds
                        .iter()
                        .map(|k| format!("Kind::{k}"))
                        .collect::<Vec<_>>()
                        .join(" | ")
                };
                let call = self.clone_call(n, arm);
                out.push_str(&format!("            {kinds} => {call},\n"));
            } else {
                for arm in &n.clone {
                    let kind = arm.kind.clone().unwrap_or_else(|| "Unknown".into());
                    let call = self.clone_call(n, arm);
                    out.push_str(&format!("            Kind::{kind} => {call},\n"));
                }
            }
        }
        out.push_str(
            "            _ => panic!(\"Clone on node kind {:?}\", nodes[node].kind),\n        }\n    }\n}\n\n",
        );
    }

    fn clone_call(&self, n: &NodeDef, arm: &CloneArm) -> String {
        let m = rust_name(&n.name);
        // Reference-typed ctor args (`&str`, `&[NodeId]`, `&[String]`) need a
        // borrow of the cloned `String`/`Box<[T]>` temp.
        let ref_args: Vec<bool> = n
            .news
            .iter()
            .find(|c| c.name == arm.new_fn)
            .map(|c| {
                c.args
                    .iter()
                    .map(|a| {
                        matches!(
                            a.ty,
                            FieldType::Str | FieldType::NodeSlice | FieldType::StringSlice
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
        let mut args: Vec<String> = Vec::new();
        for (i, a) in arm.args.iter().enumerate() {
            match a.as_str() {
                "modifiers()" => args.push("nodes[node].modifiers().cloned()".into()),
                "kind" => args.push("nodes[node].kind".into()),
                "flags" => args.push("nodes[node].flags".into()),
                s if s.starts_with("field:") => {
                    if ref_args.get(i).copied().unwrap_or(false) {
                        args.push(format!("&t{i}"));
                    } else {
                        args.push(format!("t{i}"));
                    }
                }
                s if s.starts_with("expr:") => args.push(s["expr:".len()..].into()),
                _ => args.push(a.clone()),
            }
        }
        // field args need temps — wrap in a block
        let mut pre = String::new();
        for (i, a) in arm.args.iter().enumerate() {
            if let Some(f) = a.strip_prefix("field:") {
                let p = self.field_path(n, f);
                pre.push_str(&format!(
                    "let t{i} = nodes[node].as_{m}().{p}.clone();"
                ));
            }
        }
        let new_fn = rust_name(&arm.new_fn);
        if pre.is_empty() {
            format!("{{
                let updated = self.{new_fn}(nodes, {});
                crate::ast::clone_node(nodes, updated, node, &mut self.hooks)
            }}", args.join(", "))
        } else {
            format!("{{
                {pre}
                let updated = self.{new_fn}(nodes, {});
                crate::ast::clone_node(nodes, updated, node, &mut self.hooks)
            }}", args.join(", "))
        }
    }

    // ── visit_each_child ────────────────────────────────────────────────

    fn emit_visit_each_child(&self, out: &mut String) {
        out.push_str(
            "// ── `VisitEachChild` dispatch ─────────────────────────────────────\n\n/// `(node *X) VisitEachChild(v)` — `None` when the node was unchanged.\npub fn visit_each_child(\n    cx: &mut VisitorCx<'_>,\n    v: &NodeVisitor<'_>,\n    node: NodeId,\n) -> Option<NodeId> {\n    match cx.nodes[node].kind {\n",
        );
        for n in &self.schema.nodes {
            if n.custom.iter().any(|c| c == "visit_each_child") {
                continue;
            }
            let Some(u) = &n.update else {
                continue;
            };
            if n.visit_each_child.is_empty() {
                continue;
            }
            let kinds = n
                .kinds
                .iter()
                .map(|k| format!("Kind::{k}"))
                .collect::<Vec<_>>()
                .join(" | ");
            let m = rust_name(&n.name);
            out.push_str(&format!("        {kinds} => {{\n"));
            let mut argnames: Vec<String> = Vec::new();
            for (i, a) in n.visit_each_child.iter().enumerate() {
                let an = format!("a{i}");
                let stmt = match a.op.as_str() {
                    "visitNode" | "visitToken" | "visitEmbeddedStatement" | "visitIterationBody"
                    | "visitFunctionBody" => {
                        let p = self.field_path(n, a.field.as_deref().unwrap());
                        let hook = match a.op.as_str() {
                            "visitToken" => "visit_token_hooked",
                            "visitEmbeddedStatement" => "visit_embedded_statement_hooked",
                            "visitIterationBody" => "visit_iteration_body_hooked",
                            "visitFunctionBody" => "visit_function_body_hooked",
                            _ => "visit_node_hooked",
                        };
                        format!(
                            "            let {an} = v.{hook}(cx, cx.nodes[node].as_{m}().{p});\n"
                        )
                    }
                    "visitNodes" | "visitModifiers" | "visitParameters"
                    | "visitTopLevelStatements" => {
                        let p = self.field_path(n, a.field.as_deref().unwrap());
                        let hook = match a.op.as_str() {
                            "visitModifiers" => "visit_modifiers_hooked",
                            "visitParameters" => "visit_parameters_hooked",
                            "visitTopLevelStatements" => "visit_top_level_statements_hooked",
                            _ => "visit_nodes_hooked",
                        };
                        format!(
                            "            let {an} = v.{hook}(cx, cx.nodes[node].as_{m}().{p}.clone());\n"
                        )
                    }
                    "sameMap" => {
                        let p = self.field_path(n, a.field.as_deref().unwrap());
                        format!(
                            "            let orig_{an} = cx.nodes[node].as_{m}().{p}.clone();\n            let {an} = match v.visit_slice(cx, &orig_{an}) {{\n                Some(r) => r.into_boxed_slice(),\n                None => orig_{an},\n            }};\n"
                        )
                    }
                    "field" => {
                        let p = self.field_path(n, a.field.as_deref().unwrap());
                        format!(
                            "            let {an} = cx.nodes[node].as_{m}().{p}.clone();\n"
                        )
                    }
                    "kind" => format!("            let {an} = cx.nodes[node].kind;\n"),
                    "flags" => format!("            let {an} = cx.nodes[node].flags;\n"),
                    o => panic!("bad visit arg op {o}"),
                };
                out.push_str(&stmt);
                argnames.push(an);
            }
            // arg passing: slices pass by ref
            let call_args: Vec<String> = n
                .visit_each_child
                .iter()
                .enumerate()
                .map(|(i, a)| {
                    let an = &argnames[i];
                    // match update arg types: node_slice args take `&[NodeId]`
                    let ua = u.args.get(i);
                    match ua.map(|x| x.ty) {
                        Some(FieldType::NodeSlice) | Some(FieldType::StringSlice) => {
                            format!("&{an}")
                        }
                        _ => an.clone(),
                    }
                })
                .collect();
            let ufn = rust_name(&u.name);
            out.push_str(&format!(
                "            cx.factory.{ufn}(cx.nodes, node, {})\n        }},\n",
                call_args.join(", ")
            ));
        }
        // custom + unhandled
        for n in &self.schema.nodes {
            if !n.custom.iter().any(|c| c == "visit_each_child") {
                continue;
            }
            if n.kinds.is_empty() {
                continue;
            }
            let kinds = n
                .kinds
                .iter()
                .map(|k| format!("Kind::{k}"))
                .collect::<Vec<_>>()
                .join(" | ");
            out.push_str(&format!(
                "        {kinds} => crate::ast::visit_each_child_{}(cx, v, node),\n",
                rust_name(&n.name)
            ));
        }
        out.push_str("        _ => None,\n    }\n}\n\n");
    }

    // ── subtree-facts free helpers ──────────────────────────────────────

    fn emit_facts_helpers(&self, out: &mut String) {
        out.push_str(
            "// ── subtree-facts propagation helpers ───────────────────────────────\n\n/// `propagateSubtreeFacts(child)` — facts visible to the parent.\npub fn propagate_subtree_facts(nodes: &[Node], child: NodeId) -> SubtreeFacts {\n    let n = &nodes[child];\n    n.data.propagate_subtree_facts(n, nodes)\n}\n\n/// `propagateSubtreeFacts(child)` on an optional child.\npub fn propagate_subtree_facts_opt(nodes: &[Node], child: Option<NodeId>) -> SubtreeFacts {\n    match child {\n        Some(c) => propagate_subtree_facts(nodes, c),\n        None => SubtreeFacts::NONE,\n    }\n}\n\n/// `propagateNodeListSubtreeFacts(children, propagateSubtreeFacts)`.\npub fn propagate_node_list_subtree_facts(nodes: &[Node], children: &Option<NodeList>) -> SubtreeFacts {\n    let Some(list) = children else {\n        return SubtreeFacts::NONE;\n    };\n    let mut facts = SubtreeFacts::NONE;\n    for &c in list.nodes.iter() {\n        facts |= propagate_subtree_facts(nodes, c);\n    }\n    facts\n}\n\n/// `propagateNodeListSubtreeFacts` over a `Box<[NodeId]>`.\npub fn propagate_slice_subtree_facts(nodes: &[Node], children: &[NodeId]) -> SubtreeFacts {\n    let mut facts = SubtreeFacts::NONE;\n    for &c in children {\n        facts |= propagate_subtree_facts(nodes, c);\n    }\n    facts\n}\n\n/// `propagateModifierListSubtreeFacts(modifiers)`.\npub fn propagate_modifier_list_subtree_facts(nodes: &[Node], modifiers: &Option<ModifierList>) -> SubtreeFacts {\n    let Some(list) = modifiers else {\n        return SubtreeFacts::NONE;\n    };\n    let mut facts = SubtreeFacts::NONE;\n    for &c in list.nodes.iter() {\n        facts |= propagate_subtree_facts(nodes, c);\n    }\n    facts\n}\n\n/// `propagateEraseableSyntaxListSubtreeFacts(children)` — type arguments\n/// always contribute TypeScript.\npub fn propagate_eraseable_syntax_list_subtree_facts(children: &Option<NodeList>) -> SubtreeFacts {\n    if children.is_some() {\n        SubtreeFacts::CONTAINS_TYPE_SCRIPT\n    } else {\n        SubtreeFacts::NONE\n    }\n}\n",
        );
    }
}

/// `FirstJSDocNode` → `FIRST_JS_DOC_NODE`? No — kind consts use the
/// `const_name` scheme: strip Kind, SCREAM with _ before each uppercase.
/// `FirstJSDocNode` → `FIRST_J_S_DOC_NODE` is wrong; Go names range consts
/// like `KindFirstJSDocNode` → our const in kind_generated is
/// `FIRST_JSDOC_NODE` via emit_kinds::const_name — which uppercases each
/// char boundary: `FirstJSDocNode` → `FIRST_JSDOC_NODE`? — `JSDoc` has
/// internal boundaries — const_name inserts `_` before EVERY uppercase:
/// `FirstJSDocNode` → `F_I_R_S_T__J_S_DOC__NODE`... — actually
/// `FirstJSDocNode` chars: F,i,r,s,t,J,S,D,o,c... → `FIRST_J_S_DOC_NODE`.
/// So `Kind::FIRST_J_S_DOC_NODE`. Use the same scheme here.
fn const_like(name: &str) -> String {
    let mut out = String::new();
    for (i, c) in name.chars().enumerate() {
        if c.is_ascii_uppercase() && i > 0 {
            out.push('_');
        }
        out.push(c.to_ascii_uppercase());
    }
    out
}
