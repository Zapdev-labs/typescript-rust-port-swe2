// gen-ast schema model — the in-memory form of `kinds.toml`.
//
// `kinds.toml` is the authored schema: it is bootstrapped once from
// tsc/internal/ast/{kind_generated.go, ast_generated.go, ast.go} and then
// becomes the sole input for `gen-ast generate`.

/// A field of a node or base struct.
#[derive(Debug, Clone)]
pub struct Field {
    /// Go field name, e.g. `Expression` (or `StatementBase` for embeds).
    pub go_name: String,
    /// Rust field name (snake_case), e.g. `expression`.
    pub name: String,
    /// Type tag: see `FieldType`.
    pub ty: FieldType,
    /// Target base name when `ty == FieldType::Embed`.
    pub embed: Option<String>,
    /// `// Optional` in Go — informational for `*Node` fields (they are
    /// `Option<NodeId>` regardless), and the `Option` marker for other
    /// pointer types.
    pub optional: bool,
    /// `false` when the Go field is unexported (e.g. `name`, `modifiers`).
    pub exported: bool,
    /// Rust type override for `ty == FieldType::Other` (SourceFile fields).
    pub rust_ty: Option<String>,
}

/// Type tags for `Field::ty`. These map Go types to Rust types in emit.rs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldType {
    /// Embedded base struct (Go type embedding). `embed` holds the base name.
    Embed,
    /// `*Node` and its aliases → `Option<NodeId>`
    Node,
    /// `*NodeList` / `*XxxList` aliases → `Option<NodeList>`
    NodeList,
    /// `*ModifierList` → `Option<ModifierList>`
    ModifierList,
    /// `[]*Node` → `Box<[NodeId]>`
    NodeSlice,
    /// `[]string` → `Box<[String]>`
    StringSlice,
    /// `string` → `String`
    Str,
    /// `bool` → `bool`
    Bool,
    /// `int` / `int32` → `i32`
    Int,
    /// `Kind` and `*SyntaxKind` aliases → `Kind`
    Kind,
    /// `TokenFlags` → `TokenFlags`
    TokenFlags,
    /// `NodeFlags` → `NodeFlags` (ctor/update args only)
    NodeFlags,
    /// `*Symbol` → `Option<SymbolId>`
    Symbol,
    /// `SymbolTable` → `SymbolTable`
    SymbolTable,
    /// `*FlowNode` → `Option<FlowNodeId>`
    FlowNode,
    /// `*FlowList` → `Option<FlowNodeId>` — unused; kept for FlowList.
    FlowList,
    /// `atomic.Uint32` → `std::sync::atomic::AtomicU32`
    AtomicU32,
    /// `any` → `Option<u64>` placeholder for the checker type object
    Any,
    /// SourceFile-only payload types kept verbatim (`tspath.RootedFilePath`,
    /// `core.LanguageVariant`, ...) — emitted via `rust_ty`.
    Other,
}

/// A base struct (`*Base` types in ast_generated.go).
#[derive(Debug, Clone)]
pub struct BaseDef {
    pub name: String,
    pub fields: Vec<Field>,
}

/// `new` constructor entry (a `func (f *NodeFactory) NewX ...`).
#[derive(Debug, Clone)]
pub struct CtorDef {
    /// Go name, e.g. `NewIfStatement`.
    pub name: String,
    /// How the node's `kind` is determined: `Some(kind_name)` = fixed
    /// `Kind::<name>`; `None` = taken from an argument named `kind`.
    pub kind: Option<String>,
    /// Name of the constructor parameter carrying the kind (usually `kind`).
    pub kind_arg: Option<String>,
    /// Constructor args, in order.
    pub args: Vec<CtorArg>,
    /// Extra statements after `newNode`, e.g. `node.Flags = flags`.
    pub post: Vec<CtorPost>,
    /// `f.textCount++` present.
    pub counts_text: bool,
    /// `f.identifierCount++` present.
    pub counts_identifier: bool,
}

#[derive(Debug, Clone)]
pub struct CtorArg {
    pub name: String,
    pub ty: FieldType,
    /// Data field this arg initializes, when it is stored directly.
    pub field: Option<String>,
    /// Init expression override (e.g. masked flags) — a mini-AST:
    /// `mask:TokenFlagsStringLiteralFlags` means `arg & MASK`.
    pub init_mask: Option<String>,
    /// The Go argument type, preserved for `*SyntaxKind` aliases so the
    /// node's kind list can be resolved from `[[kind_aliases]]`.
    pub go_ty: String,
}

#[derive(Debug, Clone)]
pub enum CtorPost {
    /// `node.Flags = <arg>` — VariableDeclarationList.
    SetFlags { arg: String },
    /// `node.Flags |= <arg> & NodeFlagsOptionalChain` — optional chaining.
    OrOptionalChain { arg: String },
}

/// `update` method (`func (f *NodeFactory) UpdateX(node *X, ...) *Node`).
#[derive(Debug, Clone)]
pub struct UpdateDef {
    pub name: String,
    /// Args in signature order; types mirror ctor args.
    pub args: Vec<UpdateArg>,
    /// Compare expressions joined by `||` in the rebuild `if`.
    pub compares: Vec<UpdateCompare>,
    /// The `NewX` callee used to rebuild.
    pub new_fn: String,
    /// Sources for the rebuild call's args, in order. Each is `arg:<name>`
    /// (an update arg) or `node.<Expr>` (e.g. `node.Kind`).
    pub new_args: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct UpdateArg {
    pub name: String,
    pub ty: FieldType,
}

#[derive(Debug, Clone)]
pub struct UpdateCompare {
    /// Arg name or `node.<Expr>` LHS.
    pub lhs: String,
    /// Field name on the node (or `Flags` for the outer node flags).
    pub field: String,
    /// `neq` (`lhs != node.field`) or `same` (`!core.Same(lhs, node.field)`).
    pub op: String,
}

/// One step of a `forEachChild` body, in order.
#[derive(Debug, Clone)]
pub struct VisitOp {
    /// `visit` | `visitNodes` | `visitNodeList` | `visitModifiers`
    pub op: String,
    /// Field name (resolved through bases at emit time).
    pub field: String,
}

/// One step of a `visitEachChild` arg list.
#[derive(Debug, Clone)]
pub struct VisitArg {
    /// `visitNode` | `visitToken` | `visitNodes` | `visitModifiers` |
    /// `visitEmbeddedStatement` | `visitIterationBody` | `visitParameters` |
    /// `visitFunctionBody` | `visitTopLevelStatements` | `sameMap` |
    /// `field` (passthrough `node.X`) | `kind` (passthrough `node.Kind`) |
    /// `flags` (passthrough `node.Flags`)
    pub op: String,
    /// Field name for ops that take one.
    pub field: Option<String>,
}

/// A clone arm: `cloneNode(f.NewX(args...), ...)`.
#[derive(Debug, Clone)]
pub struct CloneArm {
    /// `Some(kind)` when inside a `switch node.Kind` arm.
    pub kind: Option<String>,
    pub new_fn: String,
    /// Arg sources: `field:<name>`, `modifiers()`, `kind`.
    pub args: Vec<String>,
}

/// One operand of a generated `computeSubtreeFacts` chain.
#[derive(Debug, Clone)]
pub struct FactOp {
    /// `propagate` | `propagateList` | `propagateModifierList` | `const`
    pub op: String,
    /// Field name for propagate ops; const name for `const`.
    pub field: Option<String>,
    /// Const name for `op == "const"`.
    pub value: Option<String>,
}

/// A node struct (`type X struct` in ast_generated.go plus the three
/// hand-written payloads: SourceFile, FlowSwitchClauseData, FlowReduceLabelData).
#[derive(Debug, Clone)]
pub struct NodeDef {
    /// Go struct name.
    pub name: String,
    /// Override for the emitted Rust struct name (e.g. `SourceFile` →
    /// `SourceFileData` to avoid colliding with the container).
    pub rust_name: Option<String>,
    /// Kinds that produce this data variant. From `newNode(KindX, ...)` args
    /// or the `Is<Name>` switch for kind-parameterized constructors.
    pub kinds: Vec<String>,
    /// Directly embedded bases, in order.
    pub bases: Vec<String>,
    /// Own (non-embedded) fields, in order.
    pub fields: Vec<Field>,
    /// Constructors.
    pub news: Vec<CtorDef>,
    /// Update method, if any.
    pub update: Option<UpdateDef>,
    /// `forEachChild` steps; empty = leaf (or custom).
    pub for_each_child: Vec<VisitOp>,
    /// `visitEachChild` arg steps.
    pub visit_each_child: Vec<VisitArg>,
    /// Clone arms.
    pub clone: Vec<CloneArm>,
    /// `computeSubtreeFacts` chain; `None` = none emitted (facts == NONE or
    /// custom/`typescript` via `facts_mode`).
    pub facts: Vec<FactOp>,
    /// `generated` | `custom` | `typescript` | `none`
    pub facts_mode: String,
    /// `default` | `typescript` | `custom` | `exclusions`
    pub propagate_mode: String,
    /// `SubtreeExclusionsX` name when `propagate_mode == "exclusions"`.
    pub propagate_exclusions: Option<String>,
    /// Extra `| propagateSubtreeFacts(node.F)` terms (Method/Property name).
    pub propagate_fields: Vec<String>,
    /// `is` predicate name (`IsIfStatement` → emitted as `is_if_statement`).
    pub is_fn: Option<String>,
    /// Methods implemented by hand outside the generated file:
    /// `for_each_child` | `visit_each_child` | `clone` | `compute` | `propagate`.
    pub custom: Vec<String>,
    /// True for `SourceFile`, `FlowSwitchClauseData`, `FlowReduceLabelData` —
    /// hand-authored payloads that live in the data enum.
    pub extra: bool,
}

/// A `IsXKind` kind predicate (tail of ast_generated.go) or a node-level
/// `IsX(node)` predicate recorded in `node_preds`.
#[derive(Debug, Clone)]
pub struct KindPred {
    pub name: String,
    /// `Some([first, last])` for `kind >= X && kind <= Y` bodies.
    pub range: Option<[String; 2]>,
    /// Case list otherwise.
    pub kinds: Vec<String>,
    /// `Some(pred)` when the body delegates, e.g. `return IsXKind(node.Kind)`.
    pub delegate: Option<String>,
}

/// `KindFirstX = KindY` const aliases from kind_generated.go.
#[derive(Debug, Clone)]
pub struct KindConst {
    pub name: String,
    pub value: String,
}

/// `type XSyntaxKind = Kind` aliases.
#[derive(Debug, Clone)]
pub struct KindAlias {
    pub name: String,
    /// Kind names (without `Kind`) listed in the alias's doc comment —
    /// the authoritative kind set for the alias.
    pub kinds: Vec<String>,
}

/// Root schema.
#[derive(Debug, Default)]
pub struct Schema {
    /// `Kind` names without the `Kind` prefix, in ordinal order.
    pub kinds: Vec<String>,
    pub kind_consts: Vec<KindConst>,
    pub kind_aliases: Vec<KindAlias>,
    pub kind_preds: Vec<KindPred>,
    /// `IsX(node)` predicates that don't map 1:1 onto a node struct.
    pub node_preds: Vec<KindPred>,
    pub bases: Vec<BaseDef>,
    pub nodes: Vec<NodeDef>,
}

impl Schema {
    pub fn base_map(&self) -> std::collections::BTreeMap<&str, &BaseDef> {
        self.bases.iter().map(|b| (b.name.as_str(), b)).collect()
    }

    /// Whether `bases` transitively embeds `target` (e.g. `TypeSyntaxBase`).
    pub fn has_base(&self, bases: &[String], target: &str) -> bool {
        let map = self.base_map();
        let mut stack: Vec<&str> = bases.iter().map(|s| s.as_str()).collect();
        let mut seen = std::collections::BTreeSet::new();
        while let Some(b) = stack.pop() {
            if b == target {
                return true;
            }
            if !seen.insert(b) {
                continue;
            }
            if let Some(def) = map.get(b) {
                for f in &def.fields {
                    if f.ty == FieldType::Embed
                        && let Some(e) = &f.embed
                    {
                        stack.push(e);
                    }
                }
            }
        }
        false
    }
}
