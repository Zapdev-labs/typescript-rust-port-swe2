# Porting notes — `moduletransforms`

Ported from `tsc/internal/transformers/moduletransforms` at Go commit
`ec47d33c23e464a17cdf2475632cba629bee8763`:

| Go file | Rust file | Go LOC | Rust LOC |
| --- | --- | --- | --- |
| `commonjsmodule.go` | `commonjsmodule.rs` | 2166 | ~4030 |
| `externalmoduleinfo.go` | `externalmoduleinfo.rs` | 389 | ~650 |
| `esmodule.go` | `esmodule.rs` | 372 | ~750 |
| `utilities.go` | `utilities.rs` | 118 | ~225 |
| `impliedmodule.go` | `impliedmodule.rs` | 53 | ~100 |

Every `(tx *XxxTransformer) method` and package-level `func` in the Go
sources has a Rust counterpart; each Rust function carries a `///`-comment
naming the Go function it ports.

## Structural mapping (shared with `estransforms`)

- Go transformer structs embed `*transformers.Transformer` so visit methods
  can reach `tx.Visitor()`, `tx.Factory()`, and `tx.EmitContext()`. Rust
  cannot capture the `Transformer` being built inside its own visit
  closure, so:
  - transform state lives in an `Rc<State>` captured by the visit closure;
  - the emit context is shared as `Rc<RefCell<EmitContext>>` (`Ec`);
  - the running `NodeVisitor` arrives as the visit callback's `v` argument;
  - `tx.Factory()` maps to `ec.borrow_mut().factory` (the `fac()` helper in
    `commonjsmodule.rs` keeps those borrows one-statement tight).
- A `RefCell<EmitContext>` borrow never spans a visitor call: nested visits
  re-enter the state and would panic on a second borrow. All
  `borrow()`/`borrow_mut()` scopes are single statements or tight blocks.
- `update_*` factory methods return `Option<NodeId>` (`None` = unchanged);
  call sites use `.unwrap_or(node)` where Go returned the input pointer.
- `Option<NodeList>` fields are cloned into `Vec<NodeId>` before mutation
  or owned iteration; `NodeList` is `Clone`, not `Copy`.

## CommonJS sibling visitors

Go builds `topLevelVisitor`, `topLevelNestedVisitor`,
`discardedValueVisitor`, and `assignmentPatternVisitor` with
`emitContext.NewNodeVisitor` inside `NewCommonJSModuleTransformer`. In Rust
they are stored in `CjsVisitors` on the state `Rc`; each closure re-enters
the state through a `Weak` (`self_ref`) so the visitors can live on the
state itself. `tx.Visitor()` resolves to `visitors.main`, a `NodeVisitor`
with the same visit function and emit-context hooks as the real
transformer visitor, so behavior is identical.

`tx.pushNode`/`tx.popNode` ancestor tracking maps to `push_node()` +
`PopGuard` (RAII `Drop`), replacing Go `defer`s.

## `TransformOptions::symbols`

Go resolvers reach symbols through `*ast.Symbol` pointers; the Rust
`ReferenceResolver` trait surfaces `&mut Vec<Symbol>` parameters instead,
so `TransformOptions` gained a
`pub symbols: Option<&'a RefCell<Vec<Symbol>>>` field carrying the
binder-owned symbol arena. Callers wiring `TransformOptions` must populate
it (together with `resolver`, `emit_resolver`, and
`get_emit_module_format_of_file`) for the module transforms.

## `ImpliedModuleTransformer`

Go lazily allocates `tx.cjsTransformer`/`tx.esmTransformer` on first use
and reuses them across files. Rust mirrors this with
`RefCell<Option<Transformer>>` fields on the state struct. The transform
constructors (`new_implied_module_transformer`,
`new_common_js_module_transformer`, `new_es_module_transformer`) are `pub`
and match the `TransformerFactory` signature
(`Fn(&TransformOptions) -> Option<Transformer>`), ready to be inserted into
`chain(...)`.

## Deliberate omissions / deferred items

- **PORT(deferred): chain wiring.** Nothing in the Rust workspace yet calls
  the module transforms: Go wires `NewImpliedModuleTransformer` (and the
  direct CJS/ES constructors) from the emit pipeline, which is not yet
  ported. The constructors are exposed and factory-shaped; integration is
  deferred to the emit/driver port.
- **`getExternalModuleNameLiteral` host/resolver arguments.** Go itself
  passes `nil /*host*/` and `nil /*resolver*/` at every call site; the Rust
  signature keeps the parameters (`Option<&dyn EmitHost>`,
  `Option<&Rc<RefCell<dyn EmitResolver>>>`) for parity and future callers.
- **`tryGetModuleNameFromFile`, `tryRenameExternalModule`,
  `getExternalModuleNameFromPath`.** These are unimplemented in Go (marked
  `// !!!`); the Rust versions preserve the no-op stubs and comments.
- **`helperNameSubstitutions`** is declared but never used in `esmodule.go`
  — omitted.
- **`getExternalModuleNameLiteral` `// !!! propagate token flags`** is
  preserved verbatim from Go (upstream acknowledges it produces diffs).

## RefCell-safety invariants

- `fac()` and every explicit `ec.borrow*()` scope never enclose a
  `visit_*`/`ec_visit_iteration_body` call.
- The `flatten_destructuring_assignment` callback captures the state `Rc`
  and `Ec` clone; `vis`/`adapter` are declared before `callback` so drop
  order (reverse declaration order) is sound.
