// M2 gate test (SPEC §M2): `ast_generated` accessor coverage — factory
// construction, `as_*`/`is_*` accessors, and `update_*` no-change semantics.
use crate::ast::{NodeFactory, NodeFactoryHooks};
use crate::kind_generated::Kind;

#[test]
fn generated_accessors_and_updates() {
    let mut nodes = Vec::new();
    let mut f = NodeFactory::new(NodeFactoryHooks::default());

    let ident = f.new_identifier(&mut nodes, "x");
    assert_eq!(nodes[ident].kind, Kind::Identifier);
    assert_eq!(nodes[ident].as_identifier().text, "x");
    assert!(crate::ast_generated::is_identifier(&nodes[ident]));

    // Accessor on the wrong variant panics, matching Go's AsX on wrong kind.
    let tok = f.new_token(&mut nodes, Kind::PlusToken);
    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = nodes[tok].as_identifier();
    }));
    assert!(panicked.is_err());

    // update_*: unchanged inputs → None (Go returns the same pointer);
    // changed inputs → Some(new id) with the field updated.
    let qn = f.new_qualified_name(&mut nodes, Some(ident), Some(ident));
    assert_eq!(nodes[qn].kind, Kind::QualifiedName);
    assert!(f.update_qualified_name(&mut nodes, qn, Some(ident), Some(ident)).is_none());
    let updated = f
        .update_qualified_name(&mut nodes, qn, None, Some(ident))
        .expect("changed update must produce a node");
    assert!(nodes[updated].as_qualified_name().left.is_none());
    assert_eq!(nodes[updated].as_qualified_name().right, Some(ident));
}
