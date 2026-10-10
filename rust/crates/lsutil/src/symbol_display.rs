// Ported from tsc/internal/ls/lsutil/symbol_display.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.
//
// PORT(global): `*ast.Symbol` is `SymbolId` resolved through the owning
// `symbols: &RefCell<Vec<Symbol>>` arena (the crate-wide convention — for a
// checker this is `checker.symbol_arena`). `typeChecker *checker.Checker` is
// `Option<&mut Checker>` since several services methods are `&mut self`.
// `ast.IsDeprecatedDeclaration` is not ported in tsc-ast (jsdocCache), so the
// nil-checker fallback uses `tsc_checker::jsdoc::
// is_deprecated_declaration_with_cached_flags`, a line-for-line copy of the
// Go ast helper, with `nodes` mutable for lazy JSDoc resolution.

use std::cell::RefCell;

use tsc_ast::checkflags::CheckFlags;
use tsc_ast::{
    self as ast, FindAncestorResult, Kind, ModifierFlags, Node, NodeFlags, NodeId, Symbol,
    SymbolFlags, SymbolId,
};
use tsc_checker::checker_core::Checker;
use tsc_collections::Set;

/// `type ScriptElementKind int`
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(i32)]
pub enum ScriptElementKind {
    #[default]
    Unknown = 0,
    Warning = 1,
    /// predefined type (void) or keyword (class)
    Keyword = 2,
    /// top level script node
    ScriptElement = 3,
    /// module foo {}
    ModuleElement = 4,
    /// class X {}
    ClassElement = 5,
    /// var x = class X {}
    LocalClassElement = 6,
    /// interface Y {}
    InterfaceElement = 7,
    /// type T = ...
    TypeElement = 8,
    /// enum E {}
    EnumElement = 9,
    EnumMemberElement = 10,
    /// Inside module and script only.
    /// const v = ...
    VariableElement = 11,
    /// Inside function.
    LocalVariableElement = 12,
    /// using foo = ...
    VariableUsingElement = 13,
    /// await using foo = ...
    VariableAwaitUsingElement = 14,
    /// Inside module and script only.
    /// function f() {}
    FunctionElement = 15,
    /// Inside function.
    LocalFunctionElement = 16,
    /// class X { [public|private]* foo() {} }
    MemberFunctionElement = 17,
    /// class X { [public|private]* [get|set] foo:number; }
    MemberGetAccessorElement = 18,
    MemberSetAccessorElement = 19,
    /// class X { [public|private]* foo:number; }
    /// interface Y { foo:number; }
    MemberVariableElement = 20,
    /// class X { [public|private]* accessor foo: number; }
    MemberAccessorVariableElement = 21,
    /// class X { constructor() { } }
    /// class X { static { } }
    ConstructorImplementationElement = 22,
    /// interface Y { ():number; }
    CallSignatureElement = 23,
    /// interface Y { []:number; }
    IndexSignatureElement = 24,
    /// interface Y { new():Y; }
    ConstructSignatureElement = 25,
    /// function foo(*Y*: string)
    ParameterElement = 26,
    TypeParameterElement = 27,
    PrimitiveType = 28,
    Label = 29,
    Alias = 30,
    ConstElement = 31,
    LetElement = 32,
    Directory = 33,
    ExternalModuleName = 34,
    /// String literal
    String = 35,
    /// Jsdoc @link: in `{@link C link text}`, the before and after text "{@link " and "}"
    Link = 36,
    /// Jsdoc @link: in `{@link C link text}`, the entity name "C"
    LinkName = 37,
    /// Jsdoc @link: in `{@link C link text}`, the link text "link text"
    LinkText = 38,
}

/// `type ScriptElementKindModifier uint32` — bitmask newtype mirroring the
/// `flag_type!` flag API (`NONE`, `intersects`, `with`, `insert`, bit ops).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ScriptElementKindModifier(pub u32);

impl ScriptElementKindModifier {
    pub const NONE: Self = Self(0);
    pub const PUBLIC: Self = Self(1 << 1);
    pub const PRIVATE: Self = Self(1 << 2);
    pub const PROTECTED: Self = Self(1 << 3);
    pub const EXPORTED: Self = Self(1 << 4);
    pub const AMBIENT: Self = Self(1 << 5);
    pub const STATIC: Self = Self(1 << 6);
    pub const ABSTRACT: Self = Self(1 << 7);
    pub const OPTIONAL: Self = Self(1 << 8);
    pub const DEPRECATED: Self = Self(1 << 9);
    pub const DTS: Self = Self(1 << 10);
    pub const TS: Self = Self(1 << 11);
    pub const TSX: Self = Self(1 << 12);
    pub const JS: Self = Self(1 << 13);
    pub const JSX: Self = Self(1 << 14);
    pub const JSON: Self = Self(1 << 15);
    pub const DMTS: Self = Self(1 << 16);
    pub const MTS: Self = Self(1 << 17);
    pub const MJS: Self = Self(1 << 18);
    pub const DCTS: Self = Self(1 << 19);
    pub const CTS: Self = Self(1 << 20);
    pub const CJS: Self = Self(1 << 21);

    /// `self & flags != 0`
    #[inline]
    pub const fn intersects(self, flags: Self) -> bool {
        self.0 & flags.0 != 0
    }

    /// `self | flags`
    #[inline]
    pub const fn with(self, flags: Self) -> Self {
        Self(self.0 | flags.0)
    }

    /// `self | flags`
    #[inline]
    pub fn insert(&mut self, flags: Self) {
        self.0 |= flags.0;
    }
}

impl std::ops::BitOr for ScriptElementKindModifier {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for ScriptElementKindModifier {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl std::ops::BitAnd for ScriptElementKindModifier {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl std::ops::BitAndAssign for ScriptElementKindModifier {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl std::fmt::Debug for ScriptElementKindModifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ScriptElementKindModifier({:#x})", self.0)
    }
}

/// `scriptElementKindModifierNames` — (flag, name) pairs, in Go order.
const SCRIPT_ELEMENT_KIND_MODIFIER_NAMES: &[(ScriptElementKindModifier, &str)] = &[
    (ScriptElementKindModifier::PUBLIC, "public"),
    (ScriptElementKindModifier::PRIVATE, "private"),
    (ScriptElementKindModifier::PROTECTED, "protected"),
    (ScriptElementKindModifier::EXPORTED, "export"),
    (ScriptElementKindModifier::AMBIENT, "declare"),
    (ScriptElementKindModifier::STATIC, "static"),
    (ScriptElementKindModifier::ABSTRACT, "abstract"),
    (ScriptElementKindModifier::OPTIONAL, "optional"),
    (ScriptElementKindModifier::DEPRECATED, "deprecated"),
    (ScriptElementKindModifier::DTS, ".d.ts"),
    (ScriptElementKindModifier::TS, ".ts"),
    (ScriptElementKindModifier::TSX, ".tsx"),
    (ScriptElementKindModifier::JS, ".js"),
    (ScriptElementKindModifier::JSX, ".jsx"),
    (ScriptElementKindModifier::JSON, ".json"),
    (ScriptElementKindModifier::DMTS, ".d.mts"),
    (ScriptElementKindModifier::MTS, ".mts"),
    (ScriptElementKindModifier::MJS, ".mjs"),
    (ScriptElementKindModifier::DCTS, ".d.cts"),
    (ScriptElementKindModifier::CTS, ".cts"),
    (ScriptElementKindModifier::CJS, ".cjs"),
];

impl ScriptElementKindModifier {
    /// `(m ScriptElementKindModifier) Strings() collections.Set[string]`.
    pub fn strings(&self) -> Set<String> {
        let mut result = Set::new();
        for &(flag, name) in SCRIPT_ELEMENT_KIND_MODIFIER_NAMES {
            if self.intersects(flag) {
                result.add(name.to_string());
            }
        }
        result
    }
}

/// `FileExtensionKindModifiers`.
pub const FILE_EXTENSION_KIND_MODIFIERS: ScriptElementKindModifier =
    ScriptElementKindModifier(
        ScriptElementKindModifier::DTS.0
            | ScriptElementKindModifier::TS.0
            | ScriptElementKindModifier::TSX.0
            | ScriptElementKindModifier::JS.0
            | ScriptElementKindModifier::JSX.0
            | ScriptElementKindModifier::JSON.0
            | ScriptElementKindModifier::DMTS.0
            | ScriptElementKindModifier::MTS.0
            | ScriptElementKindModifier::MJS.0
            | ScriptElementKindModifier::DCTS.0
            | ScriptElementKindModifier::CTS.0
            | ScriptElementKindModifier::CJS.0,
    );

/// `symbol.CombinedLocalAndExportSymbolFlags()` — needs the symbol arena
/// because `export_symbol` is a `SymbolId`, not a pointer.
fn combined_local_and_export_symbol_flags(
    symbols: &RefCell<Vec<Symbol>>,
    s: SymbolId,
) -> SymbolFlags {
    let arena = symbols.borrow();
    let sym = &arena[s.index()];
    let mut flags = sym.flags;
    if let Some(export_symbol) = sym.export_symbol {
        flags |= arena[export_symbol.index()].flags;
    }
    flags
}

/// `GetSymbolKind`.
pub fn get_symbol_kind(
    type_checker: Option<&mut Checker>,
    symbol: SymbolId,
    location: NodeId,
    nodes: &[Node],
    symbols: &RefCell<Vec<Symbol>>,
) -> ScriptElementKind {
    let mut type_checker = type_checker;
    let result = get_symbol_kind_of_constructor_property_method_accessor_function_or_var(
        &mut type_checker,
        symbol,
        location,
        nodes,
        symbols,
    );
    if result != ScriptElementKind::Unknown {
        return result;
    }
    let flags = combined_local_and_export_symbol_flags(symbols, symbol);
    if flags.intersects(SymbolFlags::CLASS) {
        let decl = ast::get_declaration_of_kind(
            &symbols.borrow()[symbol.index()],
            Kind::ClassExpression,
            nodes,
        );
        if decl.is_some() {
            return ScriptElementKind::LocalClassElement;
        }
        return ScriptElementKind::ClassElement;
    }
    if flags.intersects(SymbolFlags::ENUM) {
        return ScriptElementKind::EnumElement;
    }
    if flags.intersects(SymbolFlags::TYPE_ALIAS) {
        return ScriptElementKind::TypeElement;
    }
    if flags.intersects(SymbolFlags::INTERFACE) {
        return ScriptElementKind::InterfaceElement;
    }
    if flags.intersects(SymbolFlags::TYPE_PARAMETER) {
        return ScriptElementKind::TypeParameterElement;
    }
    if flags.intersects(SymbolFlags::ENUM_MEMBER) {
        return ScriptElementKind::EnumMemberElement;
    }
    if flags.intersects(SymbolFlags::ALIAS) {
        return ScriptElementKind::Alias;
    }
    if flags.intersects(SymbolFlags::MODULE) {
        return ScriptElementKind::ModuleElement;
    }

    ScriptElementKind::Unknown
}

/// `getSymbolKindOfConstructorPropertyMethodAccessorFunctionOrVar`.
fn get_symbol_kind_of_constructor_property_method_accessor_function_or_var(
    type_checker: &mut Option<&mut Checker>,
    symbol: SymbolId,
    location: NodeId,
    nodes: &[Node],
    symbols: &RefCell<Vec<Symbol>>,
) -> ScriptElementKind {
    let roots: Vec<SymbolId> = match type_checker.as_deref_mut() {
        Some(tc) => tc.get_root_symbols(symbol),
        None => vec![symbol],
    };

    // If this is a method from a mapped type, leave as a method so long as it
    // still has a call signature, as opposed to e.g.
    // `{ [K in keyof I]: number }`.
    if roots.len() == 1
        && symbols.borrow()[roots[0].index()]
            .flags
            .intersects(SymbolFlags::METHOD)
        && match type_checker.as_deref_mut() {
            Some(tc) => {
                let t = tc.get_type_of_symbol_at_location(symbol, Some(location));
                let t = tc.get_non_nullable_type(t);
                !tc.get_call_signatures(t).is_empty()
            }
            None => true,
        }
    {
        return ScriptElementKind::MemberFunctionElement;
    }

    if let Some(tc) = type_checker.as_deref_mut() {
        if tc.is_undefined_symbol(Some(symbol)) {
            return ScriptElementKind::VariableElement;
        }
        if tc.is_arguments_symbol(Some(symbol)) {
            return ScriptElementKind::LocalVariableElement;
        }
        if (nodes[location].kind == Kind::ThisKeyword
            && ast::is_expression(&nodes[location], nodes))
            || ast::is_this_in_type_query(location, nodes)
        {
            return ScriptElementKind::ParameterElement;
        }
    }

    let flags = combined_local_and_export_symbol_flags(symbols, symbol);
    let (check_flags, declarations, value_declaration, parent) = {
        let arena = symbols.borrow();
        let sym = &arena[symbol.index()];
        (
            sym.check_flags,
            sym.declarations.clone(),
            sym.value_declaration,
            sym.parent,
        )
    };

    if flags.intersects(SymbolFlags::VARIABLE) {
        if is_first_declaration_of_symbol_parameter(&declarations, nodes) {
            return ScriptElementKind::ParameterElement;
        } else if value_declaration.is_some_and(|vd| ast::is_var_const(vd, nodes)) {
            return ScriptElementKind::ConstElement;
        } else if value_declaration.is_some_and(|vd| ast::is_var_using(vd, nodes)) {
            return ScriptElementKind::VariableUsingElement;
        } else if value_declaration.is_some_and(|vd| ast::is_var_await_using(vd, nodes)) {
            return ScriptElementKind::VariableAwaitUsingElement;
        } else if declarations.iter().any(|&d| ast::is_let(d, nodes)) {
            return ScriptElementKind::LetElement;
        }
        if is_local_variable_or_function(&declarations, parent, nodes) {
            return ScriptElementKind::LocalVariableElement;
        }
        return ScriptElementKind::VariableElement;
    }
    if flags.intersects(SymbolFlags::FUNCTION) {
        if is_local_variable_or_function(&declarations, parent, nodes) {
            return ScriptElementKind::LocalFunctionElement;
        }
        return ScriptElementKind::FunctionElement;
    }
    // FIXME: getter and setter use the same symbol. And it is rare to use only
    // setter without getter, so in most cases the symbol always has getter
    // flag. So, even when the location is just on the declaration of setter,
    // this function returns getter.
    if flags.intersects(SymbolFlags::GET_ACCESSOR) {
        return ScriptElementKind::MemberGetAccessorElement;
    }
    if flags.intersects(SymbolFlags::SET_ACCESSOR) {
        return ScriptElementKind::MemberSetAccessorElement;
    }
    if flags.intersects(SymbolFlags::METHOD) {
        return ScriptElementKind::MemberFunctionElement;
    }
    if flags.intersects(SymbolFlags::CONSTRUCTOR) {
        return ScriptElementKind::ConstructorImplementationElement;
    }
    if flags.intersects(SymbolFlags::SIGNATURE) {
        return ScriptElementKind::IndexSignatureElement;
    }

    if flags.intersects(SymbolFlags::PROPERTY) {
        if type_checker.is_some()
            && flags.intersects(SymbolFlags::TRANSIENT)
            && check_flags.intersects(CheckFlags::SYNTHETIC)
        {
            // If union property is result of union of non method
            // (property/accessors/variables), it is labeled as property
            let mut union_property_kind = ScriptElementKind::Unknown;
            for &root_symbol in &roots {
                if symbols.borrow()[root_symbol.index()]
                    .flags
                    .intersects(SymbolFlags::PROPERTY_OR_ACCESSOR | SymbolFlags::VARIABLE)
                {
                    union_property_kind = ScriptElementKind::MemberVariableElement;
                    break;
                }
            }
            if union_property_kind == ScriptElementKind::Unknown {
                // If this was union of all methods, make sure it has call
                // signatures before we can label it as method.
                let tc = type_checker.as_deref_mut().unwrap();
                let type_of_union_property =
                    tc.get_type_of_symbol_at_location(symbol, Some(location));
                if !tc.get_call_signatures(type_of_union_property).is_empty() {
                    return ScriptElementKind::MemberFunctionElement;
                }
                return ScriptElementKind::MemberVariableElement;
            }
            return union_property_kind;
        }

        return ScriptElementKind::MemberVariableElement;
    }

    ScriptElementKind::Unknown
}

/// `isFirstDeclarationOfSymbolParameter`.
fn is_first_declaration_of_symbol_parameter(
    declarations: &[NodeId],
    nodes: &[Node],
) -> bool {
    let declaration = declarations.first().copied();
    let result = ast::find_ancestor_or_quit(declaration, nodes, &mut |n, _nodes| {
        if ast::is_parameter_declaration(n) {
            return FindAncestorResult::True;
        }
        if ast::is_binding_element(n)
            || ast::is_object_binding_pattern(n)
            || ast::is_array_binding_pattern(n)
        {
            return FindAncestorResult::False;
        }
        FindAncestorResult::Quit
    });

    result.is_some()
}

/// `isLocalVariableOrFunction`.
fn is_local_variable_or_function(
    declarations: &[NodeId],
    parent_symbol: Option<SymbolId>,
    nodes: &[Node],
) -> bool {
    if parent_symbol.is_some() {
        return false; // This is exported symbol
    }

    for &decl in declarations {
        // Function expressions are local
        if nodes[decl].kind == Kind::FunctionExpression {
            return true;
        }

        if nodes[decl].kind != Kind::VariableDeclaration
            && nodes[decl].kind != Kind::FunctionDeclaration
        {
            continue;
        }

        // If the parent is not source file or module block, it is a local
        // variable.
        let mut parent = nodes[decl].parent;
        while !ast::is_function_block(parent, nodes) {
            let p = parent.expect("nil parent in isLocalVariableOrFunction");
            // Reached source file or module block
            if nodes[p].kind == Kind::SourceFile || nodes[p].kind == Kind::ModuleBlock {
                break;
            }
            parent = nodes[p].parent;
        }

        if ast::is_function_block(parent, nodes) {
            // Parent is in function block.
            return true;
        }
    }
    false
}

/// `GetSymbolModifiers`.
pub fn get_symbol_modifiers(
    type_checker: Option<&mut Checker>,
    symbol: Option<SymbolId>,
    nodes: &mut Vec<Node>,
    symbols: &RefCell<Vec<Symbol>>,
) -> ScriptElementKindModifier {
    let Some(symbol) = symbol else {
        return ScriptElementKindModifier::NONE;
    };
    let mut type_checker = type_checker;

    let mut modifiers =
        get_normalized_symbol_modifiers(&mut type_checker, symbol, nodes, symbols);
    if symbols.borrow()[symbol.index()]
        .flags
        .intersects(SymbolFlags::ALIAS)
        && type_checker.is_some()
    {
        let resolved_symbol = type_checker
            .as_deref_mut()
            .unwrap()
            .get_aliased_symbol(symbol);
        if resolved_symbol != Some(symbol) {
            // Go passes the (never-nil in practice) resolved symbol straight
            // through; a nil would panic on `symbol.Declarations`.
            let resolved =
                resolved_symbol.expect("nil resolved symbol in GetSymbolModifiers");
            modifiers |=
                get_normalized_symbol_modifiers(&mut type_checker, resolved, nodes, symbols);
        }
    }
    if symbols.borrow()[symbol.index()]
        .flags
        .intersects(SymbolFlags::OPTIONAL)
    {
        modifiers |= ScriptElementKindModifier::OPTIONAL;
    }

    modifiers
}

/// `getNormalizedSymbolModifiers`.
fn get_normalized_symbol_modifiers(
    type_checker: &mut Option<&mut Checker>,
    symbol: SymbolId,
    nodes: &mut Vec<Node>,
    symbols: &RefCell<Vec<Symbol>>,
) -> ScriptElementKindModifier {
    let mut modifier_set = ScriptElementKindModifier::NONE;
    let declarations = symbols.borrow()[symbol.index()].declarations.clone();
    if !declarations.is_empty() {
        let declaration = declarations[0];
        let rest = &declarations[1..];
        // omit deprecated flag if some declarations are not deprecated
        let exclude_flags: ModifierFlags;
        if rest.len() > 0
            && is_deprecated_declaration(type_checker, declaration, nodes)
            // !!! include jsdoc node flags
            && rest.iter().any(|&d| {
                !is_deprecated_declaration(type_checker, d, nodes)
            })
        {
            exclude_flags = ModifierFlags::DEPRECATED;
        } else {
            exclude_flags = ModifierFlags::NONE;
        }
        modifier_set =
            get_node_modifiers(type_checker, declaration, exclude_flags, nodes);
    }

    modifier_set
}

/// `isDeprecatedDeclaration`.
fn is_deprecated_declaration(
    type_checker: &mut Option<&mut Checker>,
    declaration: NodeId,
    nodes: &mut Vec<Node>,
) -> bool {
    match type_checker.as_deref_mut() {
        Some(tc) => tc.is_deprecated_declaration(declaration),
        // PORT: `ast.IsDeprecatedDeclaration` is deferred in tsc-ast; the
        // checker's `jsdoc` module carries a line-for-line port of
        // `IsDeprecatedDeclarationWithCachedFlags`, which is exactly the ast
        // semantics with `GetCombinedNodeFlags` supplied.
        None => tsc_checker::jsdoc::is_deprecated_declaration_with_cached_flags(
            nodes,
            declaration,
            ast::get_combined_node_flags(declaration, nodes),
        ),
    }
}

/// `getNodeModifiers`.
fn get_node_modifiers(
    type_checker: &mut Option<&mut Checker>,
    node: NodeId,
    exclude_flags: ModifierFlags,
    nodes: &mut Vec<Node>,
) -> ScriptElementKindModifier {
    let mut result = ScriptElementKindModifier::NONE;
    let mut flags = ModifierFlags::NONE;
    if ast::is_declaration(&nodes[node]) {
        flags = ast::get_combined_modifier_flags(node, nodes);
        if is_deprecated_declaration(type_checker, node, nodes) {
            flags |= ModifierFlags::DEPRECATED;
        }
        flags &= !exclude_flags;
    }

    if flags.intersects(ModifierFlags::PRIVATE) {
        result |= ScriptElementKindModifier::PRIVATE;
    }
    if flags.intersects(ModifierFlags::PROTECTED) {
        result |= ScriptElementKindModifier::PROTECTED;
    }
    if flags.intersects(ModifierFlags::PUBLIC) {
        result |= ScriptElementKindModifier::PUBLIC;
    }
    if flags.intersects(ModifierFlags::STATIC) {
        result |= ScriptElementKindModifier::STATIC;
    }
    if flags.intersects(ModifierFlags::ABSTRACT) {
        result |= ScriptElementKindModifier::ABSTRACT;
    }
    if flags.intersects(ModifierFlags::EXPORT) {
        result |= ScriptElementKindModifier::EXPORTED;
    }
    if flags.intersects(ModifierFlags::DEPRECATED) {
        result |= ScriptElementKindModifier::DEPRECATED;
    }
    if flags.intersects(ModifierFlags::AMBIENT) {
        result |= ScriptElementKindModifier::AMBIENT;
    }
    if nodes[node].flags.intersects(NodeFlags::AMBIENT) {
        result |= ScriptElementKindModifier::AMBIENT;
    }
    if nodes[node].kind == Kind::ExportAssignment {
        result |= ScriptElementKindModifier::EXPORTED;
    }

    result
}
