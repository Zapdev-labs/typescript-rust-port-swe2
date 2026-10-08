// Ported from tsc/internal/ast/symbol.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Symbol shell. Symbols are stored in a `Vec<Symbol>` owned by the binder;
// references use `SymbolId`. `SymbolTable` is an insertion-ordered map
// (`tsc_collections::OrderedMap`), preserving the deterministic iteration
// order the Go port relies on via `collections.OrderedMap`.

use crate::checkflags::CheckFlags;
use crate::ids::{NodeId, SymbolId};
use crate::symbolflags::SymbolFlags;
use crate::{ModifierFlags, is_private_identifier_class_element_declaration};
use tsc_collections::OrderedMap;

// Symbol

#[derive(Default)]
pub struct Symbol {
    pub flags: SymbolFlags,
    /// Non-zero only in transient symbols created by Checker
    pub check_flags: CheckFlags,
    pub name: String,
    pub declarations: Vec<NodeId>,
    pub value_declaration: Option<NodeId>,
    pub members: SymbolTable,
    pub exports: SymbolTable,
    // Go stores a lazily-assigned `id atomic.Uint64`; the slot index in the
    // owning `Vec<Symbol>` is the id in this port.
    pub parent: Option<SymbolId>,
    pub export_symbol: Option<SymbolId>,
}

impl Symbol {
    pub fn is_external_module(&self) -> bool {
        self.flags.intersects(SymbolFlags::MODULE) && is_ambient_module_symbol_name(&self.name)
    }
}

/// Ported from `(s *Symbol).IsStatic`. Needs the node arena to inspect the
/// value declaration's modifier flags.
pub fn symbol_is_static(s: &Symbol, nodes: &[crate::Node]) -> bool {
    let Some(value_declaration) = s.value_declaration else {
        return false;
    };
    let node = &nodes[value_declaration.local_index() as usize];
    node.modifier_flags(nodes).intersects(ModifierFlags::STATIC)
}

// SymbolTable

/// `SymbolTable` is an ordered map from name to `SymbolId`, mirroring
/// `map[string]*Symbol` while keeping deterministic insertion order.
pub type SymbolTable = OrderedMap<String, SymbolId>;

/// Invalid UTF8 sequence, will never occur as IdentifierName.
pub const INTERNAL_SYMBOL_NAME_PREFIX: &str = "\u{FE}";

pub const INTERNAL_SYMBOL_NAME_CALL: &str = "\u{FE}call"; // Call signatures
pub const INTERNAL_SYMBOL_NAME_CONSTRUCTOR: &str = "\u{FE}constructor"; // Constructor implementations
pub const INTERNAL_SYMBOL_NAME_NEW: &str = "\u{FE}new"; // Constructor signatures
pub const INTERNAL_SYMBOL_NAME_INDEX: &str = "\u{FE}index"; // Index signatures
pub const INTERNAL_SYMBOL_NAME_EXPORT_STAR: &str = "\u{FE}export"; // Module export * declarations
pub const INTERNAL_SYMBOL_NAME_GLOBAL: &str = "\u{FE}global"; // Global self-reference
pub const INTERNAL_SYMBOL_NAME_MISSING: &str = "\u{FE}missing"; // Indicates missing symbol
pub const INTERNAL_SYMBOL_NAME_TYPE: &str = "\u{FE}type"; // Anonymous type literal symbol
pub const INTERNAL_SYMBOL_NAME_OBJECT: &str = "\u{FE}object"; // Anonymous object literal declaration
pub const INTERNAL_SYMBOL_NAME_JSX_ATTRIBUTES: &str = "\u{FE}jsxAttributes"; // Anonymous JSX attributes object literal declaration
pub const INTERNAL_SYMBOL_NAME_CLASS: &str = "\u{FE}class"; // Unnamed class expression
pub const INTERNAL_SYMBOL_NAME_FUNCTION: &str = "\u{FE}function"; // Unnamed function expression
pub const INTERNAL_SYMBOL_NAME_COMPUTED: &str = "\u{FE}computed"; // Computed property name declaration with dynamic name
pub const INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION: &str = "\u{FE}assignment"; // Assignment declarations
pub const INTERNAL_SYMBOL_NAME_INSTANTIATION_EXPRESSION: &str = "\u{FE}instantiationExpression"; // Instantiation expressions
pub const INTERNAL_SYMBOL_NAME_IMPORT_ATTRIBUTES: &str = "\u{FE}importAttributes";
/// Export assignment symbol
pub const INTERNAL_SYMBOL_NAME_EXPORT_EQUALS: &str = "export=";
/// Default export symbol (technically not wholly internal, but included here for usability)
pub const INTERNAL_SYMBOL_NAME_DEFAULT: &str = "default";
pub const INTERNAL_SYMBOL_NAME_THIS: &str = "this";
pub const INTERNAL_SYMBOL_NAME_MODULE_EXPORTS: &str = "module.exports";

/// Ported from `SymbolName`.
pub fn symbol_name<'a>(symbol: &'a Symbol, nodes: &'a [crate::Node]) -> std::borrow::Cow<'a, str> {
    if let Some(value_declaration) = symbol.value_declaration
        && is_private_identifier_class_element_declaration(
            &nodes[value_declaration.local_index() as usize],
        )
        && let Some(name) = nodes[value_declaration.local_index() as usize].name()
    {
        return nodes[name.local_index() as usize].text(nodes);
    }
    std::borrow::Cow::Borrowed(symbol.name.as_str())
}

/// `EscapeAllInternalSymbolNames` replaces internal symbol name markers ("\xFE") with "__".
pub fn escape_all_internal_symbol_names(name: &str) -> String {
    name.replace(INTERNAL_SYMBOL_NAME_PREFIX, "__")
}

/// `EscapeInternalSymbolName` escapes a single leading internal marker.
pub fn escape_internal_symbol_name(name: &str) -> std::borrow::Cow<'_, str> {
    if let Some(rest) = name.strip_prefix(INTERNAL_SYMBOL_NAME_PREFIX) {
        return std::borrow::Cow::Owned(format!("__{rest}"));
    }
    std::borrow::Cow::Borrowed(name)
}

/// `EscapeSymbolName` converts a binder symbol name into its escaped "__String"
/// form. Internal names (prefixed with the "\xFE" sentinel) become "__"-prefixed,
/// and user names that already begin with "__" gain an extra leading underscore
/// so they can be distinguished from internal names.
pub fn escape_symbol_name(name: &str) -> std::borrow::Cow<'_, str> {
    if let Some(rest) = name.strip_prefix(INTERNAL_SYMBOL_NAME_PREFIX) {
        return std::borrow::Cow::Owned(format!("__{rest}"));
    }
    if name.starts_with("__") {
        return std::borrow::Cow::Owned(format!("_{name}"));
    }
    std::borrow::Cow::Borrowed(name)
}

/// `IsAmbientModuleSymbolName` reports whether `s` names an ambient module
/// symbol. Ambient module symbols are either of the form `"modulename"` or
/// `InternalSymbolNamePrefix + "\"modulename\"pattern@nodeId"`; see
/// `getDeclarationName` in the Go binder.
pub fn is_ambient_module_symbol_name(s: &str) -> bool {
    try_get_ambient_module_name_from_symbol_name(s).is_some()
}

/// Ported from `TryGetAmbientModuleNameFromSymbolName` in utilities.go. Kept
/// here because symbol.go is its only caller within the `ast` layer.
pub fn try_get_ambient_module_name_from_symbol_name(s: &str) -> Option<String> {
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return Some(s[1..s.len() - 1].to_string());
    }

    let pattern_prefix = format!("{INTERNAL_SYMBOL_NAME_PREFIX}\"");
    let rest = s.strip_prefix(&pattern_prefix)?;
    let marker_index = rest.rfind("\"pattern@")?;
    if marker_index < 1 {
        return None;
    }
    Some(rest[..marker_index].to_string())
}
