// Ported from tsc/internal/ls/autoimport/export.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `*ast.Symbol` → `SymbolId` + the checker-global symbol arena; `*ast.Node` →
// `NodeId` + per-file `Vec<Node>` arenas reached through the checker's
// `program_nodes` accessors.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::symbol::{INTERNAL_SYMBOL_NAME_DEFAULT, INTERNAL_SYMBOL_NAME_EXPORT_EQUALS};
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::{NodeId, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_lsutil::symbol_display::{ScriptElementKind, ScriptElementKindModifier};
use tsc_tspath::{ModuleSpecifier, PathKey, RootedFilePath};

use crate::autoimport::index::Named;
use crate::autoimport::util::try_get_module_id_and_file_name_of_module_symbol;

/// `type moduleIDKind uint8`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub(crate) enum ModuleIdKind {
    /// `moduleIDKindInvalid`.
    #[default]
    Invalid = 0,
    /// `moduleIDKindFile`.
    File,
    /// `moduleIDKindAmbient`.
    Ambient,
}

/// `type ModuleID struct` — uniquely identifies either a file module or an
/// ambient module.
#[derive(Clone, Default, PartialEq, Eq, Hash, Debug)]
pub struct ModuleID {
    pub(crate) path: PathKey,
    pub(crate) specifier: ModuleSpecifier,
    pub(crate) kind: ModuleIdKind,
}

/// `fileModuleID`.
pub(crate) fn file_module_id(path: PathKey) -> ModuleID {
    ModuleID {
        path,
        kind: ModuleIdKind::File,
        ..Default::default()
    }
}

/// `ambientModuleID`.
pub(crate) fn ambient_module_id(specifier: &str) -> ModuleID {
    ModuleID {
        specifier: tsc_tspath::to_module_specifier(specifier),
        kind: ModuleIdKind::Ambient,
        ..Default::default()
    }
}

impl ModuleID {
    /// `ModuleID.AsString`.
    pub fn as_string(&self) -> &str {
        match self.kind {
            ModuleIdKind::File => self.path.as_string(),
            ModuleIdKind::Ambient => self.specifier.as_string(),
            _ => "",
        }
    }

    /// `ModuleID.IsAmbient`.
    pub fn is_ambient(&self) -> bool {
        self.kind == ModuleIdKind::Ambient
    }

    /// `ModuleID.AsPathKey` — `(path, ok)` becomes `Option`.
    pub fn as_path_key(&self) -> Option<&PathKey> {
        if self.kind != ModuleIdKind::File {
            return None;
        }
        Some(&self.path)
    }

    /// `ModuleID.AsModuleSpecifier` — `(specifier, ok)` becomes `Option`.
    pub fn as_module_specifier(&self) -> Option<&ModuleSpecifier> {
        if self.kind != ModuleIdKind::Ambient {
            return None;
        }
        Some(&self.specifier)
    }
}

/// `type ExportID struct`.
#[derive(Clone, Default, PartialEq, Eq, Hash, Debug)]
pub struct ExportID {
    /// `ModuleID`.
    pub module_id: ModuleID,
    /// `ExportName`.
    pub export_name: String,
}

/// `type ExportSyntax int`.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(i32)]
pub enum ExportSyntax {
    /// `ExportSyntaxNone`.
    #[default]
    None = 0,
    /// `ExportSyntaxModifier` — `export const x = {}`.
    Modifier,
    /// `ExportSyntaxNamed` — `export { x }`.
    Named,
    /// `ExportSyntaxDefaultModifier` — `export default function f() {}`.
    DefaultModifier,
    /// `ExportSyntaxDefaultDeclaration` — `export default f`.
    DefaultDeclaration,
    /// `ExportSyntaxEquals` — `export = x`.
    Equals,
    /// `ExportSyntaxUMD` — `export as namespace x`.
    Umd,
    /// `ExportSyntaxStar` — `export * from "module"`.
    Star,
    /// `ExportSyntaxCommonJSModuleExports` — `module.exports = {}`.
    CommonJSModuleExports,
    /// `ExportSyntaxCommonJSExportsProperty` — `exports.x = {}`.
    CommonJSExportsProperty,
}

/// `type Export struct`.
#[derive(Clone, Default, Debug)]
pub struct Export {
    /// `ExportID` — Go embeds it; field access flattens to `export_id.*`.
    pub export_id: ExportID,
    /// `ModuleFileName`.
    pub module_file_name: RootedFilePath,
    /// `UnresolvedModuleSpecifier`.
    pub unresolved_module_specifier: ModuleSpecifier,
    /// `Syntax`.
    pub syntax: ExportSyntax,
    /// `Flags`.
    pub flags: SymbolFlags,
    /// `localName`.
    pub(crate) local_name: String,
    /// `through` is the name of the module symbol's export that this export
    /// was found on, either 'export=', `InternalSymbolNameExportStar`, or "".
    pub(crate) through: String,

    // Checker-set fields
    /// `Target`.
    pub target: ExportID,
    /// `IsTypeOnly`.
    pub is_type_only: bool,
    /// `ScriptElementKind`.
    pub script_element_kind: ScriptElementKind,
    /// `ScriptElementKindModifiers`.
    pub script_element_kind_modifiers: ScriptElementKindModifier,

    /// `Path` — the file where the export was found.
    pub path: PathKey,
    /// `PackageName`.
    pub package_name: String,
}

impl Export {
    /// `Export.Name`.
    pub fn name(&self) -> &str {
        if !self.local_name.is_empty() {
            return &self.local_name;
        }
        if self.export_id.export_name == INTERNAL_SYMBOL_NAME_EXPORT_EQUALS {
            return &self.target.export_name;
        }
        &self.export_id.export_name
    }

    /// `Export.IsRenameable`.
    pub fn is_renameable(&self) -> bool {
        self.export_id.export_name == INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
            || self.export_id.export_name == INTERNAL_SYMBOL_NAME_DEFAULT
    }

    /// `Export.AmbientModuleName`.
    pub fn ambient_module_name(&self) -> &str {
        if self.export_id.module_id.is_ambient() {
            return self.export_id.module_id.as_string();
        }
        ""
    }

    /// `Export.IsUnresolvedAlias`.
    pub fn is_unresolved_alias(&self) -> bool {
        self.flags == SymbolFlags::ALIAS
    }
}

impl Named for Export {
    fn name(&self) -> &str {
        Export::name(self)
    }
}

/// `SymbolToExport`.
pub fn symbol_to_export(symbol: SymbolId, ch: &Rc<RefCell<Checker>>) -> Option<Rc<Export>> {
    let symbol_arena = ch.borrow().symbol_arena.clone();
    let parent = symbol_arena.get_ref(symbol).parent;
    if let Some(parent) = parent
        && tsc_checker::utilities::is_external_module_symbol(parent, &ch.borrow())
    {
        let (module_id, module_file_name) =
            try_get_module_id_and_file_name_of_module_symbol(parent, ch)?;
        let file = crate::autoimport::util::get_source_file_of_module(parent, ch)?;
        return extract_first_export(symbol, ch, &module_id, &module_file_name, file);
    }

    let declaration = {
        let sa = symbol_arena.clone();
        sa[symbol.index()].declarations.first().copied()
    }?;
    let file = {
        let c = ch.borrow();
        let nodes = c.program_nodes(declaration);
        tsc_ast::get_source_file_of_node(Some(declaration), &nodes)
    }?;
    let file_symbol = {
        let c = ch.borrow();
        let nodes = c.program_nodes(file);
        nodes[file].as_source_file().declaration_base.symbol
    }?;

    let module_symbol = ch.borrow_mut().get_merged_symbol(file_symbol);
    let module_id = file_module_id({
        let c = ch.borrow();
        let nodes = c.program_nodes(file);
        nodes[file].as_source_file().path_key().clone()
    });
    let module_file_name = {
        let c = ch.borrow();
        let nodes = c.program_nodes(file);
        nodes[file].as_source_file().file_name().clone()
    };
    let target = {
        let mut c = ch.borrow_mut();
        let skipped = c.skip_alias(symbol)?;
        c.get_merged_symbol(skipped)
    };

    for export_name in [
        INTERNAL_SYMBOL_NAME_DEFAULT,
        INTERNAL_SYMBOL_NAME_EXPORT_EQUALS,
    ] {
        if let Some(export) = try_get_module_export(
            export_name,
            target,
            module_symbol,
            ch,
            &module_id,
            &module_file_name,
            file,
        ) {
            return Some(export);
        }
    }
    let symbol_name = symbol_arena.get_ref(symbol).name.clone();
    try_get_module_export(
        &symbol_name,
        target,
        module_symbol,
        ch,
        &module_id,
        &module_file_name,
        file,
    )
}

/// `tryGetModuleExport`.
fn try_get_module_export(
    export_name: &str,
    target: SymbolId,
    module_symbol: SymbolId,
    ch: &Rc<RefCell<Checker>>,
    module_id: &ModuleID,
    module_file_name: &RootedFilePath,
    file: NodeId,
) -> Option<Rc<Export>> {
    let exported = ch
        .borrow_mut()
        .try_get_member_in_module_exports_and_properties(export_name, module_symbol)?;
    let same = {
        let mut c = ch.borrow_mut();
        match c.skip_alias(exported) {
            Some(skipped) => c.get_merged_symbol(skipped) == target,
            None => false,
        }
    };
    if same {
        return extract_first_export(exported, ch, module_id, module_file_name, file);
    }
    None
}

/// `extractFirstExport`.
fn extract_first_export(
    symbol: SymbolId,
    ch: &Rc<RefCell<Checker>>,
    module_id: &ModuleID,
    module_file_name: &RootedFilePath,
    file: NodeId,
) -> Option<Rc<Export>> {
    let symbol_name = {
        let sa = ch.borrow().symbol_arena.clone();
        let sa = sa.clone();
        sa[symbol.index()].name.clone()
    };
    let mut exports: Vec<Rc<Export>> = Vec::new();
    let extractor = crate::autoimport::extract::SymbolExtractor::new(
        String::new(),
        ch.clone(),
        tsc_tspath::CaseSensitivity::CaseInsensitive,
        None,
    );
    extractor.extract_from_symbol(
        &symbol_name,
        symbol,
        module_id,
        module_file_name,
        file,
        &mut exports,
    );
    exports.into_iter().next()
}
