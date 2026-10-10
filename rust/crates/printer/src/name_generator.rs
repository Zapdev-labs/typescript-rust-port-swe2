// Ported from tsc/internal/printer/namegenerator.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Generates unique names for generated identifiers.
//
// PORT: Go's `NameGenerator` holds two callbacks into the owning `Printer`
// (`GetTextOfNode`, `IsFileLevelUniqueNameInCurrentFile`) and the two recurse
// into each other (`getTextOfNode` calls `GenerateName`). Rust cannot express
// that back-reference without `Rc<RefCell<>>` gymnastics, so the generator's
// state lives in this `NameGenerator` struct (a field on `Printer`) while the
// methods themselves are `impl Printer` below — the recursion then flows
// through `&mut self` naturally. `use_file_level_check` replaces the `checkFn`
// callback parameter, whose only values were `nil` or
// `IsFileLevelUniqueNameInCurrentFile`.

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, Kind, Node, NodeId, Symbol};
use tsc_collections::Set;

use crate::emit_context::{AutoGenerateId, Shared, get_node_for_generated_name_worker};
use tsc_core::options_generated::ScriptTarget;
use tsc_scanner::scanner;

use crate::emit_flags::{EmitFlags, GeneratedIdentifierFlags};
use crate::factory::format_generated_name;
use crate::printer::Printer;
use crate::utilities::{
    self as util, GET_LITERAL_TEXT_FLAGS_ALLOW_NUMERIC_SEPARATOR,
    GET_LITERAL_TEXT_FLAGS_JSX_ATTRIBUTE_ESCAPE, GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE,
    GET_LITERAL_TEXT_FLAGS_NONE, GetLiteralTextFlags, QuoteChar, ensure_leading_hash,
    make_identifier_from_module_name, remove_leading_hash,
};

/// `type tempFlags int` — flags enum to track count of temp variables and a
/// few dedicated names.
pub(crate) type TempFlags = i32;

/// `tempFlagsAuto` — No preferred name
pub(crate) const TEMP_FLAGS_AUTO: TempFlags = 0x00000000;
/// `tempFlagsCountMask` — Temp variable counter
pub(crate) const TEMP_FLAGS_COUNT_MASK: TempFlags = 0x0FFFFFFF;
/// `tempFlags_i` — Use/preference flag for '_i'
pub(crate) const TEMP_FLAGS_I: TempFlags = 0x10000000;

/// `type nameGenerationScope struct` — `next` is implicit: the scope stack is
/// a `Vec` and each scope's `next` is the entry at `index - 1`.
#[derive(Default)]
pub(crate) struct NameGenerationScope {
    /// TempFlags for the current name generation scope.
    pub(crate) temp_flags: TempFlags,
    /// TempFlags for the current name generation scope.
    pub(crate) formatted_name_temp_flags: FxHashMap<String, TempFlags>,
    /// Names reserved in nested name generation scopes.
    pub(crate) reserved_names: Set<String>,
    // NOTE: generated names should be scoped after Strada port is complete.
    // generated_names: Set<String>,
}

/// `type NameGenerator struct` — the mutable state; methods live on
/// `Printer`.
#[derive(Default)]
pub struct NameGenerator {
    /// `Context *EmitContext` — the emit-context tables.
    pub(crate) shared: Shared,
    /// Map of generated names for specific nodes
    pub(crate) node_id_to_generated_name: FxHashMap<NodeId, String>,
    /// Map of generated private names for specific nodes
    pub(crate) node_id_to_generated_private_name: FxHashMap<NodeId, String>,
    /// Map of generated names for temp and loop variables
    pub(crate) auto_generated_id_to_generated_name: FxHashMap<AutoGenerateId, String>,
    pub(crate) name_generation_scope: Vec<NameGenerationScope>,
    pub(crate) private_name_generation_scope: Vec<NameGenerationScope>,
    /// NOTE: Used to match Strada, but should be moved to
    /// name_generation_scope after port is complete.
    pub(crate) generated_names: Set<String>,
}

impl NameGenerator {
    /// `getScope`
    fn scope(&self, private_name: bool) -> &Vec<NameGenerationScope> {
        if private_name {
            &self.private_name_generation_scope
        } else {
            &self.name_generation_scope
        }
    }

    fn scope_mut(&mut self, private_name: bool) -> &mut Vec<NameGenerationScope> {
        if private_name {
            &mut self.private_name_generation_scope
        } else {
            &mut self.name_generation_scope
        }
    }

    /// `getTempFlags`
    fn get_temp_flags(&self, private_name: bool) -> TempFlags {
        match self.scope(private_name).last() {
            Some(scope) => scope.temp_flags,
            None => TEMP_FLAGS_AUTO,
        }
    }

    /// `setTempFlags`
    fn set_temp_flags(&mut self, private_name: bool, flags: TempFlags) {
        let scope = self.scope_mut(private_name);
        if scope.is_empty() {
            scope.push(NameGenerationScope::default());
        }
        scope.last_mut().unwrap().temp_flags = flags;
    }

    /// `getTempFlagsForFormattedName` — gets the TempFlags to use in the
    /// current nameGenerationScope for the given key.
    fn get_temp_flags_for_formatted_name(
        &self,
        private_name: bool,
        formatted_name_key: &str,
    ) -> TempFlags {
        match self.scope(private_name).last() {
            Some(scope) => scope
                .formatted_name_temp_flags
                .get(formatted_name_key)
                .copied()
                .unwrap_or(TEMP_FLAGS_AUTO),
            None => TEMP_FLAGS_AUTO,
        }
    }

    /// `setTempFlagsForFormattedName` — sets the TempFlags to use in the
    /// current nameGenerationScope for the given key.
    fn set_temp_flags_for_formatted_name(
        &mut self,
        private_name: bool,
        formatted_name_key: String,
        flags: TempFlags,
    ) {
        let scope = self.scope_mut(private_name);
        if scope.is_empty() {
            scope.push(NameGenerationScope::default());
        }
        scope
            .last_mut()
            .unwrap()
            .formatted_name_temp_flags
            .insert(formatted_name_key, flags);
    }

    /// `reserveName`
    fn reserve_name(&mut self, name: String, private_name: bool, scoped: bool, temp: bool) {
        {
            let scope = self.scope_mut(private_name);
            if scope.is_empty() {
                scope.push(NameGenerationScope::default());
            }
            if private_name || scoped {
                scope.last_mut().unwrap().reserved_names.add(name);
                return;
            }
        }
        if !temp {
            self.generated_names.add(name); // NOTE: Matches Strada, but is incorrect.
            // (*scope).generated_names.add(name) // TODO: generated names should be scoped after Strada port is complete.
        }
    }

    /// `isReservedName`
    fn is_reserved_name(&self, name: &str, private_name: bool) -> bool {
        // NOTE: The following matches Strada, but is incorrect.
        if self.generated_names.has(name) {
            return true;
        }

        // TODO: generated names should be scoped after Strada port is complete.
        ////if scope != nil {
        ////    if scope.generatedNames.Has(name) {
        ////        return true
        ////    }
        ////}

        for scope in self.scope(private_name).iter().rev() {
            if scope.reserved_names.has(name) {
                return true;
            }
        }
        false
    }

    // `isReservedName` check half of `isUniqueName` — see
    // `Printer::is_unique_name`.
}

/// `nextContainer`
fn next_container(nodes: &[Node], node: NodeId) -> Option<NodeId> {
    nodes[node]
        .locals_container_data()
        .map(|d| d.next_container)
        .flatten()
}

/// `isUniqueLocalName`
fn is_unique_local_name(name: &str, container: NodeId, nodes: &[Node], symbols: &[Symbol]) -> bool {
    let mut node = Some(container);
    while let Some(n) = node
        && ast::is_node_descendant_of(Some(n), Some(container), nodes)
        && nodes[n].locals_container_data().is_some()
    {
        if let Some(locals) = nodes[n].locals()
            // We conservatively include alias symbols to cover cases where they're emitted as locals
            && let Some(local) = locals.get(name)
            && symbols[local.index()].flags.0
                & (ast::SymbolFlags::VALUE.0
                    | ast::SymbolFlags::EXPORT_VALUE.0
                    | ast::SymbolFlags::ALIAS.0)
                != 0
        {
            return false;
        }
        node = next_container(nodes, n);
    }
    true
}

impl<'a> Printer<'a> {
    /// `(g *NameGenerator) PushScope`
    pub(crate) fn push_scope(&mut self, reuse_temp_variable_scope: bool) {
        self.name_generator
            .private_name_generation_scope
            .push(NameGenerationScope::default());
        if !reuse_temp_variable_scope {
            self.name_generator
                .name_generation_scope
                .push(NameGenerationScope::default());
        }
    }

    /// `(g *NameGenerator) PopScope`
    pub(crate) fn pop_scope(&mut self, reuse_temp_variable_scope: bool) {
        self.name_generator.private_name_generation_scope.pop();
        if !reuse_temp_variable_scope {
            self.name_generator.name_generation_scope.pop();
        }
    }

    /// `GenerateName` — generate the text for a generated identifier or
    /// private identifier.
    pub(crate) fn generate_name_text(&mut self, name: NodeId) -> String {
        let auto_generate = self
            .emit_context
            .shared()
            .borrow()
            .auto_generate
            .get(&name)
            .cloned();
        if let Some(auto_generate) = auto_generate {
            if auto_generate.flags.is_node() {
                // Node names generate unique names based on their original node
                // and are cached based on that node's id.
                let node = get_node_for_generated_name_worker(
                    &self.emit_context.shared(),
                    self.nodes,
                    auto_generate.node.unwrap_or(name),
                    auto_generate.id,
                );
                return self.generate_name_for_node_cached(
                    node,
                    ast::is_private_identifier(&self.nodes[name]),
                    auto_generate.flags,
                    &auto_generate.prefix,
                    &auto_generate.suffix,
                );
            } else {
                // Auto, Loop, and Unique names are cached based on their unique autoGenerateId.
                if let Some(auto_generated_name) = self
                    .name_generator
                    .auto_generated_id_to_generated_name
                    .get(&auto_generate.id)
                {
                    return auto_generated_name.clone();
                }
                let auto_generated_name = self.make_name(name);
                self.name_generator
                    .auto_generated_id_to_generated_name
                    .insert(auto_generate.id, auto_generated_name.clone());
                return auto_generated_name;
            }
        }
        self.get_text_of_node(name, false)
    }

    /// `generateNameForNodeCached`
    fn generate_name_for_node_cached(
        &mut self,
        node: NodeId,
        private_name: bool,
        flags: GeneratedIdentifierFlags,
        prefix: &str,
        suffix: &str,
    ) -> String {
        let node_id = ast::get_node_id(&self.nodes[node]);
        {
            let cache = if private_name {
                &self.name_generator.node_id_to_generated_private_name
            } else {
                &self.name_generator.node_id_to_generated_name
            };
            if let Some(name) = cache.get(&node_id) {
                return name.clone();
            }
        }

        let name = self.generate_name_for_node(node, private_name, flags, prefix, suffix);
        let cache = if private_name {
            &mut self.name_generator.node_id_to_generated_private_name
        } else {
            &mut self.name_generator.node_id_to_generated_name
        };
        cache.insert(node_id, name.clone());
        name
    }

    /// `generateNameForNode`
    fn generate_name_for_node(
        &mut self,
        node: NodeId,
        private_name: bool,
        flags: GeneratedIdentifierFlags,
        prefix: &str,
        suffix: &str,
    ) -> String {
        match self.nodes[node].kind {
            Kind::Identifier | Kind::PrivateIdentifier => {
                let text = self.get_text_of_node(node, false);
                self.make_unique_name(
                    &text,
                    false, /*checkFn*/
                    flags.is_optimistic(),
                    flags.is_reserved_in_nested_scopes(),
                    private_name,
                    prefix,
                    suffix,
                )
            }
            Kind::ModuleDeclaration | Kind::EnumDeclaration => {
                if private_name || !prefix.is_empty() || !suffix.is_empty() {
                    panic!(
                        "Generated name for a module or enum cannot be private and may have neither a prefix nor suffix"
                    )
                }
                self.generate_name_for_module_or_enum(node)
            }
            Kind::ImportDeclaration | Kind::JSImportDeclaration | Kind::ExportDeclaration => {
                if private_name || !prefix.is_empty() || !suffix.is_empty() {
                    panic!(
                        "Generated name for an import or export cannot be private and may have neither a prefix nor suffix"
                    )
                }
                self.generate_name_for_import_or_export_declaration(node)
            }
            Kind::FunctionDeclaration | Kind::ClassDeclaration => {
                if private_name || !prefix.is_empty() || !suffix.is_empty() {
                    panic!(
                        "Generated name for a class or function declaration cannot be private and may have neither a prefix nor suffix"
                    )
                }
                let name = self.nodes[node].name();
                // PORT: Go's condition is
                // `name != nil && !(g.Context == nil && g.Context.HasAutoGenerateInfo(name))`.
                // Since `g.Context` is never nil here the `&&` right-hand side
                // is always false, making the guard effectively `name != nil`;
                // preserved as such.
                if let Some(name) = name {
                    return self.generate_name_for_node(
                        name, false, /*privateName*/
                        flags, "", /*prefix*/
                        "", /*suffix*/
                    );
                }
                self.generate_name_for_export_default()
            }
            Kind::ExportAssignment => {
                if private_name || !prefix.is_empty() || !suffix.is_empty() {
                    panic!(
                        "Generated name for an export assignment cannot be private and may have neither a prefix nor suffix"
                    )
                }
                self.generate_name_for_export_default()
            }
            Kind::ClassExpression => {
                if private_name || !prefix.is_empty() || !suffix.is_empty() {
                    panic!(
                        "Generated name for a class expression cannot be private and may have neither a prefix nor suffix"
                    )
                }
                self.generate_name_for_class_expression()
            }
            Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor => {
                self.generate_name_for_method_or_accessor(node, private_name, prefix, suffix)
            }
            Kind::ComputedPropertyName => self.make_temp_variable_name(
                TEMP_FLAGS_AUTO,
                true, /*reservedInNestedScopes*/
                private_name,
                prefix,
                suffix,
            ),
            _ => self.make_temp_variable_name(
                TEMP_FLAGS_AUTO,
                false, /*reservedInNestedScopes*/
                private_name,
                prefix,
                suffix,
            ),
        }
    }

    /// `generateNameForModuleOrEnum`
    fn generate_name_for_module_or_enum(&mut self, node: NodeId) -> String {
        let name = self.nodes[node]
            .name()
            .map(|n| self.get_text_of_node(n, false))
            .unwrap_or_default();
        // Use module/enum name itself if it is unique, otherwise make a unique variation
        if is_unique_local_name(&name, node, self.nodes, self.symbols) {
            name
        } else {
            self.make_unique_name(
                &name, false, /*checkFn*/
                false, /*optimistic*/
                false, /*scoped*/
                false, /*privateName*/
                "",    /*prefix*/
                "",    /*suffix*/
            )
        }
    }

    /// `generateNameForImportOrExportDeclaration`
    fn generate_name_for_import_or_export_declaration(&mut self, node: NodeId) -> String {
        let expr = ast::get_external_module_name(&self.nodes[node], self.nodes);
        let mut base_name = "module".to_string();
        if let Some(expr) = expr
            && ast::is_string_literal(&self.nodes[expr])
        {
            base_name = make_identifier_from_module_name(&self.nodes[expr].text(self.nodes));
        }
        self.make_unique_name(
            &base_name, false, /*checkFn*/
            false, /*optimistic*/
            false, /*scoped*/
            false, /*privateName*/
            "",    /*prefix*/
            "",    /*suffix*/
        )
    }

    /// `generateNameForExportDefault`
    fn generate_name_for_export_default(&mut self) -> String {
        self.make_unique_name(
            "default", false, /*checkFn*/
            false, /*optimistic*/
            false, /*scoped*/
            false, /*privateName*/
            "",    /*prefix*/
            "",    /*suffix*/
        )
    }

    /// `generateNameForClassExpression`
    fn generate_name_for_class_expression(&mut self) -> String {
        self.make_unique_name(
            "class", false, /*checkFn*/
            false, /*optimistic*/
            false, /*scoped*/
            false, /*privateName*/
            "",    /*prefix*/
            "",    /*suffix*/
        )
    }

    /// `generateNameForMethodOrAccessor`
    fn generate_name_for_method_or_accessor(
        &mut self,
        node: NodeId,
        private_name: bool,
        prefix: &str,
        suffix: &str,
    ) -> String {
        if let Some(name) = self.nodes[node].name()
            && ast::is_identifier(&self.nodes[name])
        {
            return self.generate_name_for_node_cached(
                name,
                private_name,
                GeneratedIdentifierFlags::NONE,
                prefix,
                suffix,
            );
        }
        self.make_temp_variable_name(
            TEMP_FLAGS_AUTO,
            false, /*reservedInNestedScopes*/
            private_name,
            prefix,
            suffix,
        )
    }

    /// `makeName`
    fn make_name(&mut self, name: NodeId) -> String {
        let auto_generate = self
            .emit_context
            .shared()
            .borrow()
            .auto_generate
            .get(&name)
            .cloned();
        if let Some(auto_generate) = auto_generate {
            match auto_generate.flags.kind() {
                f if f == GeneratedIdentifierFlags::AUTO => {
                    return self.make_temp_variable_name(
                        TEMP_FLAGS_AUTO,
                        auto_generate.flags.is_reserved_in_nested_scopes(),
                        ast::is_private_identifier(&self.nodes[name]),
                        &auto_generate.prefix,
                        &auto_generate.suffix,
                    );
                }
                f if f == GeneratedIdentifierFlags::LOOP => {
                    assert!(ast::is_identifier(&self.nodes[name]));
                    return self.make_temp_variable_name(
                        TEMP_FLAGS_I,
                        auto_generate.flags.is_reserved_in_nested_scopes(),
                        false, /*privateName*/
                        &auto_generate.prefix,
                        &auto_generate.suffix,
                    );
                }
                f if f == GeneratedIdentifierFlags::UNIQUE => {
                    let name_text = self.nodes[name].text(self.nodes).into_owned();
                    return self.make_unique_name(
                        &name_text,
                        auto_generate.flags.is_file_level(), /*checkFn*/
                        auto_generate.flags.is_optimistic(),
                        auto_generate.flags.is_reserved_in_nested_scopes(),
                        ast::is_private_identifier(&self.nodes[name]),
                        &auto_generate.prefix,
                        &auto_generate.suffix,
                    );
                }
                _ => {}
            }
        }
        self.get_text_of_node(name, false)
    }

    /// `makeTempVariableName` — return the next available name in the pattern
    /// _a ... _z, _0, _1, ...
    /// TempFlags._i may be used to express a preference for that dedicated
    /// name.
    /// Note that names generated by makeTempVariableName and makeUniqueName
    /// will never conflict.
    fn make_temp_variable_name(
        &mut self,
        flags: TempFlags,
        reserved_in_nested_scopes: bool,
        private_name: bool,
        prefix: &str,
        suffix: &str,
    ) -> String {
        let simple = prefix.is_empty() && suffix.is_empty();
        let key;
        let mut temp_flags;
        if simple {
            key = String::new();
            temp_flags = self.name_generator.get_temp_flags(private_name);
        } else {
            // Generate a key to use to acquire a TempFlags counter based on the fixed portions of the generated name.
            let mut k = format_generated_name(private_name, prefix, "" /*base*/, suffix);
            if private_name {
                k = ensure_leading_hash(&k).into_owned();
            }
            temp_flags = self
                .name_generator
                .get_temp_flags_for_formatted_name(private_name, &k);
            key = k;
        }

        if flags != 0 && temp_flags & flags == 0 {
            let full_name = format_generated_name(private_name, prefix, "_i", suffix);
            if self.is_unique_name(&full_name, private_name) {
                temp_flags |= flags;
                self.name_generator.reserve_name(
                    full_name.clone(),
                    private_name,
                    reserved_in_nested_scopes,
                    true, /*temp*/
                );
                if simple {
                    self.name_generator.set_temp_flags(private_name, temp_flags);
                } else {
                    self.name_generator.set_temp_flags_for_formatted_name(
                        private_name,
                        key.clone(),
                        temp_flags,
                    );
                }
                return full_name;
            }
        }

        loop {
            let count = temp_flags & TEMP_FLAGS_COUNT_MASK;
            temp_flags += 1;
            // Skip over 'i' and 'n'
            if count != 8 && count != 13 {
                let name = if count < 26 {
                    format!("_{}", (b'a' + count as u8) as char)
                } else {
                    format!("_{}", count - 26)
                };
                let full_name = format_generated_name(private_name, prefix, &name, suffix);
                if self.is_unique_name(&full_name, private_name) {
                    self.name_generator.reserve_name(
                        full_name.clone(),
                        private_name,
                        reserved_in_nested_scopes,
                        true, /*temp*/
                    );
                    if simple {
                        self.name_generator.set_temp_flags(private_name, temp_flags);
                    } else {
                        self.name_generator.set_temp_flags_for_formatted_name(
                            private_name,
                            key.clone(),
                            temp_flags,
                        );
                    }
                    return full_name;
                }
            }
        }
    }

    /// `makeUniqueName` — generate a name that is unique within the current
    /// file and doesn't conflict with any names in global scope. The name is
    /// formed by adding an '_n' suffix to the specified base name, where n is
    /// a positive integer. Note that names generated by makeTempVariableName
    /// and makeUniqueName are guaranteed to never conflict.
    /// If `optimistic` is set, the first instance will use 'baseName'
    /// verbatim instead of 'baseName_1'
    ///
    /// PORT: `use_file_level_check` replaces Go's `checkFn` parameter, whose
    /// only non-nil value was `IsFileLevelUniqueNameInCurrentFile`.
    fn make_unique_name(
        &mut self,
        base_name: &str,
        use_file_level_check: bool,
        optimistic: bool,
        scoped: bool,
        private_name: bool,
        prefix: &str,
        suffix: &str,
    ) -> String {
        let mut base_name = remove_leading_hash(base_name).to_string();
        if optimistic {
            let full_name = format_generated_name(private_name, prefix, &base_name, suffix);
            if self.check_unique_name(&full_name, private_name, use_file_level_check) {
                self.name_generator.reserve_name(
                    full_name.clone(),
                    private_name,
                    scoped,
                    false, /*temp*/
                );
                return full_name;
            }
        }

        // Find the first unique 'name_n', where n is a positive integer
        if !base_name.is_empty() && !base_name.ends_with('_') {
            base_name.push('_');
        }

        let mut i = 1;
        loop {
            let full_name =
                format_generated_name(private_name, prefix, &format!("{}{}", base_name, i), suffix);
            if self.check_unique_name(&full_name, private_name, use_file_level_check) {
                self.name_generator.reserve_name(
                    full_name.clone(),
                    private_name,
                    scoped,
                    false, /*temp*/
                );
                return full_name;
            }
            i += 1;
        }
    }

    /// `MakeFileLevelOptimisticUniqueName`
    pub(crate) fn make_file_level_optimistic_unique_name(&mut self, name: &str) -> String {
        self.make_unique_name(
            name, true,  /*checkFn*/
            true,  /*optimistic*/
            false, /*scoped*/
            false, /*privateName*/
            "",    /*prefix*/
            "",    /*suffix*/
        )
    }

    /// `checkUniqueName`
    fn check_unique_name(
        &mut self,
        name: &str,
        private_name: bool,
        use_file_level_check: bool,
    ) -> bool {
        if use_file_level_check {
            self.is_file_level_unique_name_in_current_file(name, private_name)
        } else {
            self.is_unique_name(name, private_name)
        }
    }

    /// `(g *NameGenerator) isUniqueName` — on `Printer` since the file-level
    /// check may invoke the `HasGlobalName` handler.
    fn is_unique_name(&mut self, name: &str, private_name: bool) -> bool {
        self.is_file_level_unique_name_in_current_file(name, private_name)
            && !self.name_generator.is_reserved_name(name, private_name)
    }
}

impl<'a> Printer<'a> {
    /// `p.getLiteralTextOfNode(node, sourceFile, flags)`
    pub(crate) fn get_literal_text_of_node(
        &mut self,
        node: NodeId,
        source_file: Option<NodeId>,
        mut flags: GetLiteralTextFlags,
    ) -> String {
        if ast::is_string_literal(&self.nodes[node]) {
            let text_source_node = self.emit_context.text_source(node);
            if let Some(text_source_node) = text_source_node {
                let text: String;
                match self.nodes[text_source_node].kind {
                    Kind::NumericLiteral => {
                        text = self.nodes[text_source_node].text(self.nodes).into_owned()
                    }
                    Kind::Identifier | Kind::PrivateIdentifier | Kind::JsxNamespacedName => {
                        text = self.get_text_of_node(text_source_node, false)
                    }
                    _ => {
                        let sf = ast::get_source_file_of_node(Some(text_source_node), self.nodes);
                        return self.get_literal_text_of_node(text_source_node, sf, flags);
                    }
                }

                if flags & GET_LITERAL_TEXT_FLAGS_JSX_ATTRIBUTE_ESCAPE != 0 {
                    return format!(
                        "\"{}\"",
                        util::escape_jsx_attribute_string(&text, QuoteChar::DoubleQuote)
                    );
                }
                if flags & GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE != 0
                    || self
                        .emit_context
                        .emit_flags(node)
                        .has(EmitFlags::NO_ASCII_ESCAPING)
                {
                    return format!("\"{}\"", util::escape_string(&text, QuoteChar::DoubleQuote));
                }
                return format!(
                    "\"{}\"",
                    util::escape_non_ascii_string(&text, QuoteChar::DoubleQuote)
                );
            }
        }
        // !!! Printer option to control whether to terminate unterminated literals
        if self
            .emit_context
            .emit_flags(node)
            .has(EmitFlags::NO_ASCII_ESCAPING)
        {
            flags |= GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE;
        }
        if self.options.target >= ScriptTarget::ES2021 {
            flags |= GET_LITERAL_TEXT_FLAGS_ALLOW_NUMERIC_SEPARATOR;
        }
        let sf = source_file.or(self.current_source_file);
        util::get_literal_text(self.nodes, node, sf, flags)
    }

    /// `p.getTextOfNode(node, includeTrivia)`
    ///
    /// `node` must be one of Identifier | PrivateIdentifier | LiteralExpression |
    /// JsxNamespacedName
    pub(crate) fn get_text_of_node(&mut self, node: NodeId, include_trivia: bool) -> String {
        if ast::is_member_name(&self.nodes[node])
            && self
                .emit_context
                .get_auto_generate_info(Some(node))
                .is_some()
        {
            return self.generate_name_text(node);
        }

        if ast::is_string_literal(&self.nodes[node])
            && let Some(text_source_node) = self.emit_context.text_source(node)
        {
            return self.get_text_of_node(text_source_node, include_trivia);
        }

        let can_use_source_file = self.current_source_file.is_some()
            && self.nodes[node].parent.is_some()
            && !ast::node_is_synthesized(&self.nodes[node]);

        match self.nodes[node].kind {
            Kind::Identifier | Kind::PrivateIdentifier | Kind::JsxNamespacedName => {
                let same_file = can_use_source_file
                    && ast::get_source_file_of_node(Some(node), self.nodes)
                        == self.emit_context.most_original(self.current_source_file);
                if !same_file {
                    return self.nodes[node].text(self.nodes).into_owned();
                }
            }
            Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TemplateHead
            | Kind::TemplateMiddle
            | Kind::TemplateTail => {
                return self.get_literal_text_of_node(node, None, GET_LITERAL_TEXT_FLAGS_NONE);
            }
            _ => panic!("unexpected node: {:?}", self.nodes[node].kind),
        }
        let sf = self.current_source_file.unwrap();
        tsc_scanner::utilities::get_source_text_of_node_from_source_file(
            self.nodes[sf].as_source_file(),
            node,
            include_trivia,
            self.nodes,
        )
        .into_owned()
    }

    /// `p.isFileLevelUniqueNameInCurrentFile` — returns a value indicating
    /// whether a name is unique globally or within the current file.
    pub(crate) fn is_file_level_unique_name_in_current_file(
        &mut self,
        name: &str,
        _is_generated_name: bool,
    ) -> bool {
        if let Some(source_file) = self.current_source_file {
            let mut has_global_name = |n: &str| -> bool {
                match self.handlers.has_global_name.as_mut() {
                    Some(h) => h(n),
                    None => false,
                }
            };
            return self.emit_context.is_file_level_unique_name(
                self.nodes,
                source_file,
                name,
                &mut has_global_name,
            );
        }
        true
    }
}

#[cfg(test)]
mod tests {
    //! Ported from tsc/internal/printer/namegenerator_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763.
    //!
    //! PORT: Go's `NameGenerator` is a standalone struct; here the name-generation
    //! methods live on `Printer` (which embeds `NameGenerator` state), so tests
    //! construct a `Printer` around the `EmitContext` instead.

    use super::*;
    use crate::emit_context::{AutoGenerateOptions, EmitContext};
    use crate::emit_flags::GeneratedIdentifierFlags;
    use crate::printer::{PrintHandlers, Printer, PrinterOptions};
    use tsc_ast::Node;

    struct Fixture {
        ec: EmitContext,
        nodes: Vec<Node>,
    }

    fn fixture() -> Fixture {
        Fixture {
            ec: EmitContext::new(),
            nodes: Vec::new(),
        }
    }

    fn printer<'a>(f: &'a mut Fixture) -> Printer<'a> {
        Printer::new(
            PrinterOptions::default(),
            PrintHandlers::default(),
            &mut f.ec,
            &mut f.nodes,
            &[],
        )
    }

    /// `TestTempVariable1`
    #[test]
    fn test_temp_variable_1() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_temp_variable(&mut f.nodes);
        let name2 = f.ec.factory.new_temp_variable(&mut f.nodes);

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "_a");
        assert_eq!(g.generate_name_text(name2), "_b");
    }

    /// `TestTempVariable2`
    #[test]
    fn test_temp_variable_2() {
        let mut f = fixture();
        let options = AutoGenerateOptions {
            prefix: "A".into(),
            suffix: "B".into(),
            ..Default::default()
        };
        let name1 = f.ec.factory.new_temp_variable_ex(&mut f.nodes, &options);
        let name2 = f.ec.factory.new_temp_variable_ex(&mut f.nodes, &options);

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "A_aB");
        assert_eq!(g.generate_name_text(name2), "A_bB");
    }

    /// `TestTempVariable3`
    #[test]
    fn test_temp_variable_3() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_temp_variable(&mut f.nodes);

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "_a");
        assert_eq!(g.generate_name_text(name1), "_a");
    }

    /// `TestTempVariableScoped`
    #[test]
    fn test_temp_variable_scoped() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_temp_variable(&mut f.nodes);
        let name2 = f.ec.factory.new_temp_variable(&mut f.nodes);

        let mut g = printer(&mut f);
        let text1 = g.generate_name_text(name1);
        g.push_scope(false);
        let text2 = g.generate_name_text(name2);
        g.pop_scope(false);

        assert_eq!(text1, "_a");
        assert_eq!(text2, "_a");
    }

    /// `TestTempVariableScopedReserved`
    #[test]
    fn test_temp_variable_scoped_reserved() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_temp_variable_ex(
            &mut f.nodes,
            &AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                ..Default::default()
            },
        );
        let name2 = f.ec.factory.new_temp_variable(&mut f.nodes);

        let mut g = printer(&mut f);
        let text1 = g.generate_name_text(name1);
        g.push_scope(false);
        let text2 = g.generate_name_text(name2);
        g.pop_scope(false);

        assert_eq!(text1, "_a");
        assert_eq!(text2, "_b");
    }

    /// `TestLoopVariable1`
    #[test]
    fn test_loop_variable_1() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_loop_variable(&mut f.nodes);
        let name2 = f.ec.factory.new_loop_variable(&mut f.nodes);

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "_i");
        assert_eq!(g.generate_name_text(name2), "_a");
    }

    /// `TestLoopVariable2`
    #[test]
    fn test_loop_variable_2() {
        let mut f = fixture();
        let options = AutoGenerateOptions {
            prefix: "A".into(),
            suffix: "B".into(),
            ..Default::default()
        };
        let name1 = f.ec.factory.new_loop_variable_ex(&mut f.nodes, &options);
        let name2 = f.ec.factory.new_loop_variable_ex(&mut f.nodes, &options);

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "A_iB");
        assert_eq!(g.generate_name_text(name2), "A_aB");
    }

    /// `TestLoopVariable3`
    #[test]
    fn test_loop_variable_3() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_loop_variable(&mut f.nodes);

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "_i");
        assert_eq!(g.generate_name_text(name1), "_i");
    }

    /// `TestLoopVariableScoped`
    #[test]
    fn test_loop_variable_scoped() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_loop_variable(&mut f.nodes);
        let name2 = f.ec.factory.new_loop_variable(&mut f.nodes);

        let mut g = printer(&mut f);
        let text1 = g.generate_name_text(name1);
        g.push_scope(false);
        let text2 = g.generate_name_text(name2);
        g.pop_scope(false);

        assert_eq!(text1, "_i");
        assert_eq!(text2, "_i");
    }

    /// `TestUniqueName1`
    #[test]
    fn test_unique_name_1() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_unique_name(&mut f.nodes, "foo");
        let name2 = f.ec.factory.new_unique_name(&mut f.nodes, "foo");

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "foo_1");
        assert_eq!(g.generate_name_text(name2), "foo_2");
    }

    /// `TestUniqueName2`
    #[test]
    fn test_unique_name_2() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_unique_name(&mut f.nodes, "foo");

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "foo_1");
        // Expected to be same because GenerateName goes off object identity
        assert_eq!(g.generate_name_text(name1), "foo_1");
    }

    /// `TestUniqueNameScoped`
    #[test]
    fn test_unique_name_scoped() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_unique_name(&mut f.nodes, "foo");
        let name2 = f.ec.factory.new_unique_name(&mut f.nodes, "foo");

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "foo_1");
        g.push_scope(false);
        // Matches Strada, but is incorrect
        assert_eq!(g.generate_name_text(name2), "foo_2");
        g.pop_scope(false);
    }

    /// `TestUniquePrivateName1`
    #[test]
    fn test_unique_private_name_1() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_unique_private_name(&mut f.nodes, "#foo");
        let name2 = f.ec.factory.new_unique_private_name(&mut f.nodes, "#foo");

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "#foo_1");
        assert_eq!(g.generate_name_text(name2), "#foo_2");
    }

    /// `TestUniquePrivateName2`
    #[test]
    fn test_unique_private_name_2() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_unique_private_name(&mut f.nodes, "#foo");

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "#foo_1");
        assert_eq!(g.generate_name_text(name1), "#foo_1");
    }

    /// `TestUniquePrivateNameScoped`
    #[test]
    fn test_unique_private_name_scoped() {
        let mut f = fixture();
        let name1 = f.ec.factory.new_unique_private_name(&mut f.nodes, "#foo");
        let name2 = f.ec.factory.new_unique_private_name(&mut f.nodes, "#foo");

        let mut g = printer(&mut f);
        assert_eq!(g.generate_name_text(name1), "#foo_1");
        // private names are always reserved in nested scopes
        g.push_scope(false);
        assert_eq!(g.generate_name_text(name2), "#foo_2");
        g.pop_scope(false);
    }

    // PORT(deferred): TestGeneratedNameForIdentifier*, TestGeneratedNameForNamespace*,
    // TestGeneratedNameForNodeCached, TestGeneratedNameForImport/Export/Class/Method,
    // and the binder-dependent tests in namegenerator_test.go require `GenerateName`
    // entry points that drive source-file–scoped name resolution through the binder
    // and symbol table; they are deferred until the printer's resolver path is
    // exercised end-to-end.
}
