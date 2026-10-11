// Ported from tsc/internal/ls/semantictokens.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tsc_ast::ast::Node;
use tsc_ast::kind_generated::Kind;
use tsc_ast::{self as ast, ModifierFlags, NodeFlags, NodeId, SymbolFlags, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_checker::types::{SignatureKind, TypeFlags, TypeId};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_lsconv::converters::{source_file_script, Converters};
use tsc_lsproto::{self as lsproto, SemanticTokenModifier, SemanticTokenType};
use tsc_spanmap::{Feature, Fidelity};

use crate::api::Error;
use crate::languageservice::LanguageService;
use crate::utilities::get_meaning_from_location;

/// `tokenTypes` defines the order of token types for encoding.
const TOKEN_TYPES: [SemanticTokenType; 23] = [
    SemanticTokenType::Namespace,
    SemanticTokenType::Class,
    SemanticTokenType::Enum,
    SemanticTokenType::Interface,
    SemanticTokenType::Struct,
    SemanticTokenType::TypeParameter,
    SemanticTokenType::Type,
    SemanticTokenType::Parameter,
    SemanticTokenType::Variable,
    SemanticTokenType::Property,
    SemanticTokenType::EnumMember,
    SemanticTokenType::Decorator,
    SemanticTokenType::Event,
    SemanticTokenType::Function,
    SemanticTokenType::Method,
    SemanticTokenType::Macro,
    SemanticTokenType::Label,
    SemanticTokenType::Comment,
    SemanticTokenType::String,
    SemanticTokenType::Keyword,
    SemanticTokenType::Number,
    SemanticTokenType::Regexp,
    SemanticTokenType::Operator,
];

const SEMANTIC_TOKEN_MODIFIER_LOCAL: SemanticTokenModifier =
    SemanticTokenModifier(Cow::Borrowed("local"));

/// `tokenModifiers` defines the order of token modifiers for encoding.
const TOKEN_MODIFIERS: [SemanticTokenModifier; 11] = [
    SemanticTokenModifier::Declaration,
    SemanticTokenModifier::Definition,
    SemanticTokenModifier::Readonly,
    SemanticTokenModifier::Static,
    SemanticTokenModifier::Deprecated,
    SemanticTokenModifier::Abstract,
    SemanticTokenModifier::Async,
    SemanticTokenModifier::Modification,
    SemanticTokenModifier::Documentation,
    SemanticTokenModifier::DefaultLibrary,
    SEMANTIC_TOKEN_MODIFIER_LOCAL,
];

/// `tokenType`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum TokenType {
    Namespace,
    Class,
    Enum,
    Interface,
    Struct,
    TypeParameter,
    Type,
    Parameter,
    Variable,
    Property,
    EnumMember,
    Decorator,
    Event,
    Function,
    Method, // Previously called "member" in TypeScript
    Macro,
    Label,
    Comment,
    String,
    Keyword,
    Number,
    Regexp,
    Operator,
}

/// `tokenModifier` — a bitmask over `TOKEN_MODIFIERS` indices.
mod token_modifier {
    pub const DECLARATION: u32 = 1 << 0;
    pub const DEFINITION: u32 = 1 << 1;
    pub const READONLY: u32 = 1 << 2;
    pub const STATIC: u32 = 1 << 3;
    pub const DEPRECATED: u32 = 1 << 4;
    pub const ABSTRACT: u32 = 1 << 5;
    pub const ASYNC: u32 = 1 << 6;
    pub const MODIFICATION: u32 = 1 << 7;
    pub const DOCUMENTATION: u32 = 1 << 8;
    pub const DEFAULT_LIBRARY: u32 = 1 << 9;
    pub const LOCAL: u32 = 1 << 10;
}

/// `SemanticTokensLegend` returns the legend describing the token types and
/// modifiers. It filters the legend to only include types and modifiers that
/// the client supports, as indicated by `clientCapabilities`.
pub fn semantic_tokens_legend(
    client_capabilities: &lsproto::ResolvedSemanticTokensClientCapabilities,
) -> lsproto::SemanticTokensLegend {
    let types = TOKEN_TYPES
        .iter()
        .filter(|t| {
            client_capabilities
                .token_types
                .iter()
                .any(|c| c == t.0.as_ref())
        })
        .map(|t| t.0.to_string())
        .collect();
    let modifiers = TOKEN_MODIFIERS
        .iter()
        .filter(|m| {
            client_capabilities
                .token_modifiers
                .iter()
                .any(|c| c == m.0.as_ref())
        })
        .map(|m| m.0.to_string())
        .collect();
    lsproto::SemanticTokensLegend {
        token_types: Some(types),
        token_modifiers: Some(modifiers),
    }
}

/// `semanticToken`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct SemanticToken {
    node: NodeId,
    file: NodeId,
    token_type: TokenType,
    token_modifier: u32,
}

impl<'h> LanguageService<'h> {
    /// `ProvideSemanticTokens`.
    pub fn provide_semantic_tokens(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
    ) -> Result<lsproto::SemanticTokensResponse, Error> {
        let (program, file) = self.get_program_and_file(&document_uri);
        let mut files: Vec<NodeId> = Vec::with_capacity(1 + 8);
        files.push(file);
        {
            let nodes = program.nodes(file.file_index());
            files.extend_from_slice(nodes[file].as_source_file().supplemental_source_files());
        }

        let mut tokens: Vec<SemanticToken> = Vec::new();
        for projection in files {
            let (checker, done) = program.get_type_checker_for_file(ctx.clone(), projection);
            for mut token in
                self.collect_semantic_tokens(ctx, &checker, projection, &program)
            {
                token.file = projection;
                tokens.push(token);
            }
            done();
        }
        sort_semantic_tokens(&mut tokens, &program, &self.converters);

        if tokens.is_empty() {
            return Ok(lsproto::SemanticTokensOrNull {
                semantic_tokens: None,
            });
        }

        // Convert to LSP format (relative encoding)
        let encoded = encode_semantic_tokens(ctx, &tokens, &program, &self.converters);

        Ok(lsproto::SemanticTokensOrNull {
            semantic_tokens: Some(lsproto::SemanticTokens {
                result_id: None,
                data: Some(encoded),
            }),
        })
    }

    /// `ProvideSemanticTokensRange`.
    pub fn provide_semantic_tokens_range(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
        range: lsproto::Range,
    ) -> Result<lsproto::SemanticTokensRangeResponse, Error> {
        let (program, file) = self.get_program_and_file(&document_uri);
        // `mapped_ranges` borrows `nodes`; it must stay alive for the loop.
        let nodes = program.nodes(file.file_index());
        let mapped_ranges = self.converters.from_lsp_range_intersecting_for_source_file(
            file,
            &nodes,
            range,
            Feature::SemanticTokens,
        );
        let mut tokens: Vec<SemanticToken> = Vec::new();
        let mut seen: HashSet<SemanticToken> = HashSet::new();
        for mapped in mapped_ranges {
            let projection = mapped.script.file;
            let (checker, done) = program.get_type_checker_for_file(ctx.clone(), projection);
            for mut token in self.collect_semantic_tokens_in_range(
                ctx,
                &checker,
                projection,
                &program,
                mapped.span.pos(),
                mapped.span.end(),
            ) {
                token.file = projection;
                if seen.insert(token) {
                    tokens.push(token);
                }
            }
            done();
        }
        sort_semantic_tokens(&mut tokens, &program, &self.converters);

        if tokens.is_empty() {
            return Ok(lsproto::SemanticTokensOrNull {
                semantic_tokens: None,
            });
        }

        // Convert to LSP format (relative encoding)
        let encoded = encode_semantic_tokens(ctx, &tokens, &program, &self.converters);

        Ok(lsproto::SemanticTokensOrNull {
            semantic_tokens: Some(lsproto::SemanticTokens {
                result_id: None,
                data: Some(encoded),
            }),
        })
    }

    /// `collectSemanticTokens`.
    fn collect_semantic_tokens(
        &self,
        ctx: &Context,
        c: &Rc<RefCell<Checker>>,
        file: NodeId,
        program: &Rc<Program>,
    ) -> Vec<SemanticToken> {
        let (pos, end) = {
            let nodes = program.nodes(file.file_index());
            (nodes[file].pos(), nodes[file].end())
        };
        self.collect_semantic_tokens_in_range(ctx, c, file, program, pos, end)
    }

    /// `collectSemanticTokensInRange`.
    fn collect_semantic_tokens_in_range(
        &self,
        ctx: &Context,
        c: &Rc<RefCell<Checker>>,
        file: NodeId,
        program: &Rc<Program>,
        span_start: i32,
        span_end: i32,
    ) -> Vec<SemanticToken> {
        let mut tokens: Vec<SemanticToken> = Vec::new();
        let mut in_jsx_element = false;

        // A single mutable arena handle stands in for Go's shared node graph:
        // `getMeaningFromLocation` requires `&mut Vec<Node>` (JSDoc-location
        // adjustment), and acquiring it once avoids a copy-on-write clone per
        // visited token.
        let mut nodes = program.nodes_mut(file.file_index());
        let nodes: &mut Vec<Node> = &mut nodes;
        let mut ch = c.borrow_mut();

        fn visit(
            ctx: &Context,
            ch: &mut Checker,
            program: &Rc<Program>,
            nodes: &mut Vec<Node>,
            node: NodeId,
            file: NodeId,
            span_start: i32,
            span_end: i32,
            in_jsx_element: &mut bool,
            tokens: &mut Vec<SemanticToken>,
        ) -> bool {
            // Check for cancellation
            if ctx.is_cancelled() {
                return false;
            }

            if nodes[node].flags.intersects(NodeFlags::REPARSED) {
                return false;
            }
            let node_end = nodes[node].end();
            if nodes[node].pos() >= span_end || node_end <= span_start {
                return false;
            }

            let prev_in_jsx_element = *in_jsx_element;
            if ast::is_jsx_element(&nodes[node]) || ast::is_jsx_self_closing_element(&nodes[node]) {
                *in_jsx_element = true;
            } else if ast::is_jsx_expression(&nodes[node]) {
                *in_jsx_element = false;
            }

            if (ast::is_identifier(&nodes[node]) || ast::is_private_identifier(&nodes[node]))
                && !nodes[node].text(nodes).is_empty()
                && !*in_jsx_element
                && !is_in_import_clause(nodes, node)
                && !is_infinity_or_nan_string(&nodes[node].text(nodes))
            {
                let symbol = ch.get_symbol_at_location_api(node);
                if let Some(mut symbol) = symbol {
                    // Resolve aliases
                    {
                        let symbols = program.symbols.borrow();
                        if symbols[symbol.index()].flags.intersects(SymbolFlags::ALIAS) {
                            drop(symbols);
                            symbol = ch.get_aliased_symbol(symbol).unwrap_or(symbol);
                        }
                    }

                    let meaning = get_meaning_from_location(nodes, node);
                    if let Some(mut token_type) = classify_symbol(program, symbol, meaning) {
                        let mut token_modifiers: u32 = 0;

                        // Check if this is a declaration
                        if let Some(parent) = nodes[node].parent {
                            let parent_is_declaration = ast::is_binding_element(&nodes[parent])
                                || token_from_declaration_mapping(nodes[parent].kind)
                                    == Some(token_type);
                            if parent_is_declaration && nodes[parent].name() == Some(node) {
                                token_modifiers |= token_modifier::DECLARATION;
                            }
                        }

                        // Property declaration in constructor: reclassify
                        // parameters as properties in property access context
                        if token_type == TokenType::Parameter
                            && ast::is_right_side_of_qualified_name_or_property_access(node, nodes)
                        {
                            token_type = TokenType::Property;
                        }

                        // Type-based reclassification
                        token_type = reclassify_by_type(ch, nodes, node, token_type);

                        // Get the value declaration to check modifiers
                        let (value_declaration, declarations, symbol_flags) = {
                            let symbols = program.symbols.borrow();
                            let s = &symbols[symbol.index()];
                            (
                                s.value_declaration,
                                s.declarations.clone(),
                                s.flags,
                            )
                        };
                        if let Some(decl) = value_declaration {
                            let decl_nodes = program.nodes(decl.file_index());
                            let modifiers = ast::get_combined_modifier_flags(decl, &decl_nodes);
                            let node_flags = ast::get_combined_node_flags(decl, &decl_nodes);

                            if modifiers.intersects(ModifierFlags::STATIC) {
                                token_modifiers |= token_modifier::STATIC;
                            }
                            if modifiers.intersects(ModifierFlags::ASYNC) {
                                token_modifiers |= token_modifier::ASYNC;
                            }
                            if token_type != TokenType::Class && token_type != TokenType::Interface
                                && (modifiers.intersects(ModifierFlags::READONLY)
                                    || node_flags.intersects(NodeFlags::CONST)
                                    || symbol_flags.intersects(SymbolFlags::ENUM_MEMBER))
                            {
                                token_modifiers |= token_modifier::READONLY;
                            }
                            if (token_type == TokenType::Variable
                                || token_type == TokenType::Function)
                                && is_local_declaration(&decl_nodes, decl, file)
                            {
                                token_modifiers |= token_modifier::LOCAL;
                            }
                            let decl_source_file =
                                ast::get_source_file_of_node(Some(decl), &decl_nodes);
                            if let Some(decl_source_file) = decl_source_file {
                                let path = decl_nodes[decl_source_file]
                                    .as_source_file()
                                    .path_key()
                                    .clone();
                                if program.is_source_file_default_library(&path) {
                                    token_modifiers |= token_modifier::DEFAULT_LIBRARY;
                                }
                            }
                        } else {
                            for decl in declarations {
                                let decl_nodes = program.nodes(decl.file_index());
                                let decl_source_file =
                                    ast::get_source_file_of_node(Some(decl), &decl_nodes);
                                if let Some(decl_source_file) = decl_source_file {
                                    let path = decl_nodes[decl_source_file]
                                        .as_source_file()
                                        .path_key()
                                        .clone();
                                    if program.is_source_file_default_library(&path) {
                                        token_modifiers |= token_modifier::DEFAULT_LIBRARY;
                                        break;
                                    }
                                }
                            }
                        }

                        tokens.push(SemanticToken {
                            node,
                            file,
                            token_type,
                            token_modifier: token_modifiers,
                        });
                    }
                }
            }

            // `for_each_child` borrows `nodes` immutably, so collect the
            // children before recursing (the recursion may mutably borrow
            // `nodes` for `getMeaningFromLocation`).
            let mut children: Vec<NodeId> = Vec::new();
            nodes[node].for_each_child(nodes, &mut |child| {
                children.push(child);
                false
            });
            for child in children {
                visit(
                    ctx,
                    ch,
                    program,
                    nodes,
                    child,
                    file,
                    span_start,
                    span_end,
                    in_jsx_element,
                    tokens,
                );
            }
            *in_jsx_element = prev_in_jsx_element;
            false
        }

        visit(
            ctx,
            &mut ch,
            program,
            nodes,
            file,
            file,
            span_start,
            span_end,
            &mut in_jsx_element,
            &mut tokens,
        );

        // Check for cancellation after collection
        if ctx.is_cancelled() {
            return Vec::new();
        }

        tokens
    }
}

/// `sortSemanticTokens`.
fn sort_semantic_tokens(
    tokens: &mut [SemanticToken],
    program: &Rc<Program>,
    converters: &Converters,
) {
    tokens.sort_by(|a, b| {
        let (a_range, _) = semantic_token_lsp_range(*a, program, converters);
        let (b_range, _) = semantic_token_lsp_range(*b, program, converters);
        a_range
            .start
            .line
            .cmp(&b_range.start.line)
            .then(a_range.start.character.cmp(&b_range.start.character))
            .then_with(|| {
                let a_path = {
                    let nodes = program.nodes(a.file.file_index());
                    nodes[a.file].as_source_file().path_key().clone()
                };
                let b_path = {
                    let nodes = program.nodes(b.file.file_index());
                    nodes[b.file].as_source_file().path_key().clone()
                };
                a_path.cmp(&b_path)
            })
            .then_with(|| {
                let a_pos = {
                    let nodes = program.nodes(a.node.file_index());
                    nodes[a.node].pos()
                };
                let b_pos = {
                    let nodes = program.nodes(b.node.file_index());
                    nodes[b.node].pos()
                };
                a_pos.cmp(&b_pos)
            })
    });
}

/// `semanticTokenLSPRange`.
fn semantic_token_lsp_range(
    token: SemanticToken,
    program: &Rc<Program>,
    converters: &Converters,
) -> (lsproto::Range, Fidelity) {
    let nodes = program.nodes(token.file.file_index());
    let source_file = nodes[token.file].as_source_file();
    let start = tsc_scanner::scanner::get_token_pos_of_node(
        token.node,
        source_file,
        false, /*includeJSDoc*/
        &nodes,
    );
    let script = source_file_script(token.file, &nodes);
    converters.to_lsp_range_for_feature(
        &script,
        TextRange::new(start, nodes[token.node].end()),
        Feature::SemanticTokens,
    )
}

/// `classifySymbol` — `Ok`'s second value becomes `Option`.
fn classify_symbol(
    program: &Rc<Program>,
    symbol: SymbolId,
    meaning: ast::SemanticMeaning,
) -> Option<TokenType> {
    let (flags, value_declaration, declarations) = {
        let symbols = program.symbols.borrow();
        let s = &symbols[symbol.index()];
        (s.flags, s.value_declaration, s.declarations.clone())
    };
    if flags.intersects(SymbolFlags::CLASS) {
        return Some(TokenType::Class);
    }
    if flags.intersects(SymbolFlags::ENUM) {
        return Some(TokenType::Enum);
    }
    if flags.intersects(SymbolFlags::TYPE_ALIAS) {
        return Some(TokenType::Type);
    }
    if flags.intersects(SymbolFlags::INTERFACE)
        && (meaning & ast::SemanticMeaning::TYPE) != ast::SemanticMeaning::NONE
    {
        return Some(TokenType::Interface);
    }
    if flags.intersects(SymbolFlags::TYPE_PARAMETER) {
        return Some(TokenType::TypeParameter);
    }

    // Check the value declaration
    let mut decl = value_declaration;
    if decl.is_none() && !declarations.is_empty() {
        decl = Some(declarations[0]);
    }
    if let Some(mut decl) = decl {
        let decl_nodes = program.nodes(decl.file_index());
        if ast::is_binding_element(&decl_nodes[decl]) {
            decl = get_declaration_for_binding_element(&decl_nodes, decl);
        }
        if let Some(token_type) = token_from_declaration_mapping(decl_nodes[decl].kind) {
            return Some(token_type);
        }
    }

    None
}

/// `tokenFromDeclarationMapping`.
fn token_from_declaration_mapping(kind: Kind) -> Option<TokenType> {
    match kind {
        Kind::VariableDeclaration => Some(TokenType::Variable),
        Kind::Parameter => Some(TokenType::Parameter),
        Kind::PropertyDeclaration => Some(TokenType::Property),
        Kind::ModuleDeclaration => Some(TokenType::Namespace),
        Kind::EnumDeclaration => Some(TokenType::Enum),
        Kind::EnumMember => Some(TokenType::EnumMember),
        Kind::ClassDeclaration | Kind::ClassExpression => Some(TokenType::Class),
        Kind::MethodDeclaration => Some(TokenType::Method),
        Kind::FunctionDeclaration | Kind::FunctionExpression => Some(TokenType::Function),
        Kind::MethodSignature => Some(TokenType::Method),
        Kind::GetAccessor | Kind::SetAccessor => Some(TokenType::Property),
        Kind::PropertySignature => Some(TokenType::Property),
        Kind::InterfaceDeclaration => Some(TokenType::Interface),
        Kind::TypeAliasDeclaration => Some(TokenType::Type),
        Kind::TypeParameter => Some(TokenType::TypeParameter),
        Kind::PropertyAssignment | Kind::ShorthandPropertyAssignment => {
            Some(TokenType::Property)
        }
        _ => None,
    }
}

/// `reclassifyByType` — type-based reclassification for variables,
/// properties, and parameters.
fn reclassify_by_type(
    c: &mut Checker,
    nodes: &[Node],
    node: NodeId,
    tt: TokenType,
) -> TokenType {
    /// `test`: `condition` holds of `typ` or of any union constituent.
    /// PORT: Go's `typ != nil` check is unreachable — `get_type_at_location`
    /// always returns a type (errorType at worst).
    fn test(
        c: &mut Checker,
        typ: TypeId,
        condition: &mut dyn FnMut(&mut Checker, TypeId) -> bool,
    ) -> bool {
        if condition(c, typ) {
            return true;
        }
        let ty = c.types.get(typ);
        if ty.flags().intersects(TypeFlags::UNION) {
            let members = ty.types().to_vec();
            drop(ty);
            if members.into_iter().any(|t| condition(c, t)) {
                return true;
            }
        }
        false
    }

    if tt == TokenType::Variable || tt == TokenType::Property || tt == TokenType::Parameter {
        let typ = c.get_type_at_location(node);

        // Check for constructor signatures (class-like)
        if tt != TokenType::Parameter {
            let has_construct_signatures = test(c, typ, &mut |c, t| {
                !c.get_signatures_of_type(t, SignatureKind::Construct)
                    .is_empty()
            });
            if has_construct_signatures {
                return TokenType::Class;
            }
        }

        // Check for call signatures (function-like)
        // Must have call signatures AND (no properties OR be used in call
        // context)
        let has_call_signatures = test(c, typ, &mut |c, t| {
            !c.get_signatures_of_type(t, SignatureKind::Call).is_empty()
        });
        if has_call_signatures {
            let has_no_properties = !test(c, typ, &mut |c, t| {
                c.types
                    .get(t)
                    .data
                    .as_object_type()
                    .is_some_and(|obj_type| !obj_type.structured_type.properties().is_empty())
            });
            if has_no_properties || is_expression_in_call_expression(nodes, node) {
                if tt == TokenType::Property {
                    return TokenType::Method;
                }
                return TokenType::Function;
            }
        }
    }
    tt
}

/// `isLocalDeclaration` — `nodes` is the arena owning `decl`.
fn is_local_declaration(nodes: &[Node], decl: NodeId, source_file: NodeId) -> bool {
    let decl = if ast::is_binding_element(&nodes[decl]) {
        get_declaration_for_binding_element(nodes, decl)
    } else {
        decl
    };
    if ast::is_variable_declaration(&nodes[decl]) {
        let parent = nodes[decl].parent;
        // Check if this is a catch clause parameter
        if parent.is_some_and(|p| ast::is_catch_clause(&nodes[p])) {
            return ast::get_source_file_of_node(Some(decl), nodes) == Some(source_file);
        }
        if parent.is_some_and(|p| ast::is_variable_declaration_list(&nodes[p])) {
            let parent = parent.expect("parent");
            if let Some(grandparent) = nodes[parent].parent {
                let great_grandparent = nodes[grandparent].parent;
                return (!great_grandparent.is_some_and(|g| ast::is_source_file(&nodes[g]))
                    || ast::is_catch_clause(&nodes[grandparent]))
                    && ast::get_source_file_of_node(Some(decl), nodes) == Some(source_file);
            }
        }
    } else if ast::is_function_declaration(&nodes[decl]) {
        let parent = nodes[decl].parent;
        return parent.is_some_and(|p| !ast::is_source_file(&nodes[p]))
            && ast::get_source_file_of_node(Some(decl), nodes) == Some(source_file);
    }
    false
}

/// `getDeclarationForBindingElement` — `nodes` is the arena owning `element`.
fn get_declaration_for_binding_element(nodes: &[Node], element: NodeId) -> NodeId {
    let mut element = element;
    loop {
        let parent = nodes[element].parent;
        if let Some(parent) = parent {
            if ast::is_binding_pattern(&nodes[parent]) {
                if let Some(grandparent) = nodes[parent].parent {
                    if ast::is_binding_element(&nodes[grandparent]) {
                        element = grandparent;
                        continue;
                    }
                }
                return nodes[parent].parent.unwrap_or(parent);
            }
        }
        return element;
    }
}

/// `isInImportClause`.
fn is_in_import_clause(nodes: &[Node], node: NodeId) -> bool {
    nodes[node].parent.is_some_and(|parent| {
        ast::is_import_clause(&nodes[parent])
            || ast::is_import_specifier(&nodes[parent])
            || ast::is_namespace_import(&nodes[parent])
    })
}

/// `isExpressionInCallExpression`.
fn is_expression_in_call_expression(nodes: &[Node], node: NodeId) -> bool {
    let mut node = node;
    while ast::is_right_side_of_qualified_name_or_property_access(node, nodes) {
        node = nodes[node].parent.expect("right side has parent");
    }
    nodes[node].parent.is_some_and(|parent| {
        ast::is_call_expression(&nodes[parent]) && nodes[parent].expression() == Some(node)
    })
}

/// `isInfinityOrNaNString`.
fn is_infinity_or_nan_string(text: &str) -> bool {
    text == "Infinity" || text == "NaN"
}

/// `encodeSemanticTokens` encodes tokens into the LSP format using relative
/// positioning. It filters tokens based on client capabilities, only
/// including types and modifiers that the client supports.
fn encode_semantic_tokens(
    ctx: &Context,
    tokens: &[SemanticToken],
    program: &Rc<Program>,
    converters: &Converters,
) -> Vec<u32> {
    // Build mapping from server token types/modifiers to client indices
    let mut type_mapping: HashMap<TokenType, u32> = HashMap::new();
    let mut modifier_mapping: HashMap<Cow<'static, str>, u32> = HashMap::new();

    let client_capabilities = &lsproto::get_client_capabilities(ctx)
        .text_document
        .semantic_tokens;

    // Map server token types to client-supported indices
    let mut client_idx: u32 = 0;
    for (i, server_type) in TOKEN_TYPES.iter().enumerate() {
        if client_capabilities
            .token_types
            .iter()
            .any(|t| t == server_type.0.as_ref())
        {
            type_mapping.insert(TOKEN_TYPES_INDEX[i], client_idx);
            client_idx += 1;
        }
    }

    // Map server token modifiers to client-supported bit positions
    let mut client_bit: u32 = 0;
    for server_modifier in TOKEN_MODIFIERS.iter() {
        if client_capabilities
            .token_modifiers
            .iter()
            .any(|m| m == server_modifier.0.as_ref())
        {
            modifier_mapping.insert(server_modifier.0.clone(), client_bit);
            client_bit += 1;
        }
    }

    // Each token encodes 5 uint32 values: deltaLine, deltaChar, length,
    // tokenType, tokenModifiers
    let mut encoded: Vec<u32> = Vec::with_capacity(tokens.len() * 5);
    let mut prev_line: u32 = 0;
    let mut prev_char: u32 = 0;

    for token in tokens {
        // Skip tokens with types not supported by the client
        let Some(&client_type_idx) = type_mapping.get(&token.token_type) else {
            continue;
        };

        // Map modifiers to client-supported bit mask
        let mut client_modifier_mask: u32 = 0;
        for (i, server_modifier) in TOKEN_MODIFIERS.iter().enumerate() {
            if token.token_modifier & (1 << i) != 0 {
                if let Some(&client_bit) = modifier_mapping.get(server_modifier.0.as_ref()) {
                    client_modifier_mask |= 1 << client_bit;
                }
            }
        }

        // Semantic tokens must describe one concrete source segment;
        // synthesized and cross-segment tokens do not identify a coherent
        // token in the original text.
        let (lsp_range, fidelity) = semantic_token_lsp_range(*token, program, converters);
        if !fidelity.is_exact() {
            continue;
        }
        let start_pos = lsp_range.start;
        let end_pos = lsp_range.end;

        // Length is the character difference when on the same line
        let token_length: u32;
        if start_pos.line == end_pos.line {
            token_length = end_pos.character - start_pos.character;
        } else {
            let token_pos = {
                let nodes = program.nodes(token.node.file_index());
                nodes[token.node].pos()
            };
            panic!(
                "semantic tokens: token spans multiple lines: start=({},{}) end=({},{}) for token at offset {}",
                start_pos.line, start_pos.character, end_pos.line, end_pos.character, token_pos
            );
        }

        let line = start_pos.line;
        let char_ = start_pos.character;

        // Multiple virtual projections can describe the same original token;
        // LSP requires one entry per start position, so retain the first
        // after sorting.
        if !encoded.is_empty() && line == prev_line && char_ == prev_char {
            continue;
        }
        if !encoded.is_empty() && (line < prev_line || (line == prev_line && char_ < prev_char)) {
            let token_pos = {
                let nodes = program.nodes(token.node.file_index());
                nodes[token.node].pos()
            };
            panic!(
                "semantic tokens: positions must be strictly increasing: prev=({},{}) current=({},{}) for token at offset {}",
                prev_line, prev_char, line, char_, token_pos
            );
        }

        // Encode as: [deltaLine, deltaChar, length, tokenType, tokenModifiers]
        let delta_line = line - prev_line;
        let delta_char = if delta_line == 0 { char_ - prev_char } else { char_ };

        encoded.extend_from_slice(&[
            delta_line,
            delta_char,
            token_length,
            client_type_idx,
            client_modifier_mask,
        ]);

        prev_line = line;
        prev_char = char_;
    }

    encoded
}

/// `TOKEN_TYPES` indexed by `TokenType` ordinal — mirrors Go's
/// `typeMapping[tokenType(i)]` where the enum value is the array index.
const TOKEN_TYPES_INDEX: [TokenType; 23] = [
    TokenType::Namespace,
    TokenType::Class,
    TokenType::Enum,
    TokenType::Interface,
    TokenType::Struct,
    TokenType::TypeParameter,
    TokenType::Type,
    TokenType::Parameter,
    TokenType::Variable,
    TokenType::Property,
    TokenType::EnumMember,
    TokenType::Decorator,
    TokenType::Event,
    TokenType::Function,
    TokenType::Method,
    TokenType::Macro,
    TokenType::Label,
    TokenType::Comment,
    TokenType::String,
    TokenType::Keyword,
    TokenType::Number,
    TokenType::Regexp,
    TokenType::Operator,
];
