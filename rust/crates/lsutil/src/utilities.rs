// Ported from tsc/internal/ls/lsutil/utilities.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.

use std::cell::Cell;

use tsc_ast::ast::Node;
use tsc_ast::{self as ast, Kind, NodeFlags, NodeId, TokenFlags};
use tsc_astnav::tokens::get_start_of_node;
use tsc_core::core::find;
use tsc_core::nodemodules::{EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES, NODE_CORE_MODULES};
use tsc_core::tristate::Tristate;
use tsc_scanner::scanner::{
    get_ecma_line_of_position, is_identifier_part, is_identifier_start, skip_trivia,
    string_to_token,
};
use tsc_tspath::{get_base_file_name, remove_any_file_extension};

use crate::asi::{
    syntax_requires_trailing_comma_or_semicolon_or_asi, syntax_requires_trailing_semicolon_or_asi,
};
use crate::children::get_last_token;
use crate::userpreferences::QuotePreference;
use crate::userpreferences_generated::UserPreferences;

/// `ProbablyUsesSemicolons`.
pub fn probably_uses_semicolons(nodes: &mut Vec<Node>, file: NodeId) -> bool {
    let with_semicolon = Cell::new(0i32);
    let without_semicolon = Cell::new(0i32);
    const N_STATEMENTS_TO_OBSERVE: i32 = 5;

    // `visit` recursively walks children; recursion needs a fn-free form, so
    // keep the counts in `Cell`s and use a plain recursive helper.
    fn visit(
        nodes: &mut Vec<Node>,
        file: NodeId,
        node: NodeId,
        with_semicolon: &Cell<i32>,
        without_semicolon: &Cell<i32>,
    ) -> bool {
        if nodes[node].flags.intersects(NodeFlags::REPARSED) {
            return false;
        }
        if syntax_requires_trailing_semicolon_or_asi(nodes[node].kind) {
            let last_token = get_last_token(nodes, Some(node), file);
            if last_token.is_some_and(|t| nodes[t].kind == Kind::SemicolonToken) {
                with_semicolon.set(with_semicolon.get() + 1);
            } else {
                without_semicolon.set(without_semicolon.get() + 1);
            }
        } else if syntax_requires_trailing_comma_or_semicolon_or_asi(nodes[node].kind) {
            let last_token = get_last_token(nodes, Some(node), file);
            if last_token.is_some_and(|t| nodes[t].kind == Kind::SemicolonToken) {
                with_semicolon.set(with_semicolon.get() + 1);
            } else if last_token.is_some_and(|t| nodes[t].kind != Kind::CommaToken) {
                let last_token = last_token.unwrap();
                // `get_start_of_node` needs `&mut Vec<Node>`; pull the source
                // file refs after it returns to avoid overlapping borrows.
                let last_token_start =
                    get_start_of_node(nodes, file, last_token, false /* includeJSDoc */);
                let last_token_line =
                    get_ecma_line_of_position(nodes[file].as_source_file(), last_token_start);
                let next_token_line = get_ecma_line_of_position(
                    nodes[file].as_source_file(),
                    skip_trivia(&nodes[file].as_source_file().text, nodes[last_token].end()),
                );
                // Avoid counting missing semicolon in single-line objects:
                // `function f(p: { x: string /*no semicolon here is insignificant*/ }) {`
                if last_token_line != next_token_line {
                    without_semicolon.set(without_semicolon.get() + 1);
                }
            }
        }

        if with_semicolon.get() + without_semicolon.get() >= N_STATEMENTS_TO_OBSERVE {
            return true;
        }

        // `node.ForEachChild(visit)` — the iterator borrows `&nodes` while
        // `visit` needs `&mut Vec<Node>`, so collect the child ids first and
        // stop early like Go's forEachChild when `visit` returns true.
        let mut children: Vec<NodeId> = Vec::new();
        nodes[node].for_each_child(nodes, &mut |child| {
            children.push(child);
            false
        });
        for child in children {
            if visit(nodes, file, child, with_semicolon, without_semicolon) {
                return true;
            }
        }
        false
    }

    // `file.ForEachChild(visit)` — same collected-children pattern.
    let mut file_children: Vec<NodeId> = Vec::new();
    nodes[file].for_each_child(nodes, &mut |child| {
        file_children.push(child);
        false
    });
    for child in file_children {
        if visit(nodes, file, child, &with_semicolon, &without_semicolon) {
            break;
        }
    }

    // One statement missing a semicolon isn't sufficient evidence to say the user
    // doesn't want semicolons, because they may not even be done writing that statement.
    if with_semicolon.get() == 0 && without_semicolon.get() <= 1 {
        return true;
    }

    // When both kinds of observation exist, treat the file as using semicolons when the
    // ratio withSemicolon/withoutSemicolon exceeds 1/nStatementsToObserve (real arithmetic),
    // implemented as an integer inequality to avoid truncation.
    if without_semicolon.get() == 0 {
        return true;
    }
    with_semicolon.get() * N_STATEMENTS_TO_OBSERVE > without_semicolon.get()
}

/// `compiler.Program` is not yet ported; this trait is the
/// `program.UsesUriStyleNodeCoreModules()` dependency of
/// `ShouldUseUriStyleNodeCoreModules` — a future `compiler::Program` can
/// implement it directly.
///
/// PORT(deferred): tsc/internal/compiler/program.go:268 — `Program` is not
/// ported yet, so callers pass the `Tristate` through this trait (or `Some` /
/// a plain value via `UsesUriStyleNodeCoreModulesValue`).
pub trait UsesUriStyleNodeCoreModules {
    /// `program.UsesUriStyleNodeCoreModules()`
    fn uses_uri_style_node_core_modules(&self) -> Tristate;
}

/// Trivial `UsesUriStyleNodeCoreModules` over a plain `Tristate` so callers
/// without a Program can still supply the flag.
impl UsesUriStyleNodeCoreModules for Tristate {
    fn uses_uri_style_node_core_modules(&self) -> Tristate {
        *self
    }
}

/// `ShouldUseUriStyleNodeCoreModules`.
pub fn should_use_uri_style_node_core_modules(
    nodes: &[Node],
    file: NodeId,
    program: &dyn UsesUriStyleNodeCoreModules,
) -> Tristate {
    for &node in nodes[file].as_source_file().imports() {
        let text = nodes[node].text(nodes);
        if NODE_CORE_MODULES.contains(&*text)
            && !EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES.contains(&*text)
        {
            if text.starts_with("node:") {
                return Tristate::True;
            } else {
                return Tristate::False;
            }
        }
    }

    program.uses_uri_style_node_core_modules()
}

/// `QuotePreferenceFromString`.
pub fn quote_preference_from_string(nodes: &[Node], str_: NodeId) -> QuotePreference {
    if nodes[str_]
        .as_string_literal()
        .literal_expression_base
        .literal_like_node_base
        .token_flags
        .intersects(TokenFlags::SINGLE_QUOTE)
    {
        return QuotePreference::SINGLE;
    }
    QuotePreference::DOUBLE
}

/// `GetQuotePreference`.
pub fn get_quote_preference(
    nodes: &[Node],
    source_file: NodeId,
    preferences: &UserPreferences,
) -> QuotePreference {
    if !preferences.quote_preference.0.is_empty()
        && preferences.quote_preference.0.as_ref() != "auto"
    {
        if preferences.quote_preference.0.as_ref() == "single" {
            return QuotePreference::SINGLE;
        }
        return QuotePreference::DOUBLE;
    }
    // ignore synthetic import added when importHelpers: true
    let first_module_specifier = find(nodes[source_file].as_source_file().imports(), |&n| {
        ast::is_string_literal(&nodes[n])
            && nodes[n]
                .parent
                .is_some_and(|p| !ast::node_is_synthesized(&nodes[p]))
    });
    if let Some(first_module_specifier) = first_module_specifier {
        return quote_preference_from_string(nodes, first_module_specifier);
    }
    QuotePreference::DOUBLE
}

/// `ModuleSymbolToValidIdentifier`.
pub fn module_symbol_to_valid_identifier(symbol: &ast::Symbol, force_capitalize: bool) -> String {
    let mut module_name = symbol.name.clone();
    if let Some(ambient_module_name) =
        ast::try_get_ambient_module_name_from_symbol_name(&module_name)
    {
        module_name = ambient_module_name.into();
    }
    module_specifier_to_valid_identifier(&module_name, force_capitalize)
}

/// `ModuleSpecifierToValidIdentifier`.
pub fn module_specifier_to_valid_identifier(
    module_specifier: &str,
    force_capitalize: bool,
) -> String {
    let stripped = remove_any_file_extension(module_specifier);
    let stripped = stripped.strip_suffix("/index").unwrap_or(&stripped);
    let base_name = get_base_file_name(stripped);
    let mut res: Vec<char> = Vec::new();
    let mut last_char_was_valid = true;
    let base_name_runes: Vec<char> = base_name.chars().collect();
    if !base_name_runes.is_empty() && is_identifier_start(base_name_runes[0] as i32) {
        if force_capitalize {
            res.push(crate::unicode::char_to_upper(base_name_runes[0]));
        } else {
            res.push(base_name_runes[0]);
        }
    } else {
        last_char_was_valid = false;
    }

    for i in 1..base_name_runes.len() {
        let is_valid = is_identifier_part(base_name_runes[i] as i32);
        if is_valid {
            if !last_char_was_valid {
                res.push(crate::unicode::char_to_upper(base_name_runes[i]));
            } else {
                res.push(base_name_runes[i]);
            }
        }
        last_char_was_valid = is_valid;
    }

    // Need `"_"` to ensure result isn't empty.
    let res_string: String = res.into_iter().collect();
    if !res_string.is_empty() && !is_non_contextual_keyword(string_to_token(&res_string)) {
        return res_string;
    }
    format!("_{res_string}")
}

/// `IsNonContextualKeyword`.
pub fn is_non_contextual_keyword(token: Kind) -> bool {
    token.is_keyword_kind() && !ast::is_contextual_keyword(token)
}
