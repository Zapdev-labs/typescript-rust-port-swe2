// Ported from tsc/internal/testutil/tsbaseline/type_symbol_baseline.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `typeWriterWalker.currentSourceFile` is a `NodeId` resolved through
// `program.nodes(file.file_index)` borrows rather than a `*ast.SourceFile`
// pointer; `declarationTextCache` is keyed by `NodeId` (Go's `*ast.Node`
// identity). `t.Run("type"/"symbol")` subtests flatten into sequential
// calls. Go's unused `skipTypeBaselines`/`skipSymbolBaselines` parameters
// are kept for signature parity.

use std::fmt::Write as _;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, Node, NodeId};
use tsc_checker::types::{TypeFormatFlags, TypeId};
use tsc_compiler::program::ProgramLike;
use tsc_core::context::Context;
use tsc_nodebuilder::{Flags, InternalFlags};
use tsc_printer::{self as printer, EmitTextWriter};
use tsc_scanner::scanner;
use tsc_scanner::utilities::{get_source_text_of_node_from_source_file, is_intrinsic_jsx_name};
use tsc_tspath as tspath;

use super::error_baseline::ts_extension_replace;
use super::util::{
    is_bracket_line, is_default_library_file, remove_test_path_prefixes, split_code_lines,
    strip_line_delimiters,
};
use crate::baseline;
use crate::harnessutil::TestFile;

/// `DoTypeAndSymbolBaseline`.
///
// PORT: `skipTypeBaselines`/`skipSymbolBaselines` are accepted but unused,
// exactly as in Go.
#[allow(clippy::too_many_arguments)]
pub fn do_type_and_symbol_baseline(
    baseline_path: &str,
    header: &str,
    program: &Rc<dyn ProgramLike>,
    all_files: &[TestFile],
    opts: baseline::Options,
    _skip_type_baselines: bool,
    _skip_symbol_baselines: bool,
    has_error_baseline: bool,
) {
    // The full walker simulates the types that you would get from doing a full
    // compile.  The pull walker simulates the types you get when you just do
    // a type query for a random node (like how the LS would do it).  Most of the
    // time, these will be the same.  However, occasionally, they can be different.
    // Specifically, when the compiler internally depends on symbol IDs to order
    // things, then we may see different results because symbols can be created in a
    // different order with 'pull' operations, and thus can produce slightly differing
    // output.
    //
    // For example, with a full type check, we may see a type displayed as: number | string
    // But with a pull type check, we may see it as:                        string | number
    //
    // These types are equivalent, but depend on what order the compiler observed
    // certain parts of the program.

    let mut full_walker = TypeWriterWalker::new(program.clone(), has_error_baseline);

    // `t.Run("type", ...)` — `defer testutil.RecoverAndFail(...)` is folded
    // into the panic itself.
    {
        // !!! Remove once the type baselines print node reuse lines
        let mut types_opts = baseline::Options {
            subfolder: opts.subfolder.clone(),
            diff_fixup_new: None,
            skip_diff_with_old: opts.skip_diff_with_old,
            diff_fixup_old: Some(Box::new(|s: &str| {
                let mut sb = String::with_capacity(s.len());
                let mut perf_stats = false;
                for line in s.split('\n') {
                    if is_type_baseline_node_reuse_line(line) {
                        continue;
                    }
                    if !perf_stats && line.starts_with("=== Performance Stats ===") {
                        perf_stats = true;
                        continue;
                    } else if perf_stats {
                        if line.starts_with("=== ") {
                            perf_stats = false;
                        } else {
                            continue;
                        }
                    }
                    // `=== ./x` -> `=== x`
                    let line = match line.strip_prefix("=== ./") {
                        Some(rest) => format!("=== {rest}"),
                        None => line.to_string(),
                    };
                    let _ = writeln!(sb, "{line}");
                }
                sb.pop(); // trailing '\n' — Go: `sb.String()[:sb.Len()-1]`
                sb
            })),
        };
        check_baselines(
            baseline_path,
            all_files,
            &mut full_walker,
            header,
            std::mem::take(&mut types_opts),
            false, // isSymbolBaseline
        );
    }
    // `t.Run("symbol", ...)`.
    check_baselines(
        baseline_path,
        all_files,
        &mut full_walker,
        header,
        opts,
        true,
    );
}

/// `isTypeBaselineNodeReuseLine`.
fn is_type_baseline_node_reuse_line(line: &str) -> bool {
    let Some(line) = line.strip_prefix('>') else {
        return false;
    };
    let Some(line) = line.trim_start_matches(' ').strip_prefix(':') else {
        return false;
    };
    line.chars().all(|c| matches!(c, ' ' | '^' | '\r'))
}

/// `checkBaselines`.
fn check_baselines(
    baseline_path: &str,
    all_files: &[TestFile],
    full_walker: &mut TypeWriterWalker,
    header: &str,
    opts: baseline::Options,
    is_symbol_baseline: bool,
) {
    let full_extension = if is_symbol_baseline {
        ".symbols"
    } else {
        ".types"
    };
    let output_file_name = ts_extension_replace(baseline_path, full_extension);
    let full_baseline = generate_baseline(all_files, full_walker, header, is_symbol_baseline);
    baseline::run(&output_file_name, &full_baseline, &opts).unwrap_or_else(|e| panic!("{e}"));
}

/// `generateBaseline`.
fn generate_baseline(
    all_files: &[TestFile],
    full_walker: &mut TypeWriterWalker,
    header: &str,
    is_symbol_baseline: bool,
) -> String {
    let mut result = String::new();
    // !!! Perf baseline
    let perf_lines: Vec<String> = Vec::new();
    // prePerformanceValues := getPerformanceBaselineValues()
    let baselines = iterate_baseline(all_files, full_walker, is_symbol_baseline);
    for value in &baselines {
        result.push_str(value);
    }
    // postPerformanceValues := getPerformanceBaselineValues()

    if !is_symbol_baseline {
        // !!! Perf baselines
    }

    if !result.is_empty() {
        return format!(
            "//// [{header}] ////\r\n\r\n{}{}",
            perf_lines.join("\n"),
            result
        );
    }
    baseline::NO_CONTENT.to_string()
}

/// `iterateBaseline`.
fn iterate_baseline(
    all_files: &[TestFile],
    full_walker: &mut TypeWriterWalker,
    is_symbol_baseline: bool,
) -> Vec<String> {
    let mut baselines = Vec::new();

    for file in all_files {
        let unit_name = &file.unit_name;
        let mut type_lines = String::new();
        let _ = write!(type_lines, "=== {unit_name} ===\r\n");
        let code_lines = split_code_lines(&file.content);
        let results = if is_symbol_baseline {
            full_walker.get_symbols(unit_name)
        } else {
            full_walker.get_types(unit_name)
        };
        let mut last_index_written: i64 = -1;
        for result in &results {
            if is_symbol_baseline && result.symbol.is_empty() {
                return baselines;
            }
            if last_index_written == -1 {
                type_lines.push_str(&code_lines[..result.line as usize + 1].join("\r\n"));
                type_lines.push_str("\r\n");
            } else if last_index_written != result.line as i64 {
                let next = last_index_written as usize + 1;
                if !(next < code_lines.len()
                    && (is_bracket_line(code_lines[next]) || code_lines[next].trim().is_empty()))
                {
                    type_lines.push_str("\r\n");
                }
                type_lines.push_str(&code_lines[next..result.line as usize + 1].join("\r\n"));
                type_lines.push_str("\r\n");
            }
            last_index_written = result.line as i64;
            let type_or_symbol_string = if is_symbol_baseline {
                &result.symbol
            } else {
                &result.typ
            };
            let line_text = strip_line_delimiters(&result.source_text);
            type_lines.push('>');
            let _ = write!(type_lines, "{line_text} : {type_or_symbol_string}");
            type_lines.push_str("\r\n");
            if !result.underline.is_empty() {
                type_lines.push('>');
                for _ in 0..line_text.len() {
                    type_lines.push(' ');
                }
                type_lines.push_str(" : ");
                type_lines.push_str(&result.underline);
                type_lines.push_str("\r\n");
            }
        }

        if last_index_written + 1 < code_lines.len() as i64 {
            let next = (last_index_written + 1) as usize;
            if !(next < code_lines.len()
                && (is_bracket_line(code_lines[next]) || code_lines[next].trim().is_empty()))
            {
                type_lines.push_str("\r\n");
            }
            type_lines.push_str(&code_lines[next..].join("\r\n"));
        }
        type_lines.push_str("\r\n");

        baselines.push(remove_test_path_prefixes(&type_lines, false));
    }

    baselines
}

/// `typeWriterWalker`.
struct TypeWriterWalker {
    program: Rc<dyn ProgramLike>,
    had_error_baseline: bool,
    /// `currentSourceFile *ast.SourceFile` — the source file's `NodeId`.
    current_source_file: NodeId,
    /// `declarationTextCache` — `map[*ast.Node]string` keyed by `NodeId`.
    declaration_text_cache: FxHashMap<NodeId, String>,
}

/// `typeWriterResult`.
struct TypeWriterResult {
    line: i32,
    source_text: String,
    symbol: String,
    typ: String,
    underline: String,
}

impl TypeWriterWalker {
    /// `newTypeWriterWalker`.
    fn new(program: Rc<dyn ProgramLike>, had_error_baseline: bool) -> TypeWriterWalker {
        TypeWriterWalker {
            program,
            had_error_baseline,
            current_source_file: NodeId::NONE,
            declaration_text_cache: FxHashMap::default(),
        }
    }

    /// `getTypeCheckerForCurrentFile`.
    fn get_type_checker_for_current_file(
        &self,
    ) -> (
        Rc<std::cell::RefCell<tsc_checker::checker_core::Checker>>,
        tsc_compiler::checker_pool::DoneFn,
    ) {
        // If we don't use the right checker for the file, its contents won't be up to date
        // since the types/symbols baselines appear to depend on files having been checked.
        self.program
            .program()
            .get_type_checker_for_file(Context::background(), self.current_source_file)
    }

    /// `(walker) getTypes`.
    fn get_types(&mut self, filename: &str) -> Vec<TypeWriterResult> {
        let source_file = self.program.get_source_file(&tspath::to_rooted_file_path(
            filename,
            &self.program.program().base_directory(),
        ));
        let Some(source_file) = source_file else {
            return Vec::new();
        };
        self.current_source_file = source_file;
        self.visit_node(source_file, false /*isSymbolWalk*/)
    }

    /// `(walker) getSymbols`.
    fn get_symbols(&mut self, filename: &str) -> Vec<TypeWriterResult> {
        let source_file = self.program.get_source_file(&tspath::to_rooted_file_path(
            filename,
            &self.program.program().base_directory(),
        ));
        let Some(source_file) = source_file else {
            return Vec::new();
        };
        self.current_source_file = source_file;
        self.visit_node(source_file, true /*isSymbolWalk*/)
    }

    /// `(walker) visitNode`.
    fn visit_node(&mut self, node: NodeId, is_symbol_walk: bool) -> Vec<TypeWriterResult> {
        let nodes = for_each_ast_node(&self.program, node);
        let mut results = Vec::new();
        for n in nodes {
            let eligible = {
                let prog = self.program.program();
                let arena = prog.nodes(n.file_index());
                let node_ref = &arena[n];
                let parent = node_ref.parent;
                ast::is_expression_node(n, &arena)
                    || node_ref.kind == ast::Kind::Identifier
                    || ast::is_declaration_name(n, &arena)
                    || (ast::is_qualified_name(node_ref)
                        && ast::is_name_of_heritage_clause_type_reference(n, &arena)
                        && (is_symbol_walk
                            || parent.is_some_and(|p| ast::is_qualified_name(&arena[p]))))
            };
            if eligible {
                if let Some(result) = self.write_type_or_symbol(n, is_symbol_walk) {
                    results.push(result);
                }
            }
        }
        results
    }

    /// `(walker) writeTypeOrSymbol`.
    fn write_type_or_symbol(
        &mut self,
        node: NodeId,
        is_symbol_walk: bool,
    ) -> Option<TypeWriterResult> {
        let prog = self.program.program();
        let file_index = self.current_source_file.file_index();
        let (line, source_text) = {
            let nodes = prog.nodes(file_index);
            let sf = nodes[self.current_source_file].as_source_file();
            let actual_pos = scanner::skip_trivia(sf.text(), nodes[node].pos());
            let line = scanner::get_ecma_line_of_position(sf, actual_pos);
            let source_text = get_source_text_of_node_from_source_file(
                sf, node, false, /*includeTrivia*/
                &nodes,
            )
            .into_owned();
            (line, source_text)
        };
        let (file_checker, done) = self.get_type_checker_for_current_file();
        let mut file_checker = file_checker.borrow_mut();

        if !is_symbol_walk {
            // Don't try to get the type of something that's already a type.
            // Exception for `T` in `type T = something` because that may evaluate to some interesting type.
            let skip = {
                let nodes = prog.nodes(file_index);
                let parent = nodes[node].parent;
                let parent_is_alias_name_decl = parent.is_some_and(|p| {
                    (ast::is_type_alias_declaration(&nodes[p])
                        || ast::is_js_type_alias_declaration(&nodes[p]))
                        && nodes[p].name() == Some(node)
                });
                ast::is_part_of_type_node(node, &nodes)
                    || ((nodes[node].kind == ast::Kind::AsExpression
                        || nodes[node].kind == ast::Kind::SatisfiesExpression)
                        && nodes[node]
                            .type_()
                            .is_some_and(|t| nodes[t].flags.intersects(ast::NodeFlags::REPARSED)))
                    || (ast::is_identifier(&nodes[node])
                        && parent.is_some_and(|p| {
                            (ast::get_meaning_from_declaration(&nodes[p], &nodes)
                                & ast::SemanticMeaning::VALUE)
                                == ast::SemanticMeaning::NONE
                        })
                        && !parent_is_alias_name_decl)
            };
            if skip {
                done();
                return None;
            }
            if ast::is_omitted_expression(&prog.nodes(file_index)[node]) {
                done();
                return None;
            }

            // Workaround to ensure we output 'C' instead of 'typeof C' for base class expressions
            let mut t = TypeId::NONE;
            {
                let nodes = prog.nodes(file_index);
                if nodes[node].parent.is_some_and(|p| {
                    ast::is_expression_with_type_arguments_in_class_extends_clause(p, &nodes)
                }) {
                    drop(nodes);
                    t = file_checker
                        .get_type_at_location(prog.nodes(file_index)[node].parent.unwrap());
                }
            }
            if t.is_none() || tsc_checker::types::is_type_any(&file_checker.types, t) {
                t = file_checker.get_type_at_location(node);
            }
            let type_string: String;
            // var underline string
            let intrinsic_short_circuit = !self.had_error_baseline
                && tsc_checker::types::is_type_any(&file_checker.types, t)
                && {
                    let nodes = prog.nodes(file_index);
                    let parent = nodes[node].parent;
                    !parent.is_some_and(|p| ast::is_binding_element(&nodes[p]))
                        && !parent
                            .is_some_and(|p| ast::is_property_access_or_qualified_name(&nodes[p]))
                        && !ast::is_label_name(node, &nodes)
                        && !parent.is_some_and(|p| ast::is_global_scope_augmentation(&nodes[p]))
                        && !parent.is_some_and(|p| ast::is_meta_property(&nodes[p]))
                        && !is_import_statement_name(&nodes[node], &nodes, node)
                        && !is_export_statement_name(&nodes[node], &nodes, node)
                        && !self.is_intrinsic_jsx_tag(node, &nodes)
                };
            if intrinsic_short_circuit {
                type_string = file_checker
                    .types
                    .get(t)
                    .as_intrinsic_type()
                    .intrinsic_name()
                    .to_string();
            } else {
                let mut builder = tsc_checker::nodebuilder::new_node_builder(
                    &file_checker,
                    printer::EmitContext::new(),
                );
                let type_format_flags = TypeFormatFlags::NO_TRUNCATION
                    | TypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
                    | TypeFormatFlags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS;
                let parent = prog.nodes(file_index)[node].parent;
                // `arena_checkout` (not `nodes_mut`): the builder reads the
                // arena re-entrantly through `program.nodes`, which an
                // exclusive `nodes_mut` checkout would render empty.
                let mut nodes = prog.arena_checkout(file_index);
                let mut type_node = builder.type_to_type_node(
                    &mut file_checker,
                    &mut nodes,
                    t,
                    parent,
                    Flags(type_format_flags.0 & TypeFormatFlags::NODE_BUILDER_FLAGS_MASK.0)
                        | Flags::IGNORE_ERRORS,
                    InternalFlags::ALLOW_UNRESOLVED_NAMES,
                    None,
                );
                let node_is_alias_name = ast::is_identifier(&nodes[node])
                    && parent.is_some_and(|p| {
                        ast::is_type_alias_declaration(&nodes[p]) && nodes[p].name() == Some(node)
                    });
                if node_is_alias_name
                    && type_node.is_some_and(|tn| {
                        ast::is_identifier(&nodes[tn])
                            && nodes[tn].as_identifier().text == nodes[node].as_identifier().text
                    })
                {
                    // for a complex type alias `type T = ...`, showing "T : T" isn't very helpful for type tests. When the type produced is the same as
                    // the name of the type alias, recreate the type string without reusing the alias name
                    type_node = builder.type_to_type_node(
                        &mut file_checker,
                        &mut nodes,
                        t,
                        parent,
                        Flags(
                            (type_format_flags.0 | TypeFormatFlags::IN_TYPE_ALIAS.0)
                                & TypeFormatFlags::NODE_BUILDER_FLAGS_MASK.0,
                        ) | Flags::IGNORE_ERRORS,
                        InternalFlags::ALLOW_UNRESOLVED_NAMES,
                        None,
                    );
                }

                // !!! TODO: port underline printer, memoize
                let mut writer = printer::TextWriter::new("", 0);
                let symbols = file_checker.symbol_arena.clone();
                let symbols = symbols.clone();
                {
                    let emit_context_cell = builder.emit_context();
                    let mut emit_context = emit_context_cell.borrow_mut();
                    let mut printer = printer::Printer::new(
                        printer::PrinterOptions {
                            remove_comments: true,
                            ..Default::default()
                        },
                        printer::PrintHandlers::default(),
                        &mut emit_context,
                        &mut nodes,
                        &symbols,
                    );
                    tsc_checker::printer_util::install_foreign_comma_hook(
                        &mut printer,
                        file_checker.program.as_ref().expect("program"),
                    );
                    printer.write(type_node, Some(self.current_source_file), &mut writer, None);
                }
                type_string = writer.get_text();
            }
            done();
            return Some(TypeWriterResult {
                line,
                source_text,
                symbol: String::new(),
                typ: type_string,
                underline: String::new(), // !!! TODO: underline
            });
        }

        let symbol = file_checker.get_symbol_at_location_api(node);
        let Some(symbol) = symbol else {
            done();
            return None;
        };

        let mut symbol_string = String::with_capacity(256);
        symbol_string.push_str("Symbol(");
        symbol_string.push_str(&ast::escape_all_internal_symbol_names(
            &file_checker.symbol_to_string_ex(
                symbol,
                prog.nodes(file_index)[node].parent,
                ast::SymbolFlags::NONE,
                tsc_checker::types::SymbolFormatFlags::ALLOW_ANY_NODE_KIND,
                None,
            ),
        ));
        let mut count = 0;
        let declarations = file_checker.symbol_arena.get_ref(symbol)
            .declarations
            .clone();
        for &declaration in &declarations {
            if count >= 5 {
                let _ = write!(
                    symbol_string,
                    " ... and {} more",
                    declarations.len() - count
                );
                break;
            }
            count += 1;
            symbol_string.push_str(", ");
            if let Some(decl_text) = self.declaration_text_cache.get(&declaration) {
                symbol_string.push_str(decl_text);
                continue;
            }

            let (decl_line, decl_char, file_name) = {
                let decl_nodes = prog.arena_of(declaration);
                let decl_source_file = ast::get_source_file_of_node(Some(declaration), &decl_nodes);
                let (decl_line, decl_char) = match decl_source_file {
                    Some(sf) => {
                        let sf_ref = decl_nodes[sf].as_source_file();
                        scanner::get_ecma_line_and_utf16_character_of_position(
                            sf_ref,
                            decl_nodes[declaration].pos(),
                        )
                    }
                    None => (0, 0),
                };
                let file_name = decl_source_file
                    .map(|sf| {
                        tspath::get_base_file_name(
                            decl_nodes[sf].as_source_file().file_name().as_string(),
                        )
                        .into_owned()
                    })
                    .unwrap_or_default();
                (decl_line, decl_char, file_name)
            };
            symbol_string.push_str("Decl(");
            symbol_string.push_str(&file_name);
            symbol_string.push_str(", ");
            if is_default_library_file(&file_name) {
                symbol_string.push_str("--, --)");
            } else {
                let _ = write!(symbol_string, "{decl_line}, {decl_char})");
            }
        }
        symbol_string.push(')');
        done();
        Some(TypeWriterResult {
            line,
            source_text,
            symbol: symbol_string,
            typ: String::new(),
            underline: String::new(),
        })
    }

    /// `isIntrinsicJsxTag` — needs `current_source_file` text; arena passed
    /// in to reuse the caller's borrow.
    fn is_intrinsic_jsx_tag(&self, node: NodeId, nodes: &[Node]) -> bool {
        let parent = match nodes[node].parent {
            Some(p) => p,
            None => return false,
        };
        if !(ast::is_jsx_opening_element(&nodes[parent])
            || ast::is_jsx_closing_element(&nodes[parent])
            || ast::is_jsx_self_closing_element(&nodes[parent]))
        {
            return false;
        }
        if nodes[parent].tag_name() != Some(node) {
            return false;
        }
        let sf = nodes[self.current_source_file].as_source_file();
        let text = get_source_text_of_node_from_source_file(sf, node, false, nodes);
        is_intrinsic_jsx_name(&text)
    }
}

/// `forEachASTNode` — depth-first, reparsed-node-skipping traversal.
fn for_each_ast_node(program: &Rc<dyn ProgramLike>, node: NodeId) -> Vec<NodeId> {
    let mut result = Vec::new();
    let mut work = vec![node];
    let prog = program.program();
    let arena = prog.arena_of(node);
    let nodes: &[Node] = &arena;

    while let Some(elem) = work.pop() {
        let e = &nodes[elem];
        let e_is_reparsed = e.flags.intersects(ast::NodeFlags::REPARSED);
        let e_is_as_or_satisfies =
            e.kind == ast::Kind::AsExpression || e.kind == ast::Kind::SatisfiesExpression;
        let parent_is_as_or_satisfies = e.parent.is_some_and(|p| {
            let p = &nodes[p];
            p.kind == ast::Kind::SatisfiesExpression || p.kind == ast::Kind::AsExpression
        });
        // PORT(borrowck): Go's `||` chain is lazy — `elem.Parent.Expression()`
        // only runs when the earlier terms fail (and `Parent` can be the
        // SourceFile, whose `Expression()` panics), so keep it lazy here too.
        let is_parent_expression = || {
            e.parent
                .is_some_and(|p| nodes[p].expression() == Some(elem))
        };
        if !e_is_reparsed || e_is_as_or_satisfies || (parent_is_as_or_satisfies
            && is_parent_expression())
        {
            if !e_is_reparsed || parent_is_as_or_satisfies {
                result.push(elem);
            }
            let mut res_children: Vec<NodeId> = Vec::new();
            e.for_each_child(nodes, &mut |child| {
                res_children.push(child);
                false
            });
            res_children.reverse();
            work.extend(res_children);
        }
    }
    result
}

/// `isImportStatementName`.
fn is_import_statement_name(node: &Node, nodes: &[Node], node_id: NodeId) -> bool {
    let Some(parent) = node.parent else {
        return false;
    };
    let parent_node = &nodes[parent];
    if ast::is_import_specifier(parent_node)
        && (parent_node.name() == Some(node_id) || parent_node.property_name() == Some(node_id))
    {
        return true;
    }
    if ast::is_import_clause(parent_node) && parent_node.name() == Some(node_id) {
        return true;
    }
    if ast::is_import_equals_declaration(parent_node) && parent_node.name() == Some(node_id) {
        return true;
    }
    false
}

/// `isExportStatementName`.
fn is_export_statement_name(node: &Node, nodes: &[Node], node_id: NodeId) -> bool {
    let Some(parent) = node.parent else {
        return false;
    };
    let parent_node = &nodes[parent];
    if ast::is_export_assignment(parent_node) && parent_node.expression() == Some(node_id) {
        return true;
    }
    if ast::is_export_specifier(parent_node)
        && (parent_node.name() == Some(node_id) || parent_node.property_name() == Some(node_id))
    {
        return true;
    }
    false
}
