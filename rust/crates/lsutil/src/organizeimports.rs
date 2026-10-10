// Ported from tsc/internal/ls/lsutil/organizeimports.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.
//
// PORT(global): Go `func(a, b string) int` comparers are boxed
// `StringComparer` closures; `func(s1, s2 *ast.Node) int` specifier comparers
// are `SpecifierComparer`s that take the node arena explicitly.
// `golang.org/x/text/unicode/norm` is unicode-normalization's `nfd()`;
// `unicode.Is(unicode.Mn)`, `unicode.IsUpper` and `strings.Compare`/`ToLower`
// go through the crate's Go-stdlib-faithful `unicode` module.

use std::rc::Rc;

use unicode_normalization::UnicodeNormalization;

use tsc_ast::ast::Node;
use tsc_ast::{self as ast, Kind, NodeId};
use tsc_core::binarysearch::binary_search_unique_func;
use tsc_core::core::{compare_booleans, filter, first_result};
use tsc_core::tristate::Tristate;
use tsc_stringutil::{
    compare_strings_case_insensitive_eslint_compatible, compare_strings_case_sensitive,
};
use tsc_tspath::is_external_module_name_relative;

use crate::unicode::{is_mn, is_upper, strings_to_lower};
use crate::userpreferences::{
    OrganizeImportsCaseFirst, OrganizeImportsCollation, OrganizeImportsSort,
    OrganizeImportsTypeOrder,
};
use crate::userpreferences_generated::UserPreferences;

/// `func(a, b string) int` — Go function values are shared cheaply, so the
/// port stores `Rc<StringComparer>` and calls `cmp(a, b)` through `&*rc`.
pub type StringComparer = dyn Fn(&str, &str) -> i32;
/// `func(s1, s2 *ast.Node) int` — needs the node arena for `.Name().Text()`.
pub type SpecifierComparer = dyn Fn(&[Node], NodeId, NodeId) -> i32;
/// `func(s1, s2 *ast.Statement) int`.
pub type StatementComparer = dyn Fn(&[Node], NodeId, NodeId) -> i32;

/// `strings.Compare`
fn compare_strings(a: &str, b: &str) -> i32 {
    a.cmp(b) as i32
}

/// `FilterImportDeclarations` filters out non-import declarations from a list of statements.
pub fn filter_import_declarations<'a>(
    nodes: &[Node],
    statements: &'a [NodeId],
) -> std::borrow::Cow<'a, [NodeId]> {
    filter(statements, |stmt| {
        nodes[*stmt].kind == Kind::ImportDeclaration
    })
}

/// `GetDetectionLists` returns the lists of comparers and type orders to test
/// for organize imports detection.
pub fn get_detection_lists(
    preferences: &UserPreferences,
) -> (Vec<Rc<StringComparer>>, Vec<OrganizeImportsTypeOrder>) {
    let comparers_to_test: Vec<Rc<StringComparer>>;
    if preferences.organize_imports_sort != OrganizeImportsSort::AUTO {
        comparers_to_test = vec![get_organize_imports_preset_string_comparer(
            preferences.organize_imports_sort,
        )];
    } else if !preferences.organize_imports_ignore_case.is_unknown() {
        comparers_to_test = vec![get_organize_imports_string_comparer(
            preferences,
            preferences.organize_imports_ignore_case.is_true(),
        )];
    } else {
        comparers_to_test = vec![
            get_organize_imports_string_comparer(preferences, true),
            get_organize_imports_string_comparer(preferences, false),
        ];
    }

    let type_orders_to_test: Vec<OrganizeImportsTypeOrder>;
    if preferences.organize_imports_type_order != OrganizeImportsTypeOrder::AUTO {
        type_orders_to_test = vec![preferences.organize_imports_type_order];
    } else {
        type_orders_to_test = vec![
            OrganizeImportsTypeOrder::LAST,
            OrganizeImportsTypeOrder::INLINE,
            OrganizeImportsTypeOrder::FIRST,
        ];
    }

    (comparers_to_test, type_orders_to_test)
}

/// `ResolveOrganizeImportsSort`.
pub fn resolve_organize_imports_sort(preferences: &UserPreferences) -> OrganizeImportsSort {
    if preferences.organize_imports_sort != OrganizeImportsSort::AUTO {
        return preferences.organize_imports_sort;
    }

    if preferences.organize_imports_collation == OrganizeImportsCollation::UNICODE {
        return match preferences.organize_imports_ignore_case {
            Tristate::True => OrganizeImportsSort::NATURAL_IGNORE_CASE,
            Tristate::False => OrganizeImportsSort::NATURAL,
            _ => OrganizeImportsSort::AUTO,
        };
    }

    match preferences.organize_imports_ignore_case {
        Tristate::True => OrganizeImportsSort::ORDINAL_IGNORE_CASE,
        Tristate::False => OrganizeImportsSort::ORDINAL,
        _ => OrganizeImportsSort::AUTO,
    }
}

/// `getOrganizeImportsOrdinalStringComparer`
fn get_organize_imports_ordinal_string_comparer(ignore_case: bool) -> Rc<StringComparer> {
    if ignore_case {
        return Rc::new(|a: &str, b: &str| {
            compare_strings_case_insensitive_eslint_compatible(a.as_bytes(), b.as_bytes())
        });
    }
    Rc::new(|a: &str, b: &str| compare_strings_case_sensitive(a.as_bytes(), b.as_bytes()))
}

/// `getOrganizeImportsNaturalStringComparer`
fn get_organize_imports_natural_string_comparer(case_sensitive: bool) -> Rc<StringComparer> {
    Rc::new(move |a: &str, b: &str| compare_organize_imports_natural_strings(a, b, case_sensitive))
}

/// `getOrganizeImportsUnicodeStringComparer`
fn get_organize_imports_unicode_string_comparer(
    ignore_case: bool,
    preferences: &UserPreferences,
) -> Rc<StringComparer> {
    let case_first = preferences.organize_imports_case_first;
    let numeric = preferences.organize_imports_numeric_collation.is_true();
    let accents = !preferences.organize_imports_accent_collation.is_false();

    Rc::new(move |a: &str, b: &str| {
        compare_organize_imports_unicode_strings(a, b, ignore_case, case_first, numeric, accents)
    })
}

/// `compareOrganizeImportsNaturalStrings`.
fn compare_organize_imports_natural_strings(a: &str, b: &str, case_sensitive: bool) -> i32 {
    let c = compare_strings_numeric(&natural_collation_key(a), &natural_collation_key(b));
    if c != 0 {
        return c;
    }

    if case_sensitive {
        let c = compare_organize_imports_case_upper_first(a, b);
        if c != 0 {
            return c;
        }
    }

    compare_strings(a, b)
}

/// `compareOrganizeImportsUnicodeStrings`.
fn compare_organize_imports_unicode_strings(
    a: &str,
    b: &str,
    ignore_case: bool,
    case_first: OrganizeImportsCaseFirst,
    numeric: bool,
    accents: bool,
) -> i32 {
    let c = compare_organize_imports_unicode_keys(
        &natural_collation_key(a),
        &natural_collation_key(b),
        numeric,
    );
    if c != 0 {
        return c;
    }

    if accents {
        let c = compare_organize_imports_unicode_keys(
            &strings_to_lower(a),
            &strings_to_lower(b),
            numeric,
        );
        if c != 0 {
            return c;
        }
    }

    if !ignore_case {
        let c = compare_organize_imports_case(a, b, case_first);
        if c != 0 {
            return c;
        }
    }

    compare_strings(a, b)
}

/// `naturalCollationKey`.
fn natural_collation_key(s: &str) -> String {
    strings_to_lower(&remove_diacritics(s))
}

/// `removeDiacritics` — `strings.Map(drop Mn, norm.NFD.String(s))`.
fn remove_diacritics(s: &str) -> String {
    s.nfd().filter(|&r| !is_mn(r as i32)).collect()
}

/// `compareOrganizeImportsUnicodeKeys`.
fn compare_organize_imports_unicode_keys(a: &str, b: &str, numeric: bool) -> i32 {
    if numeric {
        return compare_strings_numeric(a, b);
    }
    compare_strings(a, b)
}

/// `compareStringsNumeric` — operates on byte prefixes like the Go loop over
/// `a[0]`/`utf8.DecodeRuneInString`; `&str` keeps rune iteration exact.
fn compare_strings_numeric(a: &str, b: &str) -> i32 {
    let mut a = a;
    let mut b = b;
    while !a.is_empty() && !b.is_empty() {
        if is_ascii_digit(a.as_bytes()[0]) && is_ascii_digit(b.as_bytes()[0]) {
            let a_run_end = ascii_digit_run_end(a);
            let b_run_end = ascii_digit_run_end(b);

            let c = compare_numeric_text(&a[..a_run_end], &b[..b_run_end]);
            if c != 0 {
                return c;
            }

            a = &a[a_run_end..];
            b = &b[b_run_end..];
            continue;
        }

        let a_rune = a.chars().next().unwrap();
        let b_rune = b.chars().next().unwrap();
        if a_rune != b_rune {
            return (a_rune as i32).cmp(&(b_rune as i32)) as i32;
        }

        a = &a[a_rune.len_utf8()..];
        b = &b[b_rune.len_utf8()..];
    }

    a.len().cmp(&b.len()) as i32
}

/// `isASCIIDigit`.
fn is_ascii_digit(ch: u8) -> bool {
    ch.is_ascii_digit()
}

/// `asciiDigitRunEnd`.
fn ascii_digit_run_end(s: &str) -> usize {
    let mut i = 0;
    while i < s.len() && is_ascii_digit(s.as_bytes()[i]) {
        i += 1;
    }
    i
}

/// `compareNumericText`.
fn compare_numeric_text(a: &str, b: &str) -> i32 {
    let a_digits = a.trim_start_matches('0');
    let b_digits = b.trim_start_matches('0');
    let a_digits = if a_digits.is_empty() { "0" } else { a_digits };
    let b_digits = if b_digits.is_empty() { "0" } else { b_digits };

    if a_digits.len() != b_digits.len() {
        return a_digits.len().cmp(&b_digits.len()) as i32;
    }
    let c = compare_strings(a_digits, b_digits);
    if c != 0 {
        return c;
    }
    compare_strings(a, b)
}

/// `compareOrganizeImportsCaseUpperFirst`.
fn compare_organize_imports_case_upper_first(a: &str, b: &str) -> i32 {
    compare_organize_imports_case(a, b, OrganizeImportsCaseFirst::UPPER)
}

/// `compareOrganizeImportsCase`.
fn compare_organize_imports_case(a: &str, b: &str, case_first: OrganizeImportsCaseFirst) -> i32 {
    let a_runes: Vec<char> = a.chars().collect();
    let b_runes: Vec<char> = b.chars().collect();
    let min_len = a_runes.len().min(b_runes.len());

    for i in 0..min_len {
        let a_upper = is_upper(a_runes[i] as i32);
        let b_upper = is_upper(b_runes[i] as i32);
        if a_upper != b_upper {
            if case_first == OrganizeImportsCaseFirst::UPPER {
                if a_upper {
                    return -1;
                }
                return 1;
            } else if case_first == OrganizeImportsCaseFirst::LOWER {
                if !a_upper {
                    return -1;
                }
                return 1;
            } else {
                if a_upper {
                    return 1;
                }
                return -1;
            }
        }
    }

    a_runes.len().cmp(&b_runes.len()) as i32
}

/// `getOrganizeImportsPresetStringComparer`.
pub fn get_organize_imports_preset_string_comparer(
    sort: OrganizeImportsSort,
) -> Rc<StringComparer> {
    match sort {
        OrganizeImportsSort::ORDINAL_IGNORE_CASE => {
            get_organize_imports_ordinal_string_comparer(true)
        }
        OrganizeImportsSort::NATURAL => get_organize_imports_natural_string_comparer(true),
        OrganizeImportsSort::NATURAL_IGNORE_CASE => {
            get_organize_imports_natural_string_comparer(false)
        }
        _ => get_organize_imports_ordinal_string_comparer(false),
    }
}

/// `getOrganizeImportsStringComparer`.
fn get_organize_imports_string_comparer(
    preferences: &UserPreferences,
    ignore_case: bool,
) -> Rc<StringComparer> {
    if preferences.organize_imports_sort != OrganizeImportsSort::AUTO {
        return get_organize_imports_preset_string_comparer(preferences.organize_imports_sort);
    }
    if preferences.organize_imports_collation == OrganizeImportsCollation::UNICODE {
        return get_organize_imports_unicode_string_comparer(ignore_case, preferences);
    }
    get_organize_imports_ordinal_string_comparer(ignore_case)
}

/// `getModuleSpecifierExpression`.
fn get_module_specifier_expression(nodes: &[Node], declaration: NodeId) -> Option<NodeId> {
    match nodes[declaration].kind {
        Kind::ImportEqualsDeclaration => {
            let import_equals = nodes[declaration].as_import_equals_declaration();
            if import_equals
                .module_reference
                .is_some_and(|mr| nodes[mr].kind == Kind::ExternalModuleReference)
            {
                return import_equals
                    .module_reference
                    .and_then(|mr| nodes[mr].expression());
            }
            None
        }
        Kind::ImportDeclaration => nodes[declaration].module_specifier(),
        Kind::VariableStatement => {
            let declarations = nodes[declaration]
                .as_variable_statement()
                .declaration_list
                .and_then(|dl| {
                    nodes[dl]
                        .as_variable_declaration_list()
                        .declarations
                        .clone()
                })
                .map(|l| l.nodes)
                .unwrap_or_default();
            if !declarations.is_empty() {
                let initializer = nodes[declarations[0]].initializer();
                if let Some(initializer) = initializer {
                    if nodes[initializer].kind == Kind::CallExpression {
                        let call_expr = nodes[initializer].as_call_expression();
                        if let Some(args) = &call_expr.arguments {
                            if !args.nodes.is_empty() {
                                return Some(args.nodes[0]);
                            }
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// `GetExternalModuleName` returns the module name from a module specifier expression.
pub fn get_external_module_name(nodes: &[Node], specifier: Option<NodeId>) -> String {
    if let Some(specifier) = specifier {
        if ast::is_string_literal_like(&nodes[specifier]) {
            return nodes[specifier].text(nodes).into_owned();
        }
    }
    String::new()
}

/// `CompareModuleSpecifiers` compares two module specifiers using the given comparer.
pub fn compare_module_specifiers(
    nodes: &[Node],
    m1: Option<NodeId>,
    m2: Option<NodeId>,
    comparer: &dyn Fn(&str, &str) -> i32,
) -> i32 {
    let name1 = get_external_module_name(nodes, m1);
    let name2 = get_external_module_name(nodes, m2);
    let c = compare_booleans(name1.is_empty(), name2.is_empty());
    if c != 0 {
        return c;
    }
    let c = compare_booleans(
        is_external_module_name_relative(&name1),
        is_external_module_name_relative(&name2),
    );
    if c != 0 {
        return c;
    }
    comparer(&name1, &name2)
}

/// `compareImportKind`.
fn compare_import_kind(s1: NodeId, s2: NodeId, nodes: &[Node]) -> i32 {
    get_import_kind_order(nodes, s1).cmp(&get_import_kind_order(nodes, s2)) as i32
}

/// `importKindOrder*` — sort order for different import kinds:
/// 1. Side-effect imports
/// 2. Type-only imports
/// 3. Namespace imports
/// 4. Default imports
/// 5. Named imports
/// 6. ImportEqualsDeclarations
/// 7. Require variable statements
const IMPORT_KIND_ORDER_SIDE_EFFECT: i32 = 0;
const IMPORT_KIND_ORDER_TYPE_ONLY: i32 = 1;
const IMPORT_KIND_ORDER_NAMESPACE: i32 = 2;
const IMPORT_KIND_ORDER_DEFAULT: i32 = 3;
const IMPORT_KIND_ORDER_NAMED: i32 = 4;
const IMPORT_KIND_ORDER_IMPORT_EQUALS: i32 = 5;
const IMPORT_KIND_ORDER_REQUIRE: i32 = 6;
const IMPORT_KIND_ORDER_UNKNOWN: i32 = 7;

/// `getImportKindOrder`.
fn get_import_kind_order(nodes: &[Node], s1: NodeId) -> i32 {
    match nodes[s1].kind {
        Kind::ImportDeclaration => {
            let import_decl = nodes[s1].as_import_declaration();
            let Some(import_clause_id) = import_decl.import_clause else {
                return IMPORT_KIND_ORDER_SIDE_EFFECT;
            };
            let import_clause = nodes[import_clause_id].as_import_clause();
            if nodes[import_clause_id].is_type_only() {
                return IMPORT_KIND_ORDER_TYPE_ONLY;
            }
            if import_clause
                .named_bindings
                .is_some_and(|nb| nodes[nb].kind == Kind::NamespaceImport)
            {
                return IMPORT_KIND_ORDER_NAMESPACE;
            }
            if nodes[import_clause_id].name().is_some() {
                return IMPORT_KIND_ORDER_DEFAULT;
            }
            IMPORT_KIND_ORDER_NAMED
        }
        Kind::ImportEqualsDeclaration => IMPORT_KIND_ORDER_IMPORT_EQUALS,
        Kind::VariableStatement => IMPORT_KIND_ORDER_REQUIRE,
        _ => IMPORT_KIND_ORDER_UNKNOWN,
    }
}

/// `CompareImportsOrRequireStatements` compares two import or require statements.
pub fn compare_imports_or_require_statements(
    nodes: &[Node],
    s1: NodeId,
    s2: NodeId,
    comparer: &dyn Fn(&str, &str) -> i32,
) -> i32 {
    let c = compare_module_specifiers(
        nodes,
        get_module_specifier_expression(nodes, s1),
        get_module_specifier_expression(nodes, s2),
        comparer,
    );
    if c != 0 {
        return c;
    }
    compare_import_kind(s1, s2, nodes)
}

/// `compareImportOrExportSpecifiers`.
fn compare_import_or_export_specifiers(
    nodes: &[Node],
    s1: NodeId,
    s2: NodeId,
    comparer: &dyn Fn(&str, &str) -> i32,
    preferences: &UserPreferences,
) -> i32 {
    let type_order = preferences.organize_imports_type_order;

    let s1_name = nodes[nodes[s1].name().unwrap()].text(nodes).into_owned();
    let s2_name = nodes[nodes[s2].name().unwrap()].text(nodes).into_owned();

    if type_order == OrganizeImportsTypeOrder::FIRST {
        let c = compare_booleans(nodes[s2].is_type_only(), nodes[s1].is_type_only());
        if c != 0 {
            return c;
        }
        comparer(&s1_name, &s2_name)
    } else if type_order == OrganizeImportsTypeOrder::INLINE {
        comparer(&s1_name, &s2_name)
    } else {
        // OrganizeImportsTypeOrderLast
        let c = compare_booleans(nodes[s1].is_type_only(), nodes[s2].is_type_only());
        if c != 0 {
            return c;
        }
        comparer(&s1_name, &s2_name)
    }
}

/// `GetNamedImportSpecifierComparer` returns a comparer function for sorting
/// import specifiers.
pub fn get_named_import_specifier_comparer(
    preferences: &UserPreferences,
    comparer: Option<Rc<StringComparer>>,
) -> Rc<SpecifierComparer> {
    let comparer = comparer.unwrap_or_else(|| {
        let ignore_case = if !preferences.organize_imports_ignore_case.is_unknown() {
            preferences.organize_imports_ignore_case.is_true()
        } else {
            false
        };
        get_organize_imports_string_comparer(preferences, ignore_case)
    });
    let preferences = preferences.clone();
    Rc::new(move |nodes: &[Node], s1: NodeId, s2: NodeId| {
        compare_import_or_export_specifiers(nodes, s1, s2, &*comparer, &preferences)
    })
}

/// `GetImportSpecifierInsertionIndex` returns the index at which to insert a
/// new import specifier.
pub fn get_import_specifier_insertion_index(
    nodes: &[Node],
    sorted_imports: &[NodeId],
    new_import: NodeId,
    comparer: &SpecifierComparer,
) -> usize {
    first_result(binary_search_unique_func(sorted_imports, |_mid, value| {
        comparer(nodes, *value, new_import)
    }))
}

/// `GetImportDeclarationInsertIndex` returns the index at which to insert a
/// new import declaration.
pub fn get_import_declaration_insert_index(
    nodes: &[Node],
    sorted_imports: &[NodeId],
    new_import: NodeId,
    comparer: &StatementComparer,
) -> usize {
    first_result(binary_search_unique_func(sorted_imports, |_mid, value| {
        comparer(nodes, *value, new_import)
    }))
}

/// `GetOrganizeImportsStringComparerWithDetection` returns a string comparer
/// based on detecting the order of import statements by the module specifier.
///
/// PORT: Go returns a nil comparer when `comparersToTest` is empty; that is
/// `None` here.
pub fn get_organize_imports_string_comparer_with_detection(
    nodes: &[Node],
    original_import_decls: &[NodeId],
    preferences: &UserPreferences,
) -> (Option<Rc<StringComparer>>, bool) {
    let (result, sorted) = detect_module_specifier_case_by_sort(
        nodes,
        &[original_import_decls.to_vec()],
        &get_comparers(preferences),
    );
    (result, sorted)
}

/// `getComparers`.
fn get_comparers(preferences: &UserPreferences) -> Vec<Rc<StringComparer>> {
    if preferences.organize_imports_sort != OrganizeImportsSort::AUTO
        || !preferences.organize_imports_ignore_case.is_unknown()
    {
        let ignore_case = if !preferences.organize_imports_ignore_case.is_unknown() {
            preferences.organize_imports_ignore_case.is_true()
        } else {
            false
        };
        return vec![get_organize_imports_string_comparer(
            preferences,
            ignore_case,
        )];
    }
    vec![
        get_organize_imports_string_comparer(preferences, true),
        get_organize_imports_string_comparer(preferences, false),
    ]
}

/// `namedImportSortResult`.
struct NamedImportSortResult {
    named_import_comparer: Rc<StringComparer>,
    type_order: OrganizeImportsTypeOrder,
    is_sorted: bool,
}

/// `DetectNamedImportOrganizationBySort` detects the order of named imports
/// throughout the file by considering the named imports in each statement as
/// a group.
pub fn detect_named_import_organization_by_sort(
    nodes: &[Node],
    original_groups: &[NodeId],
    comparers_to_test: &[Rc<StringComparer>],
    types_to_test: &[OrganizeImportsTypeOrder],
) -> (Option<Rc<StringComparer>>, OrganizeImportsTypeOrder, bool) {
    match detect_named_import_organization_by_sort_impl(
        nodes,
        original_groups,
        comparers_to_test,
        types_to_test,
    ) {
        None => (None, OrganizeImportsTypeOrder::LAST, false),
        Some(result) => (
            Some(result.named_import_comparer),
            result.type_order,
            result.is_sorted,
        ),
    }
}

/// `detectNamedImportOrganizationBySort`.
fn detect_named_import_organization_by_sort_impl(
    nodes: &[Node],
    original_groups: &[NodeId],
    comparers_to_test: &[Rc<StringComparer>],
    types_to_test: &[OrganizeImportsTypeOrder],
) -> Option<NamedImportSortResult> {
    let mut both_named_imports = false;
    let mut import_decls_with_named: Vec<NodeId> = Vec::new();

    for &imp in original_groups {
        let Some(import_clause_id) = nodes[imp].as_import_declaration().import_clause else {
            continue;
        };
        let clause = nodes[import_clause_id].as_import_clause();
        if clause
            .named_bindings
            .is_none_or(|nb| nodes[nb].kind != Kind::NamedImports)
        {
            continue;
        }
        let named_imports = nodes[clause.named_bindings.unwrap()].as_named_imports();
        let Some(elements) = &named_imports.elements else {
            continue;
        };
        if elements.nodes.is_empty() {
            continue;
        }

        if !both_named_imports {
            let mut has_type_only = false;
            let mut has_regular = false;
            for &elem in elements.nodes.iter() {
                if nodes[elem].is_type_only() {
                    has_type_only = true;
                } else {
                    has_regular = true;
                }
            }
            if has_type_only && has_regular {
                both_named_imports = true;
            }
        }

        import_decls_with_named.push(imp);
    }

    if import_decls_with_named.is_empty() {
        return None;
    }

    let mut named_imports_by_decl: Vec<Vec<NodeId>> =
        Vec::with_capacity(import_decls_with_named.len());
    for &imp in &import_decls_with_named {
        let clause_id = nodes[imp].as_import_declaration().import_clause.unwrap();
        let clause = nodes[clause_id].as_import_clause();
        let named_imports = nodes[clause.named_bindings.unwrap()].as_named_imports();
        named_imports_by_decl.push(named_imports.elements.as_ref().unwrap().nodes.to_vec());
    }

    if !both_named_imports || types_to_test.is_empty() {
        let mut names_list: Vec<Vec<String>> = Vec::with_capacity(named_imports_by_decl.len());
        for imports in &named_imports_by_decl {
            let names: Vec<String> = imports
                .iter()
                .map(|&imp| nodes[nodes[imp].name().unwrap()].text(nodes).into_owned())
                .collect();
            names_list.push(names);
        }
        let sort_state = detect_case_sensitivity_by_sort(&names_list, comparers_to_test);
        let type_order = if types_to_test.len() == 1 {
            types_to_test[0]
        } else {
            OrganizeImportsTypeOrder::LAST
        };
        return Some(NamedImportSortResult {
            // Go may carry a nil comparer here (empty comparersToTest);
            // downstream callers never invoke it in that case — keep it as a
            // box on the result and let the Option go through.
            named_import_comparer: sort_state
                .comparer
                .unwrap_or_else(|| Rc::new(|_: &str, _: &str| 0)),
            type_order,
            is_sorted: sort_state.is_sorted,
        });
    }

    const MAX_DIFF: usize = usize::MAX;
    let mut best_diff: std::collections::HashMap<OrganizeImportsTypeOrder, usize> = [
        (OrganizeImportsTypeOrder::FIRST, MAX_DIFF),
        (OrganizeImportsTypeOrder::LAST, MAX_DIFF),
        (OrganizeImportsTypeOrder::INLINE, MAX_DIFF),
    ]
    .into_iter()
    .collect();
    let mut best_comparer: std::collections::HashMap<OrganizeImportsTypeOrder, Rc<StringComparer>> =
        [
            (
                OrganizeImportsTypeOrder::FIRST,
                comparers_to_test[0].clone(),
            ),
            (OrganizeImportsTypeOrder::LAST, comparers_to_test[0].clone()),
            (
                OrganizeImportsTypeOrder::INLINE,
                comparers_to_test[0].clone(),
            ),
        ]
        .into_iter()
        .collect();

    for cur_comparer in comparers_to_test {
        let mut curr_diff: std::collections::HashMap<OrganizeImportsTypeOrder, usize> = [
            (OrganizeImportsTypeOrder::FIRST, 0),
            (OrganizeImportsTypeOrder::LAST, 0),
            (OrganizeImportsTypeOrder::INLINE, 0),
        ]
        .into_iter()
        .collect();

        for import_decl in &named_imports_by_decl {
            for &type_order in types_to_test {
                let prefs = UserPreferences {
                    organize_imports_type_order: type_order,
                    ..Default::default()
                };
                let diff = measure_sortedness(import_decl, |n1: &NodeId, n2: &NodeId| {
                    compare_import_or_export_specifiers(nodes, *n1, *n2, &**cur_comparer, &prefs)
                });
                *curr_diff.get_mut(&type_order).unwrap() += diff;
            }
        }

        for &type_order in types_to_test {
            if curr_diff[&type_order] < best_diff[&type_order] {
                best_diff.insert(type_order, curr_diff[&type_order]);
                best_comparer.insert(type_order, cur_comparer.clone());
            }
        }
    }

    for &best_type_order in types_to_test {
        let mut is_best = true;
        for &test_type_order in types_to_test {
            if best_diff[&test_type_order] < best_diff[&best_type_order] {
                is_best = false;
                break;
            }
        }
        if is_best {
            return Some(NamedImportSortResult {
                named_import_comparer: best_comparer[&best_type_order].clone(),
                type_order: best_type_order,
                is_sorted: best_diff[&best_type_order] == 0,
            });
        }
    }

    Some(NamedImportSortResult {
        named_import_comparer: best_comparer[&OrganizeImportsTypeOrder::LAST].clone(),
        type_order: OrganizeImportsTypeOrder::LAST,
        is_sorted: best_diff[&OrganizeImportsTypeOrder::LAST] == 0,
    })
}

/// `caseSensitivityDetectionResult`.
struct CaseSensitivityDetectionResult {
    comparer: Option<Rc<StringComparer>>,
    is_sorted: bool,
}

/// `DetectModuleSpecifierCaseBySort` detects the order of module specifiers
/// based on import statements throughout the module/file.
pub fn detect_module_specifier_case_by_sort(
    nodes: &[Node],
    import_decls_by_group: &[Vec<NodeId>],
    comparers_to_test: &[Rc<StringComparer>],
) -> (Option<Rc<StringComparer>>, bool) {
    let mut module_specifiers_by_group: Vec<Vec<String>> =
        Vec::with_capacity(import_decls_by_group.len());
    for import_group in import_decls_by_group {
        let mut module_names: Vec<String> = Vec::with_capacity(import_group.len());
        for &decl in import_group {
            if let Some(expr) = get_module_specifier_expression(nodes, decl) {
                module_names.push(get_external_module_name(nodes, Some(expr)));
            } else {
                module_names.push(String::new());
            }
        }
        module_specifiers_by_group.push(module_names);
    }
    let result = detect_case_sensitivity_by_sort(&module_specifiers_by_group, comparers_to_test);
    (result.comparer, result.is_sorted)
}

/// `detectCaseSensitivityBySort`.
fn detect_case_sensitivity_by_sort(
    original_groups: &[Vec<String>],
    comparers_to_test: &[Rc<StringComparer>],
) -> CaseSensitivityDetectionResult {
    let mut best_comparer: Option<usize> = None;
    let mut best_diff = usize::MAX;

    for (i, cur_comparer) in comparers_to_test.iter().enumerate() {
        let mut diff_of_current_comparer = 0usize;

        for list_to_sort in original_groups {
            if list_to_sort.len() <= 1 {
                continue;
            }
            let diff = measure_sortedness(list_to_sort, |a: &String, b: &String| {
                cur_comparer(a.as_str(), b.as_str())
            });
            diff_of_current_comparer += diff;
        }

        if diff_of_current_comparer < best_diff {
            best_diff = diff_of_current_comparer;
            best_comparer = Some(i);
        }
    }

    // `bestComparer == nil && len(comparersToTest) > 0` fallback
    let best_comparer = best_comparer
        .or(if !comparers_to_test.is_empty() {
            Some(0)
        } else {
            None
        })
        .map(|i| comparers_to_test[i].clone());

    CaseSensitivityDetectionResult {
        comparer: best_comparer,
        is_sorted: best_diff == 0,
    }
}

/// `measureSortedness`.
fn measure_sortedness<T>(arr: &[T], comparer: impl Fn(&T, &T) -> i32) -> usize {
    let mut i = 0;
    for j in 0..arr.len().saturating_sub(1) {
        if comparer(&arr[j], &arr[j + 1]) > 0 {
            i += 1;
        }
    }
    i
}

/// `GetNamedImportSpecifierComparerWithDetection` returns a specifier comparer
/// based on detecting the existing sort order within a single import statement.
pub fn get_named_import_specifier_comparer_with_detection(
    nodes: &[Node],
    import_decl: NodeId,
    source_file: Option<NodeId>,
    preferences: &UserPreferences,
) -> (Rc<SpecifierComparer>, Tristate) {
    let (comparers_to_test, type_orders_to_test) = get_detection_lists(preferences);

    let import_stmt = if nodes[import_decl].kind == Kind::ImportDeclaration {
        Some(import_decl)
    } else {
        None
    };

    let mut specifier_comparer =
        get_named_import_specifier_comparer(preferences, Some(comparers_to_test[0].clone()));
    let mut is_sorted = Tristate::Unknown;

    if (resolve_organize_imports_sort(preferences) == OrganizeImportsSort::AUTO
        || preferences.organize_imports_type_order == OrganizeImportsTypeOrder::AUTO)
        && import_stmt.is_some()
    {
        let detect_from_decl = detect_named_import_organization_by_sort_impl(
            nodes,
            &[import_stmt.unwrap()],
            &comparers_to_test,
            &type_orders_to_test,
        );
        match detect_from_decl {
            Some(detect) => {
                is_sorted = tsc_core::tristate::bool_to_tristate(detect.is_sorted);
                specifier_comparer = get_named_import_specifier_comparer(
                    &UserPreferences {
                        organize_imports_type_order: detect.type_order,
                        ..Default::default()
                    },
                    Some(detect.named_import_comparer),
                );
            }
            None => {
                if let Some(source_file) = source_file {
                    let all_imports = filter_import_declarations(
                        nodes,
                        nodes[source_file].statements().unwrap_or(&[]),
                    );
                    let detect_from_file = detect_named_import_organization_by_sort_impl(
                        nodes,
                        &all_imports,
                        &comparers_to_test,
                        &type_orders_to_test,
                    );
                    if let Some(detect) = detect_from_file {
                        is_sorted = tsc_core::tristate::bool_to_tristate(detect.is_sorted);
                        specifier_comparer = get_named_import_specifier_comparer(
                            &UserPreferences {
                                organize_imports_type_order: detect.type_order,
                                ..Default::default()
                            },
                            Some(detect.named_import_comparer),
                        );
                    }
                }
            }
        }
    }

    (specifier_comparer, is_sorted)
}
