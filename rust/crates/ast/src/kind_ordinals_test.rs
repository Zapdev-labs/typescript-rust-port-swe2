// M2 gate test (SPEC §M2): `Kind` ordinals must be 1:1 with Go's generated
// kind table. `testdata/kind_ordinals.tsv` is extracted from
// tsc/internal/ast/kind_generated.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// — Go names + resolved iota values, including the KindFirst*/KindLast*
// sentinel aliases (which map to Kind::FIRST_*/LAST_* associated consts here).

use crate::kind_generated::Kind;

fn sentinel_const(name: &str) -> Option<Kind> {
    Some(match name {
        "KindFirstAssignment" => Kind::FIRST_ASSIGNMENT,
        "KindLastAssignment" => Kind::LAST_ASSIGNMENT,
        "KindFirstCompoundAssignment" => Kind::FIRST_COMPOUND_ASSIGNMENT,
        "KindLastCompoundAssignment" => Kind::LAST_COMPOUND_ASSIGNMENT,
        "KindFirstReservedWord" => Kind::FIRST_RESERVED_WORD,
        "KindLastReservedWord" => Kind::LAST_RESERVED_WORD,
        "KindFirstKeyword" => Kind::FIRST_KEYWORD,
        "KindLastKeyword" => Kind::LAST_KEYWORD,
        "KindFirstFutureReservedWord" => Kind::FIRST_FUTURE_RESERVED_WORD,
        "KindLastFutureReservedWord" => Kind::LAST_FUTURE_RESERVED_WORD,
        "KindFirstTypeNode" => Kind::FIRST_TYPE_NODE,
        "KindLastTypeNode" => Kind::LAST_TYPE_NODE,
        "KindFirstPunctuation" => Kind::FIRST_PUNCTUATION,
        "KindLastPunctuation" => Kind::LAST_PUNCTUATION,
        "KindFirstToken" => Kind::FIRST_TOKEN,
        "KindLastToken" => Kind::LAST_TOKEN,
        "KindFirstLiteralToken" => Kind::FIRST_LITERAL_TOKEN,
        "KindLastLiteralToken" => Kind::LAST_LITERAL_TOKEN,
        "KindFirstTemplateToken" => Kind::FIRST_TEMPLATE_TOKEN,
        "KindLastTemplateToken" => Kind::LAST_TEMPLATE_TOKEN,
        "KindFirstBinaryOperator" => Kind::FIRST_BINARY_OPERATOR,
        "KindLastBinaryOperator" => Kind::LAST_BINARY_OPERATOR,
        "KindFirstStatement" => Kind::FIRST_STATEMENT,
        "KindLastStatement" => Kind::LAST_STATEMENT,
        "KindFirstNode" => Kind::FIRST_NODE,
        "KindFirstJSDocNode" => Kind::FIRST_J_S_DOC_NODE,
        "KindLastJSDocNode" => Kind::LAST_J_S_DOC_NODE,
        "KindFirstJSDocTagNode" => Kind::FIRST_J_S_DOC_TAG_NODE,
        "KindLastJSDocTagNode" => Kind::LAST_J_S_DOC_TAG_NODE,
        "KindFirstContextualKeyword" => Kind::FIRST_CONTEXTUAL_KEYWORD,
        "KindLastContextualKeyword" => Kind::LAST_CONTEXTUAL_KEYWORD,
        "KindLastUnaryOperator" => Kind::LAST_UNARY_OPERATOR,
        "KindFirstTriviaToken" => Kind::FIRST_TRIVIA_TOKEN,
        "KindLastTriviaToken" => Kind::LAST_TRIVIA_TOKEN,
        _ => return None,
    })
}

#[test]
fn kind_ordinals_match_go_table() {
    let tsv = include_str!("../testdata/kind_ordinals.tsv");
    let mut checked = 0usize;
    let mut failures = Vec::new();
    for line in tsv.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (name, ord) = line.split_once('\t').expect("tsv line");
        let want: i16 = ord.parse().expect("ordinal");
        let kind = Kind::from_kind_string(name).or_else(|| sentinel_const(name));
        match kind {
            Some(k) if k as i16 == want => checked += 1,
            Some(k) => failures.push(format!("{name}: got {} want {want}", k as i16)),
            None => failures.push(format!("{name}: no Rust kind")),
        }
    }
    assert!(failures.is_empty(), "ordinal mismatches:\n{}", failures.join("\n"));
    assert_eq!(checked, 387, "expected to check all 387 Go kind constants");
}
