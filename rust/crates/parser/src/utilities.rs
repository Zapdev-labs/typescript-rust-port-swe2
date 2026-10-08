// Ported from tsc/internal/parser/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::{CommentRange, Kind, Node, NodeFactory, NodeId};
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::scriptkind::ScriptKind;
use tsc_scanner::scanner;

/// `func getLanguageVariant(scriptKind core.ScriptKind) core.LanguageVariant`
pub fn get_language_variant(script_kind: ScriptKind) -> LanguageVariant {
    match script_kind {
        ScriptKind::Tsx | ScriptKind::Jsx | ScriptKind::Js | ScriptKind::Json => {
            // .tsx and .jsx files are treated as jsx language variant.
            LanguageVariant::Jsx
        }
        _ => LanguageVariant::Standard,
    }
}

/// `func tokenIsIdentifierOrKeyword(token ast.Kind) bool`
pub fn token_is_identifier_or_keyword(token: Kind) -> bool {
    token >= Kind::Identifier
}

/// `func tokenIsIdentifierOrKeywordOrGreaterThan(token ast.Kind) bool`
pub fn token_is_identifier_or_keyword_or_greater_than(token: Kind) -> bool {
    token == Kind::GreaterThanToken || token_is_identifier_or_keyword(token)
}

/// `func GetJSDocCommentRanges(f *ast.NodeFactory, commentRanges []ast.CommentRange, node *ast.Node, text string) []ast.CommentRange`
///
/// `node` is a `NodeId`; resolve it through `nodes`.
pub fn get_jsdoc_comment_ranges(
    f: &NodeFactory,
    comment_ranges: Vec<CommentRange>,
    node: NodeId,
    text: &str,
    nodes: &[Node],
) -> Vec<CommentRange> {
    let n = &nodes[node];
    let mut comment_ranges = comment_ranges;
    match n.kind {
        Kind::Parameter
        | Kind::TypeParameter
        | Kind::FunctionExpression
        | Kind::ArrowFunction
        | Kind::ParenthesizedExpression
        | Kind::VariableDeclaration
        | Kind::ExportSpecifier => {
            comment_ranges.extend(scanner::get_trailing_comment_ranges(f, text, n.pos()));
            comment_ranges.extend(scanner::get_leading_comment_ranges(f, text, n.pos()));
        }
        _ => {
            comment_ranges.extend(scanner::get_leading_comment_ranges(f, text, n.pos()));
        }
    }
    // Keep if the comment starts with '/**' but not if it is '/**/'
    comment_ranges.retain(|comment: &CommentRange| {
        let comment_start = comment.text_range.pos();
        let comment_len = comment.text_range.end() - comment_start;
        !(comment.text_range.end() > n.end()
            || comment_len < 4
            || text.as_bytes()[comment_start as usize + 1] != b'*'
            || text.as_bytes()[comment_start as usize + 2] != b'*'
            || text.as_bytes()[comment_start as usize + 3] == b'/')
    });
    comment_ranges
}

/// `func isKeywordOrPunctuation(token ast.Kind) bool`
pub fn is_keyword_or_punctuation(token: Kind) -> bool {
    token.is_keyword_kind() || token.is_punctuation_kind()
}

/// `func isJSDocLikeText(text string) bool`
pub fn is_jsdoc_like_text(text: &str) -> bool {
    let text = text.as_bytes();
    text.len() >= 4 && text[1] == b'*' && text[2] == b'*' && text[3] != b'/'
}
