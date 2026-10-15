// Ported from tsc/internal/fourslash/semantictokens.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// ASSUMPTIONS:
//   - `FourslashTest.send_request` takes `&mut self` (matches the parallel port).
//   - `f.converters` is the shared `TestConverters` (UTF-8 encoding).
//   - Go's `t *testing.T` is dropped; `t.Fatal*`/`t.Errorf` become `panic!`.

use tsc_lsconv::file_name_to_document_uri;
use tsc_lsproto::{Position, SemanticTokensParams, TextDocumentIdentifier};

use crate::fourslash::FourslashTest;

/// `type SemanticToken struct` — `Type` → `type_` (keyword).
pub(crate) struct SemanticToken {
    pub(crate) type_: String,
    pub(crate) text: String,
}

impl FourslashTest {
    /// `VerifySemanticTokens`.
    pub(crate) fn verify_semantic_tokens(&mut self, expected: &[SemanticToken]) {
        let params = SemanticTokensParams {
            text_document: TextDocumentIdentifier {
                uri: file_name_to_document_uri(&self.active_filename),
            },
            ..Default::default()
        };

        let result = self.send_request(
            &tsc_lsproto::TEXT_DOCUMENT_SEMANTIC_TOKENS_FULL_INFO,
            params,
        );

        let Some(semantic_tokens) = result.semantic_tokens else {
            if expected.is_empty() {
                return;
            }
            panic!("Expected semantic tokens but got nil");
        };

        // Decode the semantic tokens using token types/modifiers from the test configuration
        let actual = decode_semantic_tokens(
            self,
            semantic_tokens.data.as_deref().unwrap_or(&[]),
            &self.semantic_token_types,
            &self.semantic_token_modifiers,
        );

        // Compare with expected
        assert!(
            actual.len() == expected.len(),
            "Expected {} semantic tokens, got {}\n\nExpected:\n{}\n\nActual:\n{}",
            expected.len(),
            actual.len(),
            format_semantic_tokens(expected),
            format_semantic_tokens(&actual),
        );

        for (i, (exp, act)) in expected.iter().zip(actual.iter()).enumerate() {
            assert!(
                exp.type_ == act.type_ && exp.text == act.text,
                "Token {i} mismatch:\n  Expected: {{Type: {:?}, Text: {:?}}}\n  Actual:   {{Type: {:?}, Text: {:?}}}",
                exp.type_,
                exp.text,
                act.type_,
                act.text,
            );
        }
    }
}
/// `decodeSemanticTokens`.
fn decode_semantic_tokens(
    f: &FourslashTest,
    data: &[u32],
    token_types: &[String],
    token_modifiers: &[String],
) -> Vec<SemanticToken> {
    assert!(
        data.len() % 5 == 0,
        "Invalid semantic tokens data length: {}",
        data.len()
    );

    let script_info = f
        .script_infos
        .get(&f.active_filename)
        .expect("script info for active file");
    let converters = f.test_converters();

    let mut tokens = Vec::new();
    let mut prev_line = 0u32;
    let mut prev_char = 0u32;

    for chunk in data.chunks_exact(5) {
        let delta_line = chunk[0];
        let delta_char = chunk[1];
        let length = chunk[2];
        let token_type_idx = chunk[3];
        let token_modifier_mask = chunk[4];

        // Calculate absolute position
        let line = prev_line + delta_line;
        let char_ = if delta_line == 0 {
            prev_char + delta_char
        } else {
            delta_char
        };

        // Get token type
        assert!(
            (token_type_idx as usize) < token_types.len(),
            "Token type index out of range: {token_type_idx}"
        );
        let token_type = &token_types[token_type_idx as usize];

        // Get modifiers
        let mut modifiers = Vec::new();
        for (i, mod_) in token_modifiers.iter().enumerate() {
            if token_modifier_mask & (1 << i) != 0 {
                modifiers.push(mod_);
            }
        }

        // Build full type string (type.modifier1.modifier2)
        let mut type_str = token_type.clone();
        if !modifiers.is_empty() {
            type_str = format!(
                "{}.{}",
                type_str,
                modifiers
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(".")
            );
        }

        // Get the text
        let start_pos = Position {
            line,
            character: char_,
        };
        let end_pos = Position {
            line,
            character: char_ + length,
        };
        let start_offset =
            converters.line_and_character_to_position(&script_info, start_pos) as usize;
        let end_offset = converters.line_and_character_to_position(&script_info, end_pos) as usize;
        let text = script_info.content[start_offset..end_offset].to_string();

        tokens.push(SemanticToken {
            type_: type_str,
            text,
        });

        prev_line = line;
        prev_char = char_;
    }

    tokens
}

/// `formatSemanticTokens`.
fn format_semantic_tokens(tokens: &[SemanticToken]) -> String {
    tokens
        .iter()
        .enumerate()
        .map(|(i, tok)| format!("  [{i}] {{Type: {:?}, Text: {:?}}}", tok.type_, tok.text))
        .collect::<Vec<_>>()
        .join("\n")
}
