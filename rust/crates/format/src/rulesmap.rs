// Ported from tsc/internal/format/rulesmap.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::OnceLock;

use tsc_ast::ast::Node;
use tsc_ast::kind_generated::Kind;

use crate::context::FormattingContext;
use crate::rule::{
    RULE_ACTION_MODIFY_SPACE_ACTION, RULE_ACTION_MODIFY_TOKEN_ACTION, RULE_ACTION_NONE,
    RULE_ACTION_STOP_ACTION, RULE_ACTION_STOP_PROCESSING_SPACE_ACTIONS,
    RULE_ACTION_STOP_PROCESSING_TOKEN_ACTIONS, RuleAction, RuleImpl,
};
use crate::rules::get_all_rules;

/// `getRules`
pub(crate) fn get_rules<'a>(
    context: &mut FormattingContext,
    rules: &mut Vec<&'static RuleImpl>,
    nodes: &mut Vec<Node>,
) {
    let bucket = &get_rules_map()[get_rule_bucket_index(
        context.current_token_span.kind,
        context.next_token_span.kind,
    )];
    if !bucket.is_empty() {
        let mut rule_action_mask = RULE_ACTION_NONE;
        'outer: for rule in bucket {
            let accept_rule_actions = !get_rule_action_exclusion(rule_action_mask);
            if rule.action() & accept_rule_actions != 0 {
                let preds = rule.context();
                for p in preds {
                    if !p(context, nodes) {
                        continue 'outer;
                    }
                }
                rules.push(rule);
                rule_action_mask |= rule.action();
            }
        }
    }
}

/// `getRuleBucketIndex`
fn get_rule_bucket_index(row: Kind, column: Kind) -> usize {
    debug_assert!(
        row <= Kind::LAST_KEYWORD && column <= Kind::LAST_KEYWORD,
        "Must compute formatting context from tokens"
    );
    (row as usize) * MAP_ROW_LENGTH + (column as usize)
}

const MASK_BIT_SIZE: usize = 5;
const MASK: u32 = 0b11111; // MaskBitSize bits
const MAP_ROW_LENGTH: usize = Kind::LAST_TOKEN as usize + 1;

/// `getRuleActionExclusion` — for a given rule action, gets a mask of other
/// rule actions that cannot be applied at the same position.
fn get_rule_action_exclusion(rule_action: RuleAction) -> RuleAction {
    let mut mask = RULE_ACTION_NONE;
    if rule_action & RULE_ACTION_STOP_PROCESSING_SPACE_ACTIONS != 0 {
        mask |= RULE_ACTION_MODIFY_SPACE_ACTION;
    }
    if rule_action & RULE_ACTION_STOP_PROCESSING_TOKEN_ACTIONS != 0 {
        mask |= RULE_ACTION_MODIFY_TOKEN_ACTION;
    }
    if rule_action & RULE_ACTION_MODIFY_SPACE_ACTION != 0 {
        mask |= RULE_ACTION_MODIFY_SPACE_ACTION;
    }
    if rule_action & RULE_ACTION_MODIFY_TOKEN_ACTION != 0 {
        mask |= RULE_ACTION_MODIFY_TOKEN_ACTION;
    }
    mask
}

/// `var getRulesMap = sync.OnceValue(buildRulesMap)`
fn get_rules_map() -> &'static Vec<Vec<&'static RuleImpl>> {
    static RULES_MAP: OnceLock<Vec<Vec<&'static RuleImpl>>> = OnceLock::new();
    RULES_MAP.get_or_init(build_rules_map)
}

/// `buildRulesMap`
fn build_rules_map() -> Vec<Vec<&'static RuleImpl>> {
    let rules = get_all_rules();
    // Map from bucket index to array of rules
    let mut m: Vec<Vec<&'static RuleImpl>> = (0..MAP_ROW_LENGTH * MAP_ROW_LENGTH)
        .map(|_| Vec::new())
        .collect();
    // This array is used only during construction of the rulesbucket in the map
    let mut rules_bucket_construction_state_list = vec![0u32; m.len()];
    for rule in &rules {
        let specific_rule = rule.left_token_range.is_specific && rule.right_token_range.is_specific;

        for left in &rule.left_token_range.tokens {
            for right in &rule.right_token_range.tokens {
                let index = get_rule_bucket_index(*left, *right);
                add_rule(
                    &mut m[index],
                    rule.rule,
                    specific_rule,
                    &mut rules_bucket_construction_state_list,
                    index,
                );
            }
        }
    }
    m
}

/// `type RulesPosition int`
#[derive(Clone, Copy)]
#[repr(u32)]
enum RulesPosition {
    StopRulesSpecific = 0,
    StopRulesAny = (MASK_BIT_SIZE * 1) as u32,
    ContextRulesSpecific = (MASK_BIT_SIZE * 2) as u32,
    ContextRulesAny = (MASK_BIT_SIZE * 3) as u32,
    NoContextRulesSpecific = (MASK_BIT_SIZE * 4) as u32,
    NoContextRulesAny = (MASK_BIT_SIZE * 5) as u32,
}

// The Rules list contains all the inserted rules into a rulebucket in the following order:
//
//	1- Ignore rules with specific token combination
//	2- Ignore rules with any token combination
//	3- Context rules with specific token combination
//	4- Context rules with any token combination
//	5- Non-context rules with specific token combination
//	6- Non-context rules with any token combination
//
// The member rulesInsertionIndexBitmap is used to describe the number of rules
// in each sub-bucket (above) hence can be used to know the index of where to insert
// the next rule. It's a bitmap which contains 6 different sections each is given 5 bits.
//
// Example:
// In order to insert a rule to the end of sub-bucket (3), we get the index by adding
// the values in the bitmap segments 3rd, 2nd, and 1st.

/// `addRule`
fn add_rule(
    rules: &mut Vec<&'static RuleImpl>,
    rule: &'static RuleImpl,
    specific_tokens: bool,
    construction_state: &mut [u32],
    rules_bucket_index: usize,
) {
    let position = if rule.action() & RULE_ACTION_STOP_ACTION != 0 {
        if specific_tokens {
            RulesPosition::StopRulesSpecific
        } else {
            RulesPosition::StopRulesAny
        }
    } else if !rule.context().is_empty() {
        if specific_tokens {
            RulesPosition::ContextRulesSpecific
        } else {
            RulesPosition::ContextRulesAny
        }
    } else if specific_tokens {
        RulesPosition::NoContextRulesSpecific
    } else {
        RulesPosition::NoContextRulesAny
    };

    let state = construction_state[rules_bucket_index];

    rules.insert(get_rule_insertion_index(state, position), rule);
    construction_state[rules_bucket_index] = increase_insertion_index(state, position);
}

/// `getRuleInsertionIndex`
fn get_rule_insertion_index(mut index_bitmap: u32, mask_position: RulesPosition) -> usize {
    let mut index = 0usize;
    let mut pos = 0usize;
    while pos <= mask_position as usize {
        index += (index_bitmap & MASK) as usize;
        index_bitmap >>= MASK_BIT_SIZE;
        pos += MASK_BIT_SIZE;
    }
    index
}

/// `increaseInsertionIndex`
fn increase_insertion_index(index_bitmap: u32, mask_position: RulesPosition) -> u32 {
    let value = ((index_bitmap >> mask_position as u32) & MASK) + 1;
    debug_assert!(
        (value & MASK) == value,
        "Adding more rules into the sub-bucket than allowed. Maximum allowed is 32 rules."
    );
    (index_bitmap & !(MASK << mask_position as u32)) | (value << mask_position as u32)
}
