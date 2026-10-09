// Ported from tsc/internal/transformers/estransforms/definitions.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The public transformer factories: the per-target chains and
// `GetESTransformer`, which picks a chain by `EmitScriptTarget`.

use tsc_core::options_generated::ScriptTarget;

use super::r#async::new_async_transformer;
use super::classfields::new_class_fields_transformer;
use super::esdecorator::new_es_decorator_transformer;
use super::exponentiation::new_exponentiation_transformer;
use super::forawait::new_forawait_transformer;
use super::logicalassignment::new_logical_assignment_transformer;
use super::nullishcoalescing::new_nullish_coalescing_transformer;
use super::objectrestspread::new_object_rest_spread_transformer;
use super::optionalcatch::new_optional_catch_transformer;
use super::optionalchain::new_optional_chain_transformer;
use super::taggedtemplate::new_tagged_template_lift_restriction_transformer;
use super::using::new_using_declaration_transformer;
use crate::chain::{TransformOptions, TransformerFactory, chain};
use crate::transformer::Transformer;

/// `esDecoratorAndClassFields`.
pub fn es_decorator_and_class_fields<'a>() -> TransformerFactory<'a> {
    chain(vec![
        Box::new(new_es_decorator_transformer),
        Box::new(new_class_fields_transformer),
    ])
}

/// `NewESNextTransformer`.
pub fn new_es_next_transformer<'a>() -> TransformerFactory<'a> {
    chain(vec![
        Box::new(new_using_declaration_transformer),
        es_decorator_and_class_fields(),
    ])
}

// 2026: no new downlevel syntax
// 2025: only module system syntax (import attributes, json modules), untransformed regex modifiers
// 2024: no new downlevel syntax
// 2023: no new downlevel syntax
// 2022: class static blocks and class fields are handled by newClassFieldsTransformer

/// `NewES2021Transformer`.
pub fn new_es2021_transformer<'a>() -> TransformerFactory<'a> {
    chain(vec![
        new_es_next_transformer(),
        Box::new(new_logical_assignment_transformer),
    ])
}

/// `NewES2020Transformer`.
pub fn new_es2020_transformer<'a>() -> TransformerFactory<'a> {
    chain(vec![
        new_es2021_transformer(),
        Box::new(new_nullish_coalescing_transformer),
        Box::new(new_optional_chain_transformer),
    ])
}

/// `NewES2019Transformer`.
pub fn new_es2019_transformer<'a>() -> TransformerFactory<'a> {
    chain(vec![
        new_es2020_transformer(),
        Box::new(new_optional_catch_transformer),
    ])
}

/// `NewES2018Transformer`.
pub fn new_es2018_transformer<'a>() -> TransformerFactory<'a> {
    chain(vec![
        new_es2019_transformer(),
        Box::new(new_object_rest_spread_transformer),
        Box::new(new_forawait_transformer),
        Box::new(new_tagged_template_lift_restriction_transformer),
    ])
}

/// `NewES2017Transformer`.
pub fn new_es2017_transformer<'a>() -> TransformerFactory<'a> {
    chain(vec![
        new_es2018_transformer(),
        Box::new(new_async_transformer),
    ])
}

/// `NewES2016Transformer`.
pub fn new_es2016_transformer<'a>() -> TransformerFactory<'a> {
    chain(vec![
        new_es2017_transformer(),
        Box::new(new_exponentiation_transformer),
    ])
}

/// `GetESTransformer(opts)`.
pub fn get_es_transformer<'a>(opts: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    let options = opts
        .compiler_options
        .expect("GetESTransformer requires compiler options");
    match options.get_emit_script_target() {
        ScriptTarget::ESNext => es_decorator_and_class_fields()(opts),
        ScriptTarget::ES2026
        | ScriptTarget::ES2025
        | ScriptTarget::ES2024
        | ScriptTarget::ES2023
        | ScriptTarget::ES2022
        | ScriptTarget::ES2021 => new_es_next_transformer()(opts),
        ScriptTarget::ES2020 => new_es2021_transformer()(opts),
        ScriptTarget::ES2019 => new_es2020_transformer()(opts),
        ScriptTarget::ES2018 => new_es2019_transformer()(opts),
        ScriptTarget::ES2017 => new_es2018_transformer()(opts),
        ScriptTarget::ES2016 => new_es2017_transformer()(opts),
        // other, older, option, transform maximally
        _ => new_es2016_transformer()(opts),
    }
}
