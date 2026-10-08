// Ported from tsc/internal/tsoptions @ ec47d33c23e464a17cdf2475632cba629bee8763

pub mod commandlineoption;
pub mod commandlineparser;
pub mod contentmappers;
pub mod diagnostics;
pub mod enummaps;
pub mod errors;
pub mod generated;
pub mod namemap;
pub mod parsedbuildcommandline;
pub mod parsedcommandline;
pub mod parsedoptions;
pub mod parsinghelpers;
pub mod rawcompileroptions;
pub mod showconfig;
pub mod tsconfigparsing;
pub mod value;
pub mod wildcarddirectories;

#[cfg(test)]
mod commandlineparser_test;
#[cfg(test)]
mod parsedcommandline_test;
#[cfg(test)]
mod parsinghelpers_test;
#[cfg(test)]
mod rawcompileroptions_test;
#[cfg(test)]
mod tsconfigparsing_test;
#[cfg(test)]
mod wildcarddirectories_test;

#[cfg(test)]
mod contentmappers_test;
#[cfg(test)]
mod decls_test;

#[cfg(test)]
mod compileroptions_test;
#[cfg(test)]
mod parsedoptions_test;
#[cfg(test)]
mod showconfig_test;
