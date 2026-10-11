// Ported from tsc/internal/project/ata @ ec47d33c23e464a17cdf2475632cba629bee8763

mod ata;
mod discovertypings;
mod typesmap;
mod validatepackagename;

pub use ata::{
    new_typings_installer, CachedTyping, NpmExecutor, ProjectId, TypingsInfo,
    TypingsInstallRequest, TypingsInstallResult, TypingsInstaller, TypingsInstallerOptions,
};
pub use discovertypings::discover_typings;
pub use typesmap::SAFE_FILE_NAME_TO_TYPE_NAME;
pub use validatepackagename::{
    render_package_name_validation_failure, validate_package_name, NameValidationResult,
    MAX_PACKAGE_NAME_LENGTH,
};
