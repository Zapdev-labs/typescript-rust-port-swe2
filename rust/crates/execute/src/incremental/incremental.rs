// Ported from tsc/internal/execute/incremental/incremental.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::rc::Rc;
use std::sync::Arc;

use tsc_compiler::host::CompilerHost;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;

use crate::incremental::build_info::{BuildInfo, content_mapper_identities};
use crate::incremental::buildinfo_to_snapshot::build_info_to_snapshot;
use crate::incremental::program::Program;

/// `type BuildInfoReader interface`.
pub trait BuildInfoReader {
    /// `ReadBuildInfo`.
    fn read_build_info(&self, config: &ParsedCommandLine) -> Option<BuildInfo>;
}

/// `type buildInfoReader struct`.
struct BuildInfoReaderImpl {
    host: Arc<dyn CompilerHost>,
}

impl BuildInfoReader for BuildInfoReaderImpl {
    fn read_build_info(&self, config: &ParsedCommandLine) -> Option<BuildInfo> {
        let build_info_file_name = config.get_build_info_file_name();
        if build_info_file_name.as_string().is_empty() {
            return None;
        }

        // Read build info file.
        let data = self.host.fs().read_file(&build_info_file_name)?;
        let build_info: BuildInfo = tsc_json::unmarshal(data.as_bytes(), &[]).ok()?;
        Some(build_info)
    }
}

/// `func NewBuildInfoReader`.
pub fn new_build_info_reader(host: Arc<dyn CompilerHost>) -> Arc<dyn BuildInfoReader> {
    Arc::new(BuildInfoReaderImpl { host })
}

/// `func ReadBuildInfoProgram`.
///
/// PORT: returns `Rc<Program>` so the incremental program can be shared with
/// follow-up compilations as the old program.
pub fn read_build_info_program(
    config: &ParsedCommandLine,
    reader: Arc<dyn BuildInfoReader>,
    host: &Arc<dyn CompilerHost>,
) -> Option<Rc<Program>> {
    // Read buildInfo file.
    let build_info = reader.read_build_info(config)?;
    if !build_info.is_valid_version() || !build_info.is_incremental() {
        return None;
    }
    // If any configured content mapper's identity has changed, files it
    // produced may be stale, so the old program cannot be reused.
    let identities = content_mapper_identities(host.content_mapper_project()).ok()?;
    if !build_info.content_mapper_identities_match(&identities) {
        return None;
    }

    // Convert to information that can be used to create incremental program.
    Some(Rc::new(Program::from_snapshot(build_info_to_snapshot(
        build_info, config, host,
    ))))
}
