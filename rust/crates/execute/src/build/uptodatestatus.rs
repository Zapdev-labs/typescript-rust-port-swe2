// Ported from tsc/internal/execute/build/uptodatestatus.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Concurrency: this file is data-only — no goroutines/channels exist in the
// original. All `UpToDateStatus` values are owned by the sequential
// orchestrator (see the concurrency note at the top of `orchestrator.rs`).

use std::time::SystemTime;

use tsc_tspath::{RootedFilePath, RootedPath};

/// `time.Time{}` — Go's zero time. `SystemTime` cannot represent year 1, so
/// the epoch is the zero sentinel; real filesystem mtimes are never the epoch
/// in practice, matching how Go's zero time compares below every real time.
pub(crate) const ZERO_TIME: SystemTime = SystemTime::UNIX_EPOCH;

/// `time.Time.IsZero`.
pub(crate) fn is_zero_time(t: SystemTime) -> bool {
    t == ZERO_TIME
}

/// `type upToDateStatusType uint16`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum UpToDateStatusKind {
    // Errors:
    /// `upToDateStatusTypeConfigFileNotFound` — config file was not found.
    ConfigFileNotFound,
    /// `upToDateStatusTypeBuildErrors` — found errors during build.
    BuildErrors,
    /// `upToDateStatusTypeUpstreamErrors` — did not build because upstream
    /// project has errors - and we have option to stop build on upstream
    /// errors.
    UpstreamErrors,

    // Its all good, no work to do
    /// `upToDateStatusTypeUpToDate`.
    UpToDate,

    // Pseudo-builds - touch timestamps, no actual build:
    /// `upToDateStatusTypeUpToDateWithUpstreamTypes` — The project appears
    /// out of date because its upstream inputs are newer than its outputs,
    /// but all of its outputs are actually newer than the previous identical
    /// outputs of its (.d.ts) inputs. This means we can Pseudo-build (just
    /// touch timestamps), as if we had actually built this project.
    UpToDateWithUpstreamTypes,
    /// `upToDateStatusTypeUpToDateWithInputFileText` — The project appears up
    /// to date and even though input file changed, its text didnt so just
    /// need to update timestamps.
    UpToDateWithInputFileText,

    // Needs build:
    /// `upToDateStatusTypeInputFileMissing` — input file is missing.
    InputFileMissing,
    /// `upToDateStatusTypeOutputMissing` — output file is missing.
    OutputMissing,
    /// `upToDateStatusTypeInputFileNewer` — input file is newer than output
    /// file.
    InputFileNewer,
    /// `upToDateStatusTypeOutOfDateBuildInfoWithPendingEmit` — build info is
    /// out of date as we need to emit some files.
    OutOfDateBuildInfoWithPendingEmit,
    /// `upToDateStatusTypeOutOfDateBuildInfoWithErrors` — build info
    /// indicates that project has errors and they need to be reported.
    OutOfDateBuildInfoWithErrors,
    /// `upToDateStatusTypeOutOfDateOptions` — build info options indicate
    /// there is work to do based on changes in options.
    OutOfDateOptions,
    /// `upToDateStatusTypeOutOfDateRoots` — file was root when built but not
    /// any more.
    OutOfDateRoots,
    /// `upToDateStatusTypeTsVersionOutputOfDate` — buildInfo.version
    /// mismatch with current ts version.
    TsVersionOutputOfDate,
    /// `upToDateStatusTypeForceBuild` — build because --force was specified.
    ForceBuild,

    /// `upToDateStatusTypeSolution` — solution file.
    Solution,
}

/// `type inputOutputName struct`.
#[derive(Clone, Debug)]
pub(crate) struct InputOutputName {
    pub input: RootedPath,
    pub output: RootedFilePath,
}

/// `type fileAndTime struct`.
#[derive(Clone, Debug)]
pub(crate) struct FileAndTime {
    pub file: RootedFilePath,
    pub time: SystemTime,
}

/// `type inputOutputFileAndTime struct`.
#[derive(Clone, Debug)]
pub(crate) struct InputOutputFileAndTime {
    pub input: FileAndTime,
    pub output: FileAndTime,
}

/// `type upstreamErrors struct`.
#[derive(Clone, Debug)]
pub(crate) struct UpstreamErrors {
    pub r#ref: RootedPath,
    pub ref_has_upstream_errors: bool,
}

/// Go's `upToDateStatus.data any` — the payload a `UpToDateStatusKind`
/// carries. Go relies on unchecked type assertions; the enum keeps them
/// typed (each accessor still mirrors the Go assertion panic via `expect`).
#[derive(Clone, Debug)]
pub(crate) enum UpToDateStatusData {
    /// Go's nil `data`.
    None,
    /// `data tspath.RootedFilePath` — missing inputs/outputs, buildInfo
    /// paths, and the post-emit `oldestOutputFileName` on `UpToDate`.
    FilePath(RootedFilePath),
    /// `data *inputOutputName`.
    InputOutputName(InputOutputName),
    /// `data *inputOutputFileAndTime`.
    InputOutputFileAndTime(InputOutputFileAndTime),
    /// `data *upstreamErrors`.
    UpstreamErrors(UpstreamErrors),
    /// `data string` — `TsVersionOutputOfDate` carries `buildInfo.Version`.
    Version(String),
}

/// `type upToDateStatus struct`.
#[derive(Clone, Debug)]
pub(crate) struct UpToDateStatus {
    pub kind: UpToDateStatusKind,
    pub data: UpToDateStatusData,
}

impl UpToDateStatus {
    pub(crate) fn new(kind: UpToDateStatusKind) -> Self {
        UpToDateStatus {
            kind,
            data: UpToDateStatusData::None,
        }
    }

    pub(crate) fn with_data(kind: UpToDateStatusKind, data: UpToDateStatusData) -> Self {
        UpToDateStatus { kind, data }
    }

    /// `(s *upToDateStatus) isError`.
    pub(crate) fn is_error(&self) -> bool {
        matches!(
            self.kind,
            UpToDateStatusKind::ConfigFileNotFound
                | UpToDateStatusKind::BuildErrors
                | UpToDateStatusKind::UpstreamErrors
        )
    }

    /// `(s *upToDateStatus) isPseudoBuild`.
    pub(crate) fn is_pseudo_build(&self) -> bool {
        matches!(
            self.kind,
            UpToDateStatusKind::UpToDateWithUpstreamTypes
                | UpToDateStatusKind::UpToDateWithInputFileText
        )
    }

    /// `(s *upToDateStatus) inputOutputFileAndTime`.
    pub(crate) fn input_output_file_and_time(&self) -> Option<&InputOutputFileAndTime> {
        match &self.data {
            UpToDateStatusData::InputOutputFileAndTime(data) => Some(data),
            _ => None,
        }
    }

    /// `(s *upToDateStatus) inputOutputName`.
    pub(crate) fn input_output_name(&self) -> Option<&InputOutputName> {
        match &self.data {
            UpToDateStatusData::InputOutputName(data) => Some(data),
            _ => None,
        }
    }

    /// `(s *upToDateStatus) oldestOutputFileName`.
    pub(crate) fn oldest_output_file_name(&self) -> RootedFilePath {
        if !self.is_pseudo_build() && self.kind != UpToDateStatusKind::UpToDate {
            panic!("only valid for up to date status of pseudo-build or up to date");
        }

        if let Some(input_output_file_and_time) = self.input_output_file_and_time() {
            return input_output_file_and_time.output.file.clone();
        }
        if let Some(input_output_name) = self.input_output_name() {
            return input_output_name.output.clone();
        }
        match &self.data {
            UpToDateStatusData::FilePath(path) => path.clone(),
            _ => panic!("upToDateStatus.data is not a RootedFilePath"),
        }
    }

    /// `(s *upToDateStatus) upstreamErrors`.
    pub(crate) fn upstream_errors(&self) -> &UpstreamErrors {
        match &self.data {
            UpToDateStatusData::UpstreamErrors(data) => data,
            _ => panic!("upToDateStatus.data is not *upstreamErrors"),
        }
    }

    /// `s.data.(tspath.RootedFilePath)` — used by `reportUpToDateStatus`.
    pub(crate) fn file_path_data(&self) -> &RootedFilePath {
        match &self.data {
            UpToDateStatusData::FilePath(path) => path,
            _ => panic!("upToDateStatus.data is not a RootedFilePath"),
        }
    }

    /// `s.data.(string)` — `TsVersionOutputOfDate`'s recorded version.
    pub(crate) fn version_data(&self) -> &str {
        match &self.data {
            UpToDateStatusData::Version(version) => version,
            _ => panic!("upToDateStatus.data is not a string"),
        }
    }
}
