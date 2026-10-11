// Ported from tsc/internal/testutil/harnessutil/recorderfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `OutputRecorderFS` is a `vfs.FS` decorator that records every `WriteFile`
// call so [CompilationResult](crate::harnessutil::CompilationResult) can sort
// emitted outputs into a deterministic order.
//
// PORT: `*TestFile` is `Arc<TestFile>` (the `Vfs` trait requires `Send +
// Sync`, so `Rc` is not an option); `map[*TestFile]` pointer-key lookups in
// `newCompilationResult` become `Arc::as_ptr` identity.

use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use rustc_hash::FxHashMap;
use tsc_tspath::{self as tspath, RootedDirectoryPath, RootedFilePath, RootedPath};
use tsc_vfs::fs::{FileInfo, FsError};
use tsc_vfs::{Entries, Vfs};

use super::TestFile;

/// `type OutputRecorderFS struct`.
pub struct OutputRecorderFs {
    inner: Arc<dyn Vfs>,
    outputs: Mutex<OutputRecorderState>,
}

/// `recordedOutput`.
pub struct RecordedOutput {
    pub path: RootedFilePath,
    pub file: Arc<TestFile>,
}

#[derive(Default)]
struct OutputRecorderState {
    map: FxHashMap<RootedFilePath, usize>,
    outputs: Vec<RecordedOutput>,
}

/// `NewOutputRecorderFS`.
///
// PORT: Go returns `vfs.FS` and `newCompilationResult` recovers the recorder
// with a type assertion; the port returns the concrete `Arc<OutputRecorderFs>`
// so the caller can keep a typed handle (see [`CachedCompilerHost::recorder`]).
pub fn new_output_recorder_fs(fs: Arc<dyn Vfs>) -> Arc<OutputRecorderFs> {
    Arc::new(OutputRecorderFs {
        inner: fs,
        outputs: Mutex::new(OutputRecorderState::default()),
    })
}

impl OutputRecorderFs {
    /// `fs.recordedOutputs()`.
    pub fn recorded_outputs(&self) -> Vec<RecordedOutput> {
        let state = self.outputs.lock().unwrap();
        state
            .outputs
            .iter()
            .map(|o| RecordedOutput {
                path: o.path.clone(),
                file: o.file.clone(),
            })
            .collect()
    }
}

// `vfs.FS` implementation — everything delegates to `inner` except `WriteFile`.
impl Vfs for OutputRecorderFs {
    fn case_sensitivity(&self) -> tsc_tspath::CaseSensitivity {
        self.inner.case_sensitivity()
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.inner.file_exists(path)
    }

    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.inner.read_file(path)
    }

    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.write_file(path, data)?;
        let real_path = tspath::rooted_file_path_from_path(self.inner.realpath(&path.as_path()));
        let mut state = self.outputs.lock().unwrap();
        let file = Arc::new(TestFile {
            unit_name: real_path.as_string().to_string(),
            content: data.to_string(),
        });
        if let Some(&index) = state.map.get(&real_path) {
            state.outputs[index] = RecordedOutput {
                path: real_path,
                file,
            };
        } else {
            let index = state.outputs.len();
            state.map.insert(real_path.clone(), index);
            state.outputs.push(RecordedOutput {
                path: real_path,
                file,
            });
        }
        Ok(())
    }

    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.append_file(path, data)
    }

    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.inner.remove(path)
    }

    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.inner.chtimes(path, a_time, m_time)
    }

    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.inner.directory_exists(path)
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.inner.get_accessible_entries(path)
    }

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.inner.stat(path)
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.inner.realpath(path)
    }

    /// Go promotes the embedded `vfs.FS`'s `FsWithSys` implementation when the
    /// inner FS is an `iovfs.FsWithSys`; delegating preserves that (calls on
    /// the returned object bypass the recorder, as in Go).
    fn as_fs_with_sys(&self) -> Option<&dyn tsc_vfs::iovfs::FsWithSys> {
        self.inner.as_fs_with_sys()
    }
}
