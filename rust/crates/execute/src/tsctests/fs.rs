// Ported from tsc/internal/execute/tsctests/fs.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `testFs` embeds `vfs.FS` in Go; the Rust port is a `Vfs` decorator that
//   delegates every member to `inner` except `read_file`/`write_file`/`remove`.
// - Go's `(contents string, ok bool)` becomes `Option<String>`, and `error`
//   returns become `FsError`.
// - `defaultLibs` is `*collections.SyncSet` — nil until the first missing
//   default lib is installed; the port models it as
//   `Mutex<Option<Arc<SyncSet<RootedPath>>>>` so the `FsDiffer`'s
//   `default_libs` closure observes the lazily-installed set.

use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use tsc_collections::SyncSet;
use tsc_testutil::fsbaselineutil;
use tsc_testutil::harnessutil::FAKE_TS_VERSION;
use tsc_tspath::{self as tspath, CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};
use tsc_vfs::fs::{FileInfo, FsError};
use tsc_vfs::vfs::{Entries, Vfs};

use crate::incremental::build_info::BuildInfo;
use crate::tsctests::readablebuildinfo::to_readable_build_info;

/// `type testFs struct` — fakes buildinfo versions and tracks written files.
pub struct TestFs {
    /// `FS` — the wrapped filesystem.
    pub inner: Arc<dyn Vfs>,
    /// `defaultLibs` — `None` is Go's nil `*SyncSet`.
    default_libs: Mutex<Option<Arc<SyncSet<RootedPath>>>>,
    /// `writtenFiles` — shared with the `FsDiffer` (`FsDiffer::new`'s
    /// `written_files` argument must be this set's `Arc` clone).
    pub written_files: Arc<SyncSet<RootedFilePath>>,
}

impl TestFs {
    /// Wraps `inner` (`vfstest.FromMap*` output in `newTscSystem`).
    pub fn new(inner: Arc<dyn Vfs>) -> TestFs {
        TestFs {
            inner,
            default_libs: Mutex::new(None),
            written_files: Arc::new(SyncSet::new()),
        }
    }

    /// `defaultLibs` — `None` is Go's nil.
    pub fn default_libs(&self) -> Option<Arc<SyncSet<RootedPath>>> {
        self.default_libs
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// `defaultLibs` get-or-init — `if s.fs.defaultLibs == nil { s.fs.defaultLibs = &SyncSet{} }`.
    pub fn default_libs_or_init(&self) -> Arc<SyncSet<RootedPath>> {
        self.default_libs
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get_or_insert_with(|| Arc::new(SyncSet::new()))
            .clone()
    }

    /// `removeIgnoreLibPath`.
    fn remove_ignore_lib_path(&self, path: &RootedPath) {
        if let Some(default_libs) = self.default_libs() {
            default_libs.delete(path);
        }
    }

    /// `readFileHandlingBuildInfo`.
    fn read_file_handling_build_info(&self, path: &RootedFilePath) -> Option<String> {
        let contents = self.inner.read_file(path)?;
        if path.extension_is(tspath::EXTENSION_TS_BUILD_INFO) {
            // read buildinfo and modify version
            if let Ok(mut build_info) =
                tsc_json::unmarshal::<BuildInfo>(contents.as_bytes(), &[])
            {
                if build_info.version == FAKE_TS_VERSION {
                    build_info.version = tsc_core::version::version().to_string();
                    let new_contents = tsc_json::marshal(&build_info, &[]).unwrap_or_else(|err| {
                        panic!(
                            "testFs.ReadFile: failed to marshal build info after fixing version: {err}"
                        )
                    });
                    return Some(
                        String::from_utf8(new_contents).expect("marshal produces utf-8"),
                    );
                }
            }
        }
        Some(contents)
    }

    /// `writeFileHandlingBuildInfo`.
    fn write_file_handling_build_info(
        &self,
        path: &RootedFilePath,
        data: &str,
    ) -> Result<(), FsError> {
        let mut data = data.to_string();
        if path.extension_is(tspath::EXTENSION_TS_BUILD_INFO) {
            match tsc_json::unmarshal::<BuildInfo>(data.as_bytes(), &[]) {
                Ok(mut build_info) => {
                    if build_info.version == tsc_core::version::version() {
                        // Change it to harnessutil.FakeTSVersion
                        build_info.version = FAKE_TS_VERSION.to_string();
                        match tsc_json::marshal(&build_info, &[]) {
                            Ok(new_data) => {
                                data = String::from_utf8(new_data)
                                    .expect("marshal produces utf-8");
                            }
                            Err(err) => {
                                return Err(FsError::Message(format!(
                                    "testFs.WriteFile: failed to marshal build info after fixing version: {err}"
                                )));
                            }
                        }
                    }
                    // Write readable build info version
                    let sanitized = fsbaselineutil::sanitize_internal_symbol_name(data.as_bytes());
                    let readable = to_readable_build_info(
                        &build_info,
                        &String::from_utf8_lossy(&sanitized),
                    );
                    // Go calls `f.WriteFile` — the `testFs` wrapper, so the
                    // `.readable.baseline.txt` file also lands in
                    // `written_files`.
                    self.write_file(&path.append_suffix(".readable.baseline.txt"), &readable)
                        .map_err(|err| {
                            FsError::Message(format!(
                                "testFs.WriteFile: failed to write readable build info: {err}"
                            ))
                        })?;
                }
                Err(err) => {
                    panic!(
                        "testFs.WriteFile: failed to unmarshal build info: - use underlying FS's write method if this is intended use for testcase{err}"
                    );
                }
            }
        }
        self.inner.write_file(path, &data)
    }
}

impl Vfs for TestFs {
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.inner.case_sensitivity()
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.inner.file_exists(path)
    }

    /// `(*testFs) ReadFile`.
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.remove_ignore_lib_path(&path.as_path());
        self.read_file_handling_build_info(path)
    }

    /// `(*testFs) WriteFile`.
    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.remove_ignore_lib_path(&path.as_path());
        self.written_files.add(path.clone());
        self.write_file_handling_build_info(path, data)
    }

    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.append_file(path, data)
    }

    /// `(*testFs) Remove`.
    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.remove_ignore_lib_path(path);
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

    /// `sys.fs.(iovfs.FsWithSys)` fails in Go — `testFs` only embeds `vfs.FS`
    /// and does not expose `FSys`; `None` mirrors the failed assertion.
    /// (`FsDiffer` is built from `sys.fs.FS` — the *inner* fs — which does
    /// implement it.)
    fn as_fs_with_sys(&self) -> Option<&dyn tsc_vfs::iovfs::FsWithSys> {
        None
    }
}
