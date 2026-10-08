// Ported from tsc/internal/vfs/vfsmock/mock_generated.go + wrapper.go
// @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: mock_generated.go is moq boilerplate: a [Vfs] whose methods dispatch
// to `XxxFunc` fields and record arguments in `calls`. Rust models the func
// fields as Option<Box<dyn Fn>> and the call log as a Mutex<Calls> struct.

#[cfg(test)]
mod tests;

use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::fs::{FileInfo, FsError};
use crate::vfs::{Entries, Vfs};

/// FsMock is vfsmock.FSMock: a mock implementation of [Vfs].
///
/// Each `*_func` field mocks the corresponding method; a missing func panics,
/// matching moq's behavior.
#[derive(Default)]
pub struct FsMock {
    pub append_file_func:
        Option<Box<dyn Fn(&RootedFilePath, &str) -> Result<(), FsError> + Send + Sync>>,
    pub case_sensitivity_func: Option<Box<dyn Fn() -> CaseSensitivity + Send + Sync>>,
    pub chtimes_func: Option<
        Box<dyn Fn(&RootedPath, SystemTime, SystemTime) -> Result<(), FsError> + Send + Sync>,
    >,
    pub directory_exists_func:
        Option<Box<dyn Fn(&RootedDirectoryPath) -> bool + Send + Sync>>,
    pub file_exists_func: Option<Box<dyn Fn(&RootedFilePath) -> bool + Send + Sync>>,
    pub get_accessible_entries_func:
        Option<Box<dyn Fn(&RootedDirectoryPath) -> Entries + Send + Sync>>,
    pub read_file_func: Option<Box<dyn Fn(&RootedFilePath) -> Option<String> + Send + Sync>>,
    pub realpath_func: Option<Box<dyn Fn(&RootedPath) -> RootedPath + Send + Sync>>,
    pub remove_func: Option<Box<dyn Fn(&RootedPath) -> Result<(), FsError> + Send + Sync>>,
    pub stat_func:
        Option<Box<dyn Fn(&RootedPath) -> Option<Arc<dyn FileInfo>> + Send + Sync>>,
    pub write_file_func:
        Option<Box<dyn Fn(&RootedFilePath, &str) -> Result<(), FsError> + Send + Sync>>,

    /// calls tracks calls to the methods.
    calls: Mutex<Calls>,
}

/// Calls is FSMock.calls: per-method argument logs.
#[derive(Default, Debug)]
pub struct Calls {
    pub append_file: Vec<AppendFileCall>,
    pub case_sensitivity: Vec<()>,
    pub chtimes: Vec<ChtimesCall>,
    pub directory_exists: Vec<DirectoryExistsCall>,
    pub file_exists: Vec<FileExistsCall>,
    pub get_accessible_entries: Vec<GetAccessibleEntriesCall>,
    pub read_file: Vec<ReadFileCall>,
    pub realpath: Vec<RealpathCall>,
    pub remove: Vec<RemoveCall>,
    pub stat: Vec<StatCall>,
    pub write_file: Vec<WriteFileCall>,
}

#[derive(Debug)]
pub struct AppendFileCall {
    pub path: RootedFilePath,
    pub data: String,
}
#[derive(Debug)]
pub struct ChtimesCall {
    pub path: RootedPath,
    pub a_time: SystemTime,
    pub m_time: SystemTime,
}
#[derive(Debug)]
pub struct DirectoryExistsCall {
    pub path: RootedDirectoryPath,
}
#[derive(Debug)]
pub struct FileExistsCall {
    pub path: RootedFilePath,
}
#[derive(Debug)]
pub struct GetAccessibleEntriesCall {
    pub path: RootedDirectoryPath,
}
#[derive(Debug)]
pub struct ReadFileCall {
    pub path: RootedFilePath,
}
#[derive(Debug)]
pub struct RealpathCall {
    pub path: RootedPath,
}
#[derive(Debug)]
pub struct RemoveCall {
    pub path: RootedPath,
}
#[derive(Debug)]
pub struct StatCall {
    pub path: RootedPath,
}
#[derive(Debug)]
pub struct WriteFileCall {
    pub path: RootedFilePath,
    pub data: String,
}

impl FsMock {
    /// calls returns a snapshot-independent handle to the calls log.
    /// PORT: moq exposes `mock.calls` for direct field access; here tests call
    /// `mock.calls()` and inspect the returned guard.
    pub fn calls(&self) -> std::sync::MutexGuard<'_, Calls> {
        self.calls.lock().unwrap()
    }

    /// calls_that returns the recorded calls for one method.
    pub fn len_calls(&self) -> usize {
        let c = self.calls.lock().unwrap();
        c.append_file.len()
            + c.case_sensitivity.len()
            + c.chtimes.len()
            + c.directory_exists.len()
            + c.file_exists.len()
            + c.get_accessible_entries.len()
            + c.read_file.len()
            + c.realpath.len()
            + c.remove.len()
            + c.stat.len()
            + c.write_file.len()
    }
}

impl Vfs for FsMock {
    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.calls.lock().unwrap().append_file.push(AppendFileCall {
            path: path.clone(),
            data: data.to_string(),
        });
        match &self.append_file_func {
            None => panic!("mock out the AppendFile method"),
            Some(f) => f(path, data),
        }
    }

    fn case_sensitivity(&self) -> CaseSensitivity {
        self.calls.lock().unwrap().case_sensitivity.push(());
        match &self.case_sensitivity_func {
            None => panic!("mock out the CaseSensitivity method"),
            Some(f) => f(),
        }
    }

    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.calls.lock().unwrap().chtimes.push(ChtimesCall {
            path: path.clone(),
            a_time,
            m_time,
        });
        match &self.chtimes_func {
            None => panic!("mock out the Chtimes method"),
            Some(f) => f(path, a_time, m_time),
        }
    }

    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.calls
            .lock()
            .unwrap()
            .directory_exists
            .push(DirectoryExistsCall { path: path.clone() });
        match &self.directory_exists_func {
            None => panic!("mock out the DirectoryExists method"),
            Some(f) => f(path),
        }
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.calls.lock().unwrap().file_exists.push(FileExistsCall {
            path: path.clone(),
        });
        match &self.file_exists_func {
            None => panic!("mock out the FileExists method"),
            Some(f) => f(path),
        }
    }

    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.calls
            .lock()
            .unwrap()
            .get_accessible_entries
            .push(GetAccessibleEntriesCall { path: path.clone() });
        match &self.get_accessible_entries_func {
            None => panic!("mock out the GetAccessibleEntries method"),
            Some(f) => f(path),
        }
    }

    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.calls.lock().unwrap().read_file.push(ReadFileCall {
            path: path.clone(),
        });
        match &self.read_file_func {
            None => panic!("mock out the ReadFile method"),
            Some(f) => f(path),
        }
    }

    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.calls.lock().unwrap().realpath.push(RealpathCall {
            path: path.clone(),
        });
        match &self.realpath_func {
            None => panic!("mock out the Realpath method"),
            Some(f) => f(path),
        }
    }

    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.calls.lock().unwrap().remove.push(RemoveCall {
            path: path.clone(),
        });
        match &self.remove_func {
            None => panic!("mock out the Remove method"),
            Some(f) => f(path),
        }
    }

    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.calls.lock().unwrap().stat.push(StatCall {
            path: path.clone(),
        });
        match &self.stat_func {
            None => panic!("mock out the Stat method"),
            Some(f) => f(path),
        }
    }

    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.calls.lock().unwrap().write_file.push(WriteFileCall {
            path: path.clone(),
            data: data.to_string(),
        });
        match &self.write_file_func {
            None => panic!("mock out the WriteFile method"),
            Some(f) => f(path, data),
        }
    }
}

/// wrap is vfsmock.Wrap: wraps a [Vfs] and returns an FsMock which calls it.
pub fn wrap(fs: Arc<dyn Vfs>) -> Arc<FsMock> {
    let f = fs.clone();
    let mock = FsMock {
        directory_exists_func: Some(Box::new(move |p| f.directory_exists(p))),
        file_exists_func: {
            let f = fs.clone();
            Some(Box::new(move |p| f.file_exists(p)))
        },
        get_accessible_entries_func: {
            let f = fs.clone();
            Some(Box::new(move |p| f.get_accessible_entries(p)))
        },
        read_file_func: {
            let f = fs.clone();
            Some(Box::new(move |p| f.read_file(p)))
        },
        realpath_func: {
            let f = fs.clone();
            Some(Box::new(move |p| f.realpath(p)))
        },
        remove_func: {
            let f = fs.clone();
            Some(Box::new(move |p| f.remove(p)))
        },
        chtimes_func: {
            let f = fs.clone();
            Some(Box::new(move |p, a, m| f.chtimes(p, a, m)))
        },
        stat_func: {
            let f = fs.clone();
            Some(Box::new(move |p| f.stat(p)))
        },
        case_sensitivity_func: {
            let f = fs.clone();
            Some(Box::new(move || f.case_sensitivity()))
        },
        write_file_func: {
            let f = fs.clone();
            Some(Box::new(move |p, d| f.write_file(p, d)))
        },
        append_file_func: {
            let f = fs.clone();
            Some(Box::new(move |p, d| f.append_file(p, d)))
        },
        ..Default::default()
    };
    Arc::new(mock)
}
