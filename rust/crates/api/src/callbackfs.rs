// Ported from tsc/internal/api/callbackfs.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `conn ipc.Conn` → `Arc<dyn ipc::Conn>`; `ctx context.Context` →
//   `tsc_core::context::Context`. Go sets both fields after construction via
//   `SetConnection`; `Vfs` methods take `&self`, so they live behind a
//   `Mutex` (`SetConnection` writes both atomically, as Go does).
// - `conn.Call(ctx, name, arg)` marshals `arg` inside `Call`; the ported
//   `ipc::Conn::call` takes pre-marshaled `Option<json::Value>`, so `call`
//   runs `ipc::marshal_params` first — marshal failures arrive on the same
//   error channel Go uses.
// - `json.Value` results → `Option<json::Value>` (`None` is a nil/absent
//   `jsontext.Value`). `json.Unmarshal(nil, &v)` errors and callers
//   `panic(err)`; `unmarshal_callback_value` reproduces that by decoding an
//   empty byte slice, which serde_json also rejects. The `value` member is
//   decoded through a map so a literal `null` keeps its raw bytes — Go's
//   `json.Unmarshal(null, &v)` is a no-op success that leaves the zero
//   value, which serde's `Option<RawValue>` would wrongly conflate with an
//   absent member.
// - Go `panic(err)` → `panic!("{e}")`: the panic payload is the rendered
//   error message, matching what `fmt.Sprint(recover())` observes.
// - `WriteFile`/`Remove` return `error`; the `Vfs` trait's error channel is
//   `FsError`, so an ipc failure becomes `FsError::Message(err.to_string())`
//   — only the message text reaches the client either way.
// - `time.Parse(time.RFC3339Nano, mtime)` → `parse_rfc3339_nano`, a local
//   strict parser (no approved datetime crate exists in the workspace).
// - `rawEntries *struct{...}` decodes JSON `null` to a nil pointer whose
//   field access panics in Go; here `Option<RawEntries>` + `expect` panics
//   for the same input.

use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use tsc_core::context::Context;
use tsc_ipc as ipc;
use tsc_json as json;
use tsc_tspath::{
    CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath,
    rooted_directory_path_from_normalized, rooted_file_path_from_normalized, to_rooted_path,
};
use tsc_vfs::fs::{
    FileInfo, FileMode, FsError, MODE_CHAR_DEVICE, MODE_DEVICE, MODE_DIR, MODE_IRREGULAR,
    MODE_NAMED_PIPE, MODE_SETGID, MODE_SETUID, MODE_SOCKET, MODE_STICKY, MODE_SYMLINK,
};
use tsc_vfs::{Entries, Vfs};

// Callback names that can be enabled
const CALLBACK_READ_FILE: &str = "readFile";
const CALLBACK_FILE_EXISTS: &str = "fileExists";
const CALLBACK_DIRECTORY_EXISTS: &str = "directoryExists";
const CALLBACK_GET_ACCESSIBLE_ENTRIES: &str = "getAccessibleEntries";
const CALLBACK_REALPATH: &str = "realpath";
const CALLBACK_STAT: &str = "stat";
const CALLBACK_WRITE_FILE: &str = "writeFile";
const CALLBACK_REMOVE_FILE: &str = "removeFile";

/// `isCallbackName`
fn is_callback_name(name: &str) -> bool {
    matches!(
        name,
        CALLBACK_READ_FILE
            | CALLBACK_FILE_EXISTS
            | CALLBACK_DIRECTORY_EXISTS
            | CALLBACK_GET_ACCESSIBLE_ENTRIES
            | CALLBACK_REALPATH
            | CALLBACK_STAT
            | CALLBACK_WRITE_FILE
            | CALLBACK_REMOVE_FILE
    )
}

/// `callbackFS` wraps a base filesystem and delegates certain operations
/// to the client via RPC callbacks. This allows the API client to provide
/// a virtual filesystem (e.g., in-memory files for testing).
///
/// The callbacks to enable are specified at construction time via the
/// --callbacks CLI flag. The connection is set via `set_connection` after
/// the transport connection is established.
pub struct CallbackFs {
    base: Arc<dyn Vfs>,
    enabled_callbacks: FxHashSet<String>,
    realpath_identity: bool,
    fake_stat: bool,
    write_file_noop: bool,
    remove_file_noop: bool,
    error_callbacks: FxHashSet<String>,
    case_sensitive: Option<bool>,

    /// `conn` and `ctx` — set after the connection is established.
    conn: Mutex<Option<CallbackConnection>>,
}

/// The `fs.conn`/`fs.ctx` pair installed by `SetConnection`.
struct CallbackConnection {
    ctx: Context,
    conn: Arc<dyn ipc::Conn>,
}

/// `newCallbackFS` creates a new `callbackFS` wrapping the given base
/// filesystem. The callbacks slice specifies which filesystem operations
/// should be delegated to the client (e.g., "readFile", "fileExists").
pub fn new_callback_fs(
    base: Arc<dyn Vfs>,
    callbacks: &[String],
    case_sensitive: Option<bool>,
) -> CallbackFs {
    let mut enabled =
        FxHashSet::with_capacity_and_hasher(callbacks.len(), Default::default());
    let mut error_callbacks = FxHashSet::default();
    for cb in callbacks {
        // `strings.CutSuffix(cb, ":error")`
        if let Some(name) = cb.strip_suffix(":error") {
            if !is_callback_name(name) {
                panic!("unknown callback name: {name}");
            }
            error_callbacks.insert(name.to_string());
            continue;
        }
        if cb == "realpath:identity"
            || cb == "stat:fakeStat"
            || cb == "writeFile:noop"
            || cb == "removeFile:noop"
        {
            continue;
        }
        if !is_callback_name(cb) {
            panic!("unknown callback name: {cb}");
        }
        enabled.insert(cb.clone());
    }
    CallbackFs {
        base,
        enabled_callbacks: enabled,
        // `slices.Contains(callbacks, "...")`
        realpath_identity: callbacks.iter().any(|cb| cb == "realpath:identity"),
        fake_stat: callbacks.iter().any(|cb| cb == "stat:fakeStat"),
        write_file_noop: callbacks.iter().any(|cb| cb == "writeFile:noop"),
        remove_file_noop: callbacks.iter().any(|cb| cb == "removeFile:noop"),
        error_callbacks,
        case_sensitive,
        conn: Mutex::new(None),
    }
}

impl CallbackFs {
    /// `SetConnection` sets the RPC connection for callbacks.
    /// This must be called after the transport connection is established
    /// but before any filesystem operations that need callbacks.
    pub fn set_connection(&self, ctx: Context, conn: Arc<dyn ipc::Conn>) {
        *self.conn.lock().unwrap() = Some(CallbackConnection { ctx, conn });
    }

    /// `fs.isEnabled` returns true if the named callback is enabled.
    fn is_enabled(&self, name: &str) -> bool {
        self.enabled_callbacks.contains(name)
    }

    /// `fs.call` invokes a callback on the client and returns the result.
    fn call(
        &self,
        name: &str,
        arg: &(impl Serialize + ?Sized),
    ) -> Result<Option<json::Value>, ipc::Error> {
        let (ctx, conn) = {
            let state = self.conn.lock().unwrap();
            match state.as_ref() {
                Some(state) => (state.ctx.clone(), state.conn.clone()),
                None => {
                    return Err(ipc::Error::Message(format!(
                        "CallbackFS: {name} called before connection set"
                    )));
                }
            }
        };
        // `json.Marshal(arg)` happens inside Go's `conn.Call`.
        let params = ipc::marshal_params(arg)?;
        conn.call(&ctx, name, Some(params))
    }

    /// `fs.panicIfError`
    fn panic_if_error(&self, name: &str) {
        if self.error_callbacks.contains(name) {
            panic!("filesystem operation configured with serverFS.error: {name}");
        }
    }

    /// `fs.fakeStatForPath`
    fn fake_stat_for_path(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        if self.directory_exists(&rooted_directory_path_from_normalized(path.as_string())) {
            return Some(Arc::new(CallbackFileInfo {
                name: path.base_name().to_string(),
                size: 0,
                mode: MODE_DIR | 0o555,
                mod_time: UNIX_EPOCH, // `time.Time{}` zero value
            }));
        }
        if self.file_exists(&rooted_file_path_from_normalized(path.as_string())) {
            return Some(Arc::new(CallbackFileInfo {
                name: path.base_name().to_string(),
                size: 0,
                mode: FileMode(0o444),
                mod_time: UNIX_EPOCH, // `time.Time{}` zero value
            }));
        }
        None
    }
}

/// `callbackResponse`
#[derive(Default)]
struct CallbackResponse {
    /// `Kind string` — a missing member leaves the zero value so the
    /// explicit empty-kind panic below is preserved.
    kind: String,
    /// `Value json.Value` — `None` is an absent member (Go's nil
    /// `jsontext.Value`); `Some` keeps the member bytes verbatim, including
    /// a literal `null`.
    value: Option<json::Value>,
}

impl<'de> Deserialize<'de> for CallbackResponse {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Struct-shaped member decode: Go's unmarshal ignores unknown
        // members and fails on non-object input; decoding through a map
        // gives the same shape while preserving `value`'s raw bytes —
        // `Option<RawValue>` field decoding would collapse a JSON `null`
        // into the absent case.
        let mut members: FxHashMap<String, json::Value> =
            Deserialize::deserialize(deserializer)?;
        let kind = match members.remove("kind") {
            Some(v) => String::deserialize(&*v).map_err(serde::de::Error::custom)?,
            None => String::new(),
        };
        Ok(CallbackResponse {
            kind,
            value: members.remove("value"),
        })
    }
}

/// `json.Unmarshal(result, &response)` / `json.Unmarshal(response.Value,
/// &v)` — an absent `json.Value` unmarshals from empty bytes, which fails
/// exactly like Go's unmarshal of a nil `jsontext.Value`; callers `panic`.
/// `json.Unmarshal(null, &v)` on a fresh target is a no-op success leaving
/// the zero value — serde_json rejects `null` for scalar targets, so it is
/// intercepted here.
fn unmarshal_callback_value<T>(value: Option<&json::Value>) -> T
where
    T: serde::de::DeserializeOwned + Default,
{
    let bytes: &[u8] = value.map_or(b"", |v| v.get().as_bytes());
    if bytes == b"null" {
        return T::default();
    }
    json::unmarshal(bytes, &[]).unwrap_or_else(|e| panic!("{e}"))
}

/// `decodeCallbackResponse`
fn decode_callback_response(name: &str, result: Option<json::Value>) -> CallbackResponse {
    let response: CallbackResponse = unmarshal_callback_value(result.as_ref());
    if response.kind.is_empty() {
        panic!("filesystem callback response is missing a kind");
    }
    if response.kind == "error" {
        panic!("filesystem callback returned serverFS.error: {name}");
    }
    response
}

/// `invalidCallbackResponse`
fn invalid_callback_response(name: &str, response: &CallbackResponse) -> ! {
    panic!("invalid {name} callback response kind: {}", response.kind)
}

/// `callbackFileInfo`
struct CallbackFileInfo {
    name: String,
    size: i64,
    mode: FileMode,
    mod_time: SystemTime,
}

/// `callbackFileInfo`'s `fs.FileInfo` implementation.
impl FileInfo for CallbackFileInfo {
    /// `Name`
    fn name(&self) -> String {
        self.name.clone()
    }
    /// `Size`
    fn size(&self) -> i64 {
        self.size
    }
    /// `Mode`
    fn mode(&self) -> FileMode {
        self.mode
    }
    /// `ModTime`
    fn mod_time(&self) -> SystemTime {
        self.mod_time
    }
    /// `IsDir` — `info.mode.IsDir()`
    fn is_dir(&self) -> bool {
        self.mode.is_dir()
    }
    /// `Sys` — Go returns nil.
    fn sys(&self) -> Option<Arc<dyn std::any::Any + Send + Sync>> {
        None
    }
}

/// `vfs.FS` for `callbackFS`.
impl Vfs for CallbackFs {
    /// `CaseSensitivity`
    fn case_sensitivity(&self) -> CaseSensitivity {
        if let Some(case_sensitive) = self.case_sensitive {
            if case_sensitive {
                return CaseSensitivity::CaseSensitive;
            }
            return CaseSensitivity::CaseInsensitive;
        }
        self.base.case_sensitivity()
    }

    /// `ReadFile`
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.panic_if_error(CALLBACK_READ_FILE);
        if self.is_enabled(CALLBACK_READ_FILE) {
            let result = self
                .call(CALLBACK_READ_FILE, path.as_string())
                .unwrap_or_else(|e| panic!("{e}"));
            let response = decode_callback_response(CALLBACK_READ_FILE, result);
            return match response.kind.as_str() {
                "value" => Some(unmarshal_callback_value(response.value.as_ref())),
                "missing" => None,
                "useOS" => self.base.read_file(path),
                _ => invalid_callback_response(CALLBACK_READ_FILE, &response),
            };
        }
        self.base.read_file(path)
    }

    /// `FileExists`
    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.panic_if_error(CALLBACK_FILE_EXISTS);
        if self.is_enabled(CALLBACK_FILE_EXISTS) {
            let result = self
                .call(CALLBACK_FILE_EXISTS, path.as_string())
                .unwrap_or_else(|e| panic!("{e}"));
            let response = decode_callback_response(CALLBACK_FILE_EXISTS, result);
            return match response.kind.as_str() {
                "value" => unmarshal_callback_value(response.value.as_ref()),
                "useOS" => self.base.file_exists(path),
                _ => invalid_callback_response(CALLBACK_FILE_EXISTS, &response),
            };
        }
        self.base.file_exists(path)
    }

    /// `DirectoryExists`
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.panic_if_error(CALLBACK_DIRECTORY_EXISTS);
        if self.is_enabled(CALLBACK_DIRECTORY_EXISTS) {
            let result = self
                .call(CALLBACK_DIRECTORY_EXISTS, path.as_string())
                .unwrap_or_else(|e| panic!("{e}"));
            let response = decode_callback_response(CALLBACK_DIRECTORY_EXISTS, result);
            return match response.kind.as_str() {
                "value" => unmarshal_callback_value(response.value.as_ref()),
                "useOS" => self.base.directory_exists(path),
                _ => invalid_callback_response(CALLBACK_DIRECTORY_EXISTS, &response),
            };
        }
        self.base.directory_exists(path)
    }

    /// `GetAccessibleEntries`
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.panic_if_error(CALLBACK_GET_ACCESSIBLE_ENTRIES);
        if self.is_enabled(CALLBACK_GET_ACCESSIBLE_ENTRIES) {
            let result = self
                .call(CALLBACK_GET_ACCESSIBLE_ENTRIES, path.as_string())
                .unwrap_or_else(|e| panic!("{e}"));
            let response = decode_callback_response(CALLBACK_GET_ACCESSIBLE_ENTRIES, result);
            return match response.kind.as_str() {
                "value" => {
                    // `rawEntries *struct{ Files; Directories; Symlinks }` —
                    // a JSON `null` value is a nil pointer; Go panics
                    // dereferencing it.
                    let raw_entries: Option<RawEntries> =
                        unmarshal_callback_value(response.value.as_ref());
                    let raw_entries =
                        raw_entries.expect("getAccessibleEntries callback returned null");
                    let mut entries = Entries {
                        files: raw_entries.files,
                        directories: raw_entries.directories,
                        symlinks: None,
                    };
                    // `Symlinks != nil` — an explicitly empty array still
                    // means symlink information is available.
                    if let Some(symlinks) = raw_entries.symlinks {
                        entries.symlinks = Some(symlinks.into_iter().collect());
                    }
                    entries
                }
                "useOS" => self.base.get_accessible_entries(path),
                _ => invalid_callback_response(CALLBACK_GET_ACCESSIBLE_ENTRIES, &response),
            };
        }
        self.base.get_accessible_entries(path)
    }

    /// `Realpath`
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.panic_if_error(CALLBACK_REALPATH);
        if self.is_enabled(CALLBACK_REALPATH) {
            let result = self
                .call(CALLBACK_REALPATH, path.as_string())
                .unwrap_or_else(|e| panic!("{e}"));
            let response = decode_callback_response(CALLBACK_REALPATH, result);
            return match response.kind.as_str() {
                "value" => {
                    // `tspath.ToRootedPath(realpath, path.Directory())`
                    let realpath: String = unmarshal_callback_value(response.value.as_ref());
                    to_rooted_path(&realpath, &path.directory())
                }
                "identity" => path.clone(),
                "useOS" => self.base.realpath(path),
                _ => invalid_callback_response(CALLBACK_REALPATH, &response),
            };
        }
        if self.realpath_identity {
            return path.clone();
        }
        self.base.realpath(path)
    }

    /// `Stat`
    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.panic_if_error(CALLBACK_STAT);
        if self.is_enabled(CALLBACK_STAT) {
            let result = self
                .call(CALLBACK_STAT, path.as_string())
                .unwrap_or_else(|e| panic!("{e}"));
            let response = decode_callback_response(CALLBACK_STAT, result);
            return match response.kind.as_str() {
                "value" => {
                    let stat: CallbackStat = unmarshal_callback_value(response.value.as_ref());
                    let mod_time = parse_rfc3339_nano(&stat.mtime).unwrap_or_else(|| {
                        panic!(
                            "parsing time {:?} as \"2006-01-02T15:04:05.999999999Z07:00\": cannot parse",
                            stat.mtime
                        )
                    });
                    Some(Arc::new(CallbackFileInfo {
                        name: path.base_name().to_string(),
                        size: stat.size,
                        mode: node_file_mode_to_go_file_mode(stat.mode),
                        mod_time,
                    }))
                }
                "missing" => None,
                "fakeStat" => self.fake_stat_for_path(path),
                "useOS" => self.base.stat(path),
                _ => invalid_callback_response(CALLBACK_STAT, &response),
            };
        }
        if self.fake_stat {
            return self.fake_stat_for_path(path);
        }
        self.base.stat(path)
    }

    /// `WriteFile`
    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.panic_if_error(CALLBACK_WRITE_FILE);
        if self.is_enabled(CALLBACK_WRITE_FILE) {
            let payload = WriteFileParams {
                path: path.as_string(),
                data,
            };
            let result = self
                .call(CALLBACK_WRITE_FILE, &payload)
                .map_err(|e| FsError::Message(e.to_string()))?;
            let response = decode_callback_response(CALLBACK_WRITE_FILE, result);
            match response.kind.as_str() {
                "value" | "noop" => return Ok(()),
                "useOS" => return self.base.write_file(path, data),
                _ => invalid_callback_response(CALLBACK_WRITE_FILE, &response),
            }
        }
        if self.write_file_noop {
            return Ok(());
        }
        self.base.write_file(path, data)
    }

    /// `AppendFile` — always delegates to base (no callback support).
    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.base.append_file(path, data)
    }

    /// `Remove`
    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.panic_if_error(CALLBACK_REMOVE_FILE);
        if self.is_enabled(CALLBACK_REMOVE_FILE) {
            let result = self
                .call(CALLBACK_REMOVE_FILE, path.as_string())
                .map_err(|e| FsError::Message(e.to_string()))?;
            let response = decode_callback_response(CALLBACK_REMOVE_FILE, result);
            match response.kind.as_str() {
                "value" | "noop" => return Ok(()),
                "useOS" => return self.base.remove(path),
                _ => invalid_callback_response(CALLBACK_REMOVE_FILE, &response),
            }
        }
        if self.remove_file_noop {
            return Ok(());
        }
        self.base.remove(path)
    }

    /// `Chtimes` — always delegates to base (no callback support).
    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.base.chtimes(path, a_time, m_time)
    }

    /// `as_concrete` — models `fs.(*callbackFS)`-style assertions.
    fn as_concrete(&self) -> Option<&dyn std::any::Any> {
        Some(self)
    }
}

/// The `getAccessibleEntries` callback's `"value"` payload —
/// `struct { Files; Directories; Symlinks []string }`.
#[derive(Deserialize)]
struct RawEntries {
    #[serde(default)]
    files: Vec<String>,
    #[serde(default)]
    directories: Vec<String>,
    symlinks: Option<Vec<String>>,
}

/// The `stat` callback's `"value"` payload —
/// `struct { Mode uint32; Size int64; MTime string }`.
#[derive(Default, Deserialize)]
struct CallbackStat {
    #[serde(default)]
    mode: u32,
    #[serde(default)]
    size: i64,
    #[serde(default)]
    mtime: String,
}

/// The `writeFile` callback's argument —
/// `struct { Path string; Data string }`.
#[derive(Serialize)]
struct WriteFileParams<'a> {
    path: &'a str,
    data: &'a str,
}

/// `nodeFileModeToGoFileMode`
fn node_file_mode_to_go_file_mode(mode: u32) -> FileMode {
    let mut result = FileMode(mode & 0o777);
    if mode & 0o4000 != 0 {
        result = result | MODE_SETUID;
    }
    if mode & 0o2000 != 0 {
        result = result | MODE_SETGID;
    }
    if mode & 0o1000 != 0 {
        result = result | MODE_STICKY;
    }
    match mode & 0o170000 {
        0o010000 => result = result | MODE_NAMED_PIPE,
        0o020000 => result = result | MODE_DEVICE | MODE_CHAR_DEVICE,
        0o040000 => result = result | MODE_DIR,
        0o060000 => result = result | MODE_DEVICE,
        0o100000 => {
            // Regular file.
        }
        0o120000 => result = result | MODE_SYMLINK,
        0o140000 => result = result | MODE_SOCKET,
        _ => result = result | MODE_IRREGULAR,
    }
    result
}

/// `time.Parse(time.RFC3339Nano, s)` — strict RFC 3339 timestamp →
/// `SystemTime`. Accepts `YYYY-MM-DDTHH:MM:SS[.fraction](Z|±HH:MM)`; any
/// deviation (bad separators, out-of-range fields, trailing data) yields
/// `None`, and the caller panics as Go's `panic(err)` does.
fn parse_rfc3339_nano(s: &str) -> Option<SystemTime> {
    fn digits(b: &[u8]) -> Option<u64> {
        if b.is_empty() || !b.iter().all(u8::is_ascii_digit) {
            return None;
        }
        Some(b.iter().fold(0u64, |n, d| n * 10 + u64::from(d - b'0')))
    }

    let b = s.as_bytes();
    // Fixed prefix: "YYYY-MM-DDTHH:MM:SS" is 19 bytes.
    if b.len() < 20
        || b[4] != b'-'
        || b[7] != b'-'
        || b[10] != b'T'
        || b[13] != b':'
        || b[16] != b':'
    {
        return None;
    }
    let year = digits(&b[0..4])? as i64;
    let month = digits(&b[5..7])? as u32;
    let day = digits(&b[8..10])? as u32;
    let hour = digits(&b[11..13])? as u32;
    let minute = digits(&b[14..16])? as u32;
    let second = digits(&b[17..19])? as u32;

    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let days_in_month = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap => 29,
        2 => 28,
        _ => return None,
    };
    if !(1..=days_in_month).contains(&day)
        || hour >= 24
        || minute >= 60
        || second >= 60
    {
        return None;
    }

    // ".999999999" — optional fractional seconds; digits beyond nanosecond
    // precision are consumed but truncated, as Go's parser does.
    let mut i = 19;
    let mut nanos: u32 = 0;
    if b[i] == b'.' {
        i += 1;
        let start = i;
        while i < b.len() && b[i].is_ascii_digit() {
            if i - start < 9 {
                nanos = nanos * 10 + u32::from(b[i] - b'0');
            }
            i += 1;
        }
        if i == start {
            return None;
        }
        nanos *= 10u32.pow(9 - usize::min(i - start, 9) as u32);
    }

    // "Z07:00" — 'Z' or a ±HH:MM offset.
    if i >= b.len() {
        return None;
    }
    let offset_secs: i64 = match b[i] {
        b'Z' => {
            i += 1;
            0
        }
        sign @ (b'+' | b'-') => {
            if i + 6 > b.len() || b[i + 3] != b':' {
                return None;
            }
            let h = digits(&b[i + 1..i + 3])? as i64;
            let m = digits(&b[i + 4..i + 6])? as i64;
            if h >= 24 || m >= 60 {
                return None;
            }
            i += 6;
            let secs = h * 3600 + m * 60;
            if sign == b'-' { -secs } else { secs }
        }
        _ => return None,
    };
    if i != b.len() {
        return None;
    }

    // Howard Hinnant's days-from-civil: days since 1970-01-01.
    let y = if month <= 2 { year - 1 } else { year };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400; // [0, 399]
    let mp = (month + 9) % 12; // Mar=0 .. Feb=11
    let doy = (153 * mp + 2) / 5 + day - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy as i64;
    let days = era * 146097 + doe - 719468;

    let secs =
        days * 86_400 + i64::from(hour) * 3600 + i64::from(minute) * 60 + i64::from(second)
            - offset_secs;
    if secs >= 0 {
        UNIX_EPOCH.checked_add(Duration::new(secs as u64, nanos))
    } else if nanos == 0 {
        UNIX_EPOCH.checked_sub(Duration::new((-secs) as u64, 0))
    } else {
        // Borrow one second so the sub-second part stays positive.
        UNIX_EPOCH.checked_sub(Duration::new((-secs - 1) as u64, 1_000_000_000 - nanos))
    }
}
