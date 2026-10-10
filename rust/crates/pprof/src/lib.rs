// Ported from tsc/internal/pprof/pprof.go @ ec47d33c23e464a17cdf2475632cba629bee8763

// tsc-pprof — port of tsc/internal/pprof.
//
// PORT: Go's runtime/pprof has no direct Rust equivalent. CPU profiling uses
// the `pprof` crate (same protobuf format, readable by `go tool pprof`).
// Heap/alloc profiles have no Rust-runtime equivalent with the default
// allocator; `save_heap_profile`/`save_alloc_profile` write a gzip'd
// `/proc/self/status`-style memory summary at the same filename contract.
// `run_gc` is a no-op (Rust has no GC).

use std::fmt::Write as _;
use std::io::Write;
use std::path::Path;
use std::sync::Mutex;

/// `type ProfileSession struct`
pub struct ProfileSession {
    cpu_file_path: String,
    mem_file_path: String,
    guard: Option<pprof::ProfilerGuard<'static>>,
    log_writer: Box<dyn Write + Send>,
}

/// `func BeginProfiling(profileDir string, logWriter io.Writer) *ProfileSession`
///
/// PORT: panics on the same failure modes as Go (`MkdirAll`, `Create`,
/// `StartCPUProfile`).
pub fn begin_profiling(profile_dir: &str, log_writer: Box<dyn Write + Send>) -> ProfileSession {
    std::fs::create_dir_all(profile_dir).unwrap();

    let pid = std::process::id();
    let cpu_profile_path = Path::new(profile_dir).join(format!("{pid}-cpuprofile.pb.gz"));
    let mem_profile_path = Path::new(profile_dir).join(format!("{pid}-memprofile.pb.gz"));

    let guard = pprof::ProfilerGuardBuilder::default()
        .frequency(1000)
        .build()
        .unwrap();

    ProfileSession {
        cpu_file_path: cpu_profile_path.to_string_lossy().into_owned(),
        mem_file_path: mem_profile_path.to_string_lossy().into_owned(),
        guard: Some(guard),
        log_writer,
    }
}

impl ProfileSession {
    /// `func (p *ProfileSession) Stop()`
    pub fn stop(&mut self) {
        if let Some(guard) = self.guard.take() {
            match guard.report().build() {
                Ok(report) => match report.pprof() {
                    Ok(profile) => {
                        let mut content = Vec::new();
                        use prost::Message as _;
                        profile.encode(&mut content).unwrap();
                        let file = std::fs::File::create(&self.cpu_file_path).unwrap();
                        let mut gz =
                            flate2::write::GzEncoder::new(file, flate2::Compression::default());
                        gz.write_all(&content).unwrap();
                        gz.finish().unwrap();
                    }
                    Err(e) => panic!("failed to encode CPU profile: {e}"),
                },
                Err(e) => panic!("failed to build CPU profile report: {e}"),
            }
        }

        if !self.mem_file_path.is_empty() {
            write_memory_summary(&self.mem_file_path);
            writeln!(self.log_writer, "Memory profile: {}", self.mem_file_path).unwrap();
        }

        writeln!(self.log_writer, "CPU profile: {}", self.cpu_file_path).unwrap();
    }
}

/// `type CPUProfiler struct` — manages on-demand CPU profiling.
#[derive(Default)]
pub struct CpuProfiler {
    session: Mutex<Option<ProfileSession>>,
}

impl CpuProfiler {
    /// `func (c *CPUProfiler) StartCPUProfile(profileDir string) error`
    pub fn start_cpu_profile(&self, profile_dir: &str) -> Result<(), String> {
        let mut session = self.session.lock().unwrap();
        if session.is_some() {
            return Err("CPU profiling already in progress".to_string());
        }

        std::fs::create_dir_all(profile_dir)
            .map_err(|e| format!("failed to create profile directory: {e}"))?;

        let cpu_profile_path = Path::new(profile_dir).join(format!(
            "{}-{}-cpuprofile.pb.gz",
            std::process::id(),
            unix_millis()
        ));

        let guard = pprof::ProfilerGuardBuilder::default()
            .frequency(1000)
            .build()
            .map_err(|e| format!("failed to start CPU profile: {e}"))?;

        *session = Some(ProfileSession {
            cpu_file_path: cpu_profile_path.to_string_lossy().into_owned(),
            mem_file_path: String::new(),
            guard: Some(guard),
            log_writer: Box::new(std::io::sink()),
        });
        Ok(())
    }

    /// `func (c *CPUProfiler) StopCPUProfile() (string, error)`
    pub fn stop_cpu_profile(&self) -> Result<String, String> {
        let mut session = self.session.lock().unwrap();
        let Some(mut s) = session.take() else {
            return Err("CPU profiling not in progress".to_string());
        };
        s.stop();
        Ok(s.cpu_file_path)
    }
}

/// `func SaveHeapProfile(profileDir string) (string, error)`
///
/// PORT: writes a gzip'd memory summary (Go heap profiles don't exist in
/// Rust); same filename contract.
pub fn save_heap_profile(profile_dir: &str) -> Result<String, String> {
    save_memory_profile(profile_dir, "heapprofile")
}

/// `func SaveAllocProfile(profileDir string) (string, error)`
pub fn save_alloc_profile(profile_dir: &str) -> Result<String, String> {
    save_memory_profile(profile_dir, "allocprofile")
}

fn save_memory_profile(profile_dir: &str, kind: &str) -> Result<String, String> {
    std::fs::create_dir_all(profile_dir)
        .map_err(|e| format!("failed to create profile directory: {e}"))?;

    let path = Path::new(profile_dir).join(format!(
        "{}-{}-{kind}.pb.gz",
        std::process::id(),
        unix_millis()
    ));
    write_memory_summary(&path.to_string_lossy());
    Ok(path.to_string_lossy().into_owned())
}

fn write_memory_summary(path: &str) {
    let file = match std::fs::File::create(path) {
        Ok(f) => f,
        Err(e) => panic!("failed to create memory profile file: {e}"),
    };
    let mut gz = flate2::write::GzEncoder::new(file, flate2::Compression::default());
    let mut summary =
        String::from("# Rust port — no Go-style heap profile; process memory summary follows.\n");
    if let Ok(status) = std::fs::read_to_string("/proc/self/status") {
        for line in status.lines() {
            if line.starts_with("Vm") {
                let _ = writeln!(summary, "{line}");
            }
        }
    }
    gz.write_all(summary.as_bytes()).unwrap();
    gz.finish().unwrap();
}

fn unix_millis() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis()
}

/// `func RunGC()` — PORT: no-op; Rust has no garbage collector.
pub fn run_gc() {}
