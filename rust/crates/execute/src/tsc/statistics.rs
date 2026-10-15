// Ported from tsc/internal/execute/tsc/statistics.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

use crate::tsc::compile::{CommandLineTesting, CompileTimes};
use crate::tsc::emit::EmitInput;

struct TableRow {
    name: String,
    value: String,
}

/// `type table struct`.
#[derive(Default)]
struct Table {
    rows: Vec<TableRow>,
}

impl Table {
    /// `(t *table) add` — `Duration` values format via `formatDuration`.
    fn add_duration(&mut self, name: &str, value: Duration) {
        self.rows.push(TableRow {
            name: name.to_string(),
            value: format_duration(value),
        });
    }

    fn add(&mut self, name: &str, value: impl std::fmt::Display) {
        self.rows.push(TableRow {
            name: name.to_string(),
            value: value.to_string(),
        });
    }

    /// `(t *table) print`.
    fn print(&self, w: &mut dyn io::Write) {
        let mut name_width = 0usize;
        let mut value_width = 0usize;
        for r in &self.rows {
            name_width = name_width.max(r.name.len());
            value_width = value_width.max(r.value.len());
        }
        for r in &self.rows {
            let _ = writeln!(
                w,
                "{:<width$} {:>vwidth$}",
                format!("{}:", r.name),
                r.value,
                width = name_width + 1,
                vwidth = value_width
            );
        }
    }
}

/// `formatDuration` — `%.3fs`.
fn format_duration(d: Duration) -> String {
    format!("{:.3}s", d.as_secs_f64())
}

/// `type Statistics struct`.
#[derive(Clone, Debug, Default)]
pub struct Statistics {
    is_aggregate: bool,
    /// `Projects int`.
    pub projects: i32,
    /// `ProjectsBuilt int`.
    pub projects_built: i32,
    /// `TimestampUpdates int`.
    pub timestamp_updates: i32,
    files: usize,
    lines: usize,
    identifiers: i64,
    symbols: u64,
    types: u64,
    instantiations: u64,
    memory_used: u64,
    memory_allocs: u64,
    /// `compileTimes *CompileTimes`.
    compile_times: Rc<std::cell::RefCell<CompileTimes>>,
}

impl Statistics {
    /// `statisticsFromProgram` — counts read off the program.
    ///
    /// PORT(divergence): Go fills `memoryUsed`/`memoryAllocs` from
    /// `runtime.ReadMemStats` after two `runtime.GC()`s; Rust has no GC
    /// stats, so both are reported as 0.
    pub fn from_program(input: &EmitInput<'_>) -> Statistics {
        Statistics {
            is_aggregate: false,
            projects: 0,
            projects_built: 0,
            timestamp_updates: 0,
            files: input.program.source_files().len(),
            lines: input.program.line_count(),
            identifiers: input.program.identifier_count(),
            symbols: input.program.symbol_count(),
            types: input.program.type_count(),
            instantiations: input.program.instantiation_count(),
            memory_used: 0,
            memory_allocs: 0,
            compile_times: input.compile_times.clone(),
        }
    }

    /// `(s *Statistics) Report`.
    pub fn report(&self, w: &mut dyn io::Write, testing: Option<&Arc<dyn CommandLineTesting>>) {
        if let Some(t) = testing {
            t.on_statistics_start(w);
        }
        let mut table = Table::default();
        let prefix = if self.is_aggregate { "Aggregate " } else { "" };

        if self.is_aggregate {
            table.add("Projects in scope", self.projects);
            table.add("Projects built", self.projects_built);
            table.add("Timestamps only updates", self.timestamp_updates);
        }
        table.add(&format!("{prefix}Files"), self.files);
        table.add(&format!("{prefix}Lines"), self.lines);
        table.add(&format!("{prefix}Identifiers"), self.identifiers);
        table.add(&format!("{prefix}Symbols"), self.symbols);
        table.add(&format!("{prefix}Types"), self.types);
        table.add(&format!("{prefix}Instantiations"), self.instantiations);
        table.add(
            &format!("{prefix}Memory used"),
            format!("{}K", self.memory_used / 1024),
        );
        table.add(&format!("{prefix}Memory allocs"), self.memory_allocs);
        {
            let times = self.compile_times.borrow();
            if times.config_time != Duration::ZERO {
                table.add_duration(&format!("{prefix}Config time"), times.config_time);
            }
            if times.build_info_read_time != Duration::ZERO {
                table.add_duration(
                    &format!("{prefix}BuildInfo read time"),
                    times.build_info_read_time,
                );
            }
            table.add_duration(&format!("{prefix}Parse time"), times.parse_time);
            if times.bind_time != Duration::ZERO {
                table.add_duration(&format!("{prefix}Bind time"), times.bind_time);
            }
            if times.check_time != Duration::ZERO {
                table.add_duration(&format!("{prefix}Check time"), times.check_time);
            }
            if times.emit_time != Duration::ZERO {
                table.add_duration(&format!("{prefix}Emit time"), times.emit_time);
            }
            if times.changes_compute_time != Duration::ZERO {
                table.add_duration(
                    &format!("{prefix}Changes compute time"),
                    times.changes_compute_time,
                );
            }
            self.add_content_mapper_statistics(&mut table, prefix, &times);
            table.add_duration(&format!("{prefix}Total time"), times.total_time);
        }
        table.print(w);
        if let Some(t) = testing {
            t.on_statistics_end(w);
        }
    }

    /// `(s *Statistics) addContentMapperStatistics`.
    fn add_content_mapper_statistics(&self, table: &mut Table, prefix: &str, times: &CompileTimes) {
        let timings = &times.content_mapper_times;
        if timings.request_wait != Duration::ZERO {
            table.add_duration(
                &format!("{prefix}Content mapper request wait time"),
                timings.request_wait,
            );
        }
        let mut identities: Vec<&String> = timings.mappers.keys().collect();
        identities.sort();
        for identity in identities {
            let mapper = &timings.mappers[identity];
            if mapper.spawn.count != 0 {
                table.add_duration(
                    &format!("{prefix}{identity} initialization time"),
                    mapper.spawn.duration + mapper.initialize.duration,
                );
            }
            if mapper.transform.count != 0 {
                table.add_duration(
                    &format!("{prefix}{identity} transform time"),
                    mapper.transform.duration,
                );
            }
            if mapper.open_project.count != 0 {
                table.add_duration(
                    &format!("{prefix}{identity} openProject time"),
                    mapper.open_project.duration,
                );
            }
            if mapper.close_project.count != 0 {
                table.add_duration(
                    &format!("{prefix}{identity} closeProject time"),
                    mapper.close_project.duration,
                );
            }
        }
    }

    /// `(s *Statistics) Aggregate`.
    pub fn aggregate(&mut self, stat: &Statistics) {
        self.is_aggregate = true;
        // `s.compileTimes == nil` — always non-nil in Rust; keep the Add.
        self.files += stat.files;
        self.lines += stat.lines;
        self.identifiers += stat.identifiers;
        self.symbols += stat.symbols;
        self.types += stat.types;
        self.instantiations += stat.instantiations;
        self.memory_used += stat.memory_used;
        self.memory_allocs += stat.memory_allocs;
        let stat_times = stat.compile_times.borrow();
        let mut times = self.compile_times.borrow_mut();
        times.config_time += stat_times.config_time;
        times.build_info_read_time += stat_times.build_info_read_time;
        times.parse_time += stat_times.parse_time;
        times.bind_time += stat_times.bind_time;
        times.check_time += stat_times.check_time;
        times.emit_time += stat_times.emit_time;
        times.changes_compute_time += stat_times.changes_compute_time;
    }

    /// `(s *Statistics) SetTotalTime`.
    pub fn set_total_time(&self, total_time: Duration) {
        self.compile_times.borrow_mut().total_time = total_time;
    }
}
