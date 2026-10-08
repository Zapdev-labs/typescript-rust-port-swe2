// M3 corpus gate: parse every file under the given roots, catch panics,
// and emit one JSON line per file:
//   {"file":..., "panic": "<msg>"}                        on panic
//   {"file":..., "diags":[{"code","pos","end","cat","msg"}]}
// Usage: parsecorpus <root> [root...] > out.jsonl
// Go oracle produces the same shape via tsc's parser (see scripts/).

use std::panic::{catch_unwind, AssertUnwindSafe};

use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::core::get_script_kind_from_file_name;
use tsc_parser::parse_source_file;
use tsc_tspath::{PathKey, RootedFilePath};

fn parse_one(path: &str) -> String {
    let file_name = RootedFilePath::from(path.to_string());
    let text = match std::fs::read(path) {
        // Go feeds raw bytes to the scanner; invalid UTF-8 surfaces as RuneError.
        // from_utf8_lossy is the closest equivalent over a valid &str.
        Ok(b) => String::from_utf8_lossy(&b).into_owned(),
        Err(e) => {
            return format!(
                "{{\"file\":{},\"read_error\":\"{}\"}}",
                serde_json::to_string(path).unwrap(),
                e
            )
        }
    };
    let script_kind = get_script_kind_from_file_name(&file_name);
    let opts = SourceFileParseOptions {
        file_name: file_name.clone(),
        path_key: PathKey::from(path.to_string()),
        ..Default::default()
    };

    let result = catch_unwind(AssertUnwindSafe(|| {
        let (file, nodes): (NodeId, Vec<Node>) =
            parse_source_file(opts, &text, script_kind);
        let d = nodes[file].as_source_file();
        let mut diags = Vec::new();
        for dr in d.diagnostics.iter().chain(d.js_diagnostics.iter()) {
            let g = tsc_ast::diagnostic::lock_diagnostic(dr);
            diags.push(format!(
                "{{\"code\":{},\"pos\":{},\"end\":{},\"cat\":{},\"key\":{},\"args\":{}}}",
                g.code(),
                g.loc().pos(),
                g.loc().end(),
                g.category() as i32,
                serde_json::to_string(g.message_key()).unwrap(),
                serde_json::to_string(g.message_args()).unwrap()
            ));
        }
        format!("{{\"file\":{},\"diags\":[{}]}}",
            serde_json::to_string(path).unwrap(),
            diags.join(","))
    }));

    match result {
        Ok(s) => s,
        Err(e) => {
            let msg = e
                .downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| e.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "unknown panic".into());
            format!(
                "{{\"file\":{},\"panic\":{}}}",
                serde_json::to_string(path).unwrap(),
                serde_json::to_string(&msg).unwrap()
            )
        }
    }
}

fn want(p: &std::path::Path) -> bool {
    matches!(
        p.extension().and_then(|e| e.to_str()),
        Some("ts" | "tsx" | "mts" | "cts" | "js" | "jsx" | "mjs" | "cjs" | "json")
    )
}

fn walk(dir: &std::path::Path, out: &mut Vec<String>) {
    if dir.is_file() {
        if want(dir) {
            out.push(dir.to_string_lossy().to_string());
        }
        return;
    }
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let p = entry.path();
        if p.is_dir() {
            walk(&p, out);
        } else if want(&p) {
            out.push(p.to_string_lossy().to_string());
        }
    }
}

fn main() {
    let mut files = Vec::new();
    for arg in std::env::args().skip(1) {
        walk(std::path::Path::new(&arg), &mut files);
    }
    files.sort();
    let stdout = std::io::stdout();
    use std::io::Write;
    let mut w = std::io::BufWriter::new(stdout.lock());
    for f in &files {
        writeln!(w, "{}", parse_one(f)).unwrap();
    }
}

