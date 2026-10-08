// gen-ast — AST code generator for the Rust tsc port.
//
//   gen-ast bootstrap [go-ast-dir] [kinds.toml]   — one-shot Go → TOML
//   gen-ast generate  [kinds.toml] [out-dir]      — emit generated sources
//   gen-ast check     [kinds.toml] [out-dir]      — verify outputs are fresh
//
// Defaults assume the repo layout <root>/tsc/internal/ast and
// <root>/rust/{tools/gen-ast/kinds.toml, crates/ast/src}.

mod emit_ast;
mod emit_kinds;
mod goparse;
mod model;
mod schema_io;
mod toml;

use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn repo_root() -> PathBuf {
    // gen-ast → tools → rust → root
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(3)
        .unwrap()
        .to_path_buf()
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(cmd) = args.first() else {
        eprintln!("usage: gen-ast <bootstrap|generate|check> [paths...]");
        return ExitCode::FAILURE;
    };
    let root = repo_root();
    let default_kinds = root.join("rust/tools/gen-ast/kinds.toml");
    let default_go = root.join("tsc/internal/ast");
    let default_out = root.join("rust/crates/ast/src");

    let result = match cmd.as_str() {
        "bootstrap" => {
            let go = args.get(1).map(PathBuf::from).unwrap_or(default_go);
            let kinds = args.get(2).map(PathBuf::from).unwrap_or(default_kinds);
            bootstrap(&go, &kinds)
        }
        "generate" => {
            let kinds = args.get(1).map(PathBuf::from).unwrap_or(default_kinds);
            let out = args.get(2).map(PathBuf::from).unwrap_or(default_out);
            generate(&kinds, &out)
        }
        "check" => {
            let kinds = args.get(1).map(PathBuf::from).unwrap_or(default_kinds);
            let out = args.get(2).map(PathBuf::from).unwrap_or(default_out);
            check(&kinds, &out)
        }
        other => Err(format!("unknown command `{other}`")),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("gen-ast: {e}");
            ExitCode::FAILURE
        }
    }
}

fn bootstrap(go_dir: &Path, kinds_path: &Path) -> Result<(), String> {
    let schema = goparse::bootstrap(go_dir)?;
    let text = schema_io::write_schema(&schema);
    std::fs::write(kinds_path, text).map_err(|e| format!("write {}: {e}", kinds_path.display()))?;
    eprintln!(
        "gen-ast: wrote {} ({} kinds, {} bases, {} nodes)",
        kinds_path.display(),
        schema.kinds.len(),
        schema.bases.len(),
        schema.nodes.len()
    );
    Ok(())
}

/// Run `rustfmt` over emitted Rust so generated files satisfy
/// `cargo fmt --check` verbatim. Falls back to the raw text if `rustfmt` is
/// unavailable.
fn format_rust(content: String) -> String {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let Ok(mut child) = Command::new("rustfmt")
        .arg("--edition")
        .arg("2024")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    else {
        return content;
    };
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(content.as_bytes());
    }
    match child.wait_with_output() {
        Ok(out) if out.status.success() => String::from_utf8(out.stdout).unwrap_or(content),
        _ => content,
    }
}

fn generate(kinds_path: &Path, out_dir: &Path) -> Result<(), String> {
    let schema = schema_io::load_schema(kinds_path)?;
    write_if_changed(
        &out_dir.join("kind_generated.rs"),
        &format_rust(emit_kinds::emit(&schema)),
    )?;
    write_if_changed(
        &out_dir.join("ast_generated.rs"),
        &format_rust(emit_ast::Emitter::new(&schema).emit()),
    )?;
    Ok(())
}

fn check(kinds_path: &Path, out_dir: &Path) -> Result<(), String> {
    let schema = schema_io::load_schema(kinds_path)?;
    for (file, want) in [
        ("kind_generated.rs", emit_kinds::emit(&schema)),
        ("ast_generated.rs", emit_ast::Emitter::new(&schema).emit()),
    ] {
        let want = format_rust(want);
        let path = out_dir.join(file);
        let have =
            std::fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        if have != want {
            return Err(format!(
                "{} is stale — run `gen-ast generate`",
                path.display()
            ));
        }
    }
    eprintln!("gen-ast: generated files are up to date");
    Ok(())
}

fn write_if_changed(path: &Path, content: &str) -> Result<(), String> {
    if let Ok(existing) = std::fs::read_to_string(path) {
        if existing == content {
            return Ok(());
        }
    }
    std::fs::write(path, content).map_err(|e| format!("write {}: {e}", path.display()))?;
    eprintln!("gen-ast: wrote {}", path.display());
    Ok(())
}
