use tsc_core::context::Context;
use tsc_transpile::{Options, transpile_module};

fn main() {
    let src = "const x = ;\nconst y: = 2\n";
    let out = transpile_module(
        &Context::background(),
        src,
        Options { report_diagnostics: true, ..Default::default() },
    )
    .expect("transpile");
    println!("=== DIAGS: {} ===", out.diagnostics.len());
    for d in &out.diagnostics {
        let guard = tsc_ast::diagnostic::lock_diagnostic(d);
        println!("code={} chains={}", guard.code(), guard.message_chain().len());
    }
}
