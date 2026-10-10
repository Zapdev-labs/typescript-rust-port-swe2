use tsc_core::context::Context;
use tsc_transpile::{Options, transpile_module};

fn main() {
    let out = transpile_module(
        &Context::background(),
        "enum E { A, B }\nconst x: E = E.A;\nconsole.log(x);\n",
        Options::default(),
    )
    .expect("transpile");
    println!("=== OUTPUT ===\n{}", out.output_text);
    println!("=== DIAGS: {} ===", out.diagnostics.len());
}
