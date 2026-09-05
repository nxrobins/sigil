//! Scratch: compile a single .sigil file passed as argv[1] and print
//! diagnostics. Used by the Phase 3 gap-filling loop to verify each
//! new tool compiles cleanly before commit.

use std::env;
use std::fs;
use std::process::ExitCode;

use sigil_compiler::compile_named_module;

fn main() -> ExitCode {
    let path = match env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: check_tool <path/to/file.sigil>");
            return ExitCode::from(2);
        }
    };
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("read error: {e}");
            return ExitCode::from(2);
        }
    };
    let name = std::path::Path::new(&path)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("?")
        .to_string();
    match compile_named_module(name, source) {
        Ok(c) => {
            let inner = c.wasm_inner.len();
            let outer = c.wasm_outer.as_ref().map_or(0, |v| v.len());
            println!("OK: {} bytes (inner={inner}, outer={outer})", inner + outer);
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("FAILED: {} diagnostics", e.diagnostics().len());
            for d in e.diagnostics() {
                eprintln!("  {:?}: {}", d.code(), d.message());
            }
            ExitCode::from(1)
        }
    }
}
