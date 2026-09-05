//! Wasm output-size bench (one-shot, doc-published).
//!
//! For each `bench/wasm-size/0N_<slug>/` pair:
//!   1. Compile `main.sigil` via the SIGIL compiler API; record
//!      `wasm_inner.len() + wasm_outer.len()`.
//!   2. Compile `main.rs` via `cargo build --release --target
//!      wasm32-unknown-unknown` (subprocess); record the resulting
//!      `.wasm`'s `fs::metadata().len()`.
//!   3. If `wasm-opt` is on PATH, apply `-Oz` to both and record
//!      optimized sizes. SIGIL's inner and outer modules are optimized
//!      separately (a Wasm binary is a single module) and summed.
//!   4. Emit a markdown row.
//!
//! Per the v2 plan: cross-platform (no PowerShell), preflight checks
//! for `cargo` and `wasm32-unknown-unknown`, `cargo clean` between
//! runs for cache symmetry. Section breakdown via wasmparser is out
//! of scope for this example (the plan's MI-8/UP-9 are addressed by
//! a one-off `wasm-objdump` analysis in PERFORMANCE.md authoring
//! rather than driver-enforcement) — keeping the example dependency-
//! footprint small.
//!
//! Authors paste output into PERFORMANCE.md.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use sigil_compiler::compile_named_module;

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn repo_root() -> PathBuf {
    // crates/sigil-compiler/ → up to repo root
    manifest_dir()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn pairs_dir() -> PathBuf {
    repo_root().join("bench").join("wasm-size")
}

fn check_cargo_available() -> Result<(), String> {
    Command::new("cargo")
        .arg("--version")
        .output()
        .map_err(|e| format!("`cargo` not on PATH: {e}\nInstall Rust from https://rustup.rs"))?;
    Ok(())
}

fn check_wasm32_target() -> Result<(), String> {
    let out = Command::new("rustup")
        .args(["target", "list", "--installed"])
        .output()
        .map_err(|e| format!("`rustup` not on PATH: {e}"))?;
    let text = String::from_utf8_lossy(&out.stdout);
    if !text.lines().any(|l| l.trim() == "wasm32-unknown-unknown") {
        return Err("wasm32-unknown-unknown target not installed.\n\
             Install with: rustup target add wasm32-unknown-unknown"
            .into());
    }
    Ok(())
}

fn wasm_opt_available() -> bool {
    Command::new("wasm-opt")
        .arg("--version")
        .output()
        .ok()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn collect_pairs() -> Vec<PathBuf> {
    let dir = pairs_dir();
    let mut out = Vec::new();
    if !dir.is_dir() {
        return out;
    }
    for entry in fs::read_dir(&dir).expect("bench/wasm-size missing") {
        let path = entry.unwrap().path();
        if !path.is_dir() {
            continue;
        }
        let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if !(name.len() >= 3
            && name.as_bytes()[0].is_ascii_digit()
            && name.as_bytes()[1].is_ascii_digit()
            && name.as_bytes()[2] == b'_')
        {
            continue;
        }
        if !path.join("main.sigil").is_file() {
            continue;
        }
        out.push(path);
    }
    out.sort();
    out
}

fn compile_sigil(pair: &Path) -> (usize, usize) {
    let src_path = pair.join("main.sigil");
    let source = fs::read_to_string(&src_path).expect("read main.sigil");
    let name = src_path.file_name().and_then(|s| s.to_str()).unwrap_or("?");
    let comp =
        compile_named_module(name.to_string(), source).expect("SIGIL fixture compiles cleanly");
    let inner = comp.wasm_inner.len();
    let outer = comp.wasm_outer.as_ref().map_or(0, |v| v.len());
    (inner, outer)
}

fn compile_rust(pair: &Path) -> PathBuf {
    let manifest = pair.join("Cargo.toml");

    // cargo clean for cache symmetry between runs (MI-4 fence).
    let _ = Command::new("cargo")
        .args(["clean", "--manifest-path"])
        .arg(&manifest)
        .output();

    let status = Command::new("cargo")
        .args([
            "build",
            "--release",
            "--target",
            "wasm32-unknown-unknown",
            "--manifest-path",
        ])
        .arg(&manifest)
        .status()
        .expect("cargo build");
    if !status.success() {
        panic!("cargo build failed for {}", pair.display());
    }

    // Locate the .wasm in target/wasm32-unknown-unknown/release/
    let target_dir = pair
        .join("target")
        .join("wasm32-unknown-unknown")
        .join("release");
    for entry in fs::read_dir(&target_dir).expect("target dir") {
        let p = entry.unwrap().path();
        if p.extension().and_then(|s| s.to_str()) == Some("wasm") {
            return p;
        }
    }
    panic!("no .wasm in {}", target_dir.display());
}

fn wasm_opt(wasm: &Path) -> Option<u64> {
    let out_path = wasm.with_file_name(format!(
        "{}.opt.wasm",
        wasm.file_stem().and_then(|s| s.to_str()).unwrap_or("opt")
    ));
    let status = Command::new("wasm-opt")
        .arg("-Oz")
        .arg("--all-features") // SIGIL modules use memory64 (i64 pointer ABI)
        .arg(wasm)
        .arg("-o")
        .arg(&out_path)
        .status()
        .ok()?;
    if !status.success() {
        return None;
    }
    let size = fs::metadata(&out_path).ok().map(|m| m.len());
    let _ = fs::remove_file(&out_path); // one-shot measurement; keep the tree clean
    size
}

fn write_sigil_modules(pair: &Path) -> Vec<PathBuf> {
    // Materialize compiled SIGIL Wasm bytes to disk so wasm-opt can
    // operate on real files — ONE FILE PER MODULE. A Wasm binary is a
    // single module, so the inner and outer modules must be optimized
    // separately and their optimized sizes summed; concatenating them
    // produces an invalid binary that wasm-opt rejects.
    let src_path = pair.join("main.sigil");
    let source = fs::read_to_string(&src_path).expect("read main.sigil");
    let name = src_path.file_name().and_then(|s| s.to_str()).unwrap_or("?");
    let comp = compile_named_module(name.to_string(), source).expect("SIGIL clean");
    let inner_path = pair.join(".sigil_inner.wasm");
    fs::write(&inner_path, &comp.wasm_inner).expect("write inner wasm");
    let mut out = vec![inner_path];
    if let Some(outer_bytes) = &comp.wasm_outer {
        let outer_path = pair.join(".sigil_outer.wasm");
        fs::write(&outer_path, outer_bytes).expect("write outer wasm");
        out.push(outer_path);
    }
    out
}

fn print_environment() {
    println!("# Wasm output size — SIGIL vs Rust → Wasm");
    println!();
    let rustc = Command::new("rustc").arg("--version").output();
    if let Ok(o) = rustc {
        let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
        println!("- rustc: `{s}`");
    }
    let cargo = Command::new("cargo").arg("--version").output();
    if let Ok(o) = cargo {
        let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
        println!("- cargo: `{s}`");
    }
    let wo = Command::new("wasm-opt").arg("--version").output();
    if let Ok(o) = wo {
        let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
        println!("- wasm-opt: `{s}`");
    } else {
        println!("- wasm-opt: NOT FOUND on PATH (optimized columns omitted)");
    }
    println!();
}

fn main() {
    if let Err(e) = check_cargo_available() {
        eprintln!("{e}");
        std::process::exit(1);
    }
    if let Err(e) = check_wasm32_target() {
        eprintln!("{e}");
        std::process::exit(1);
    }
    let have_wasm_opt = wasm_opt_available();
    print_environment();

    println!("## Size table (bytes)");
    println!();
    if have_wasm_opt {
        println!("| Pair | SIGIL raw | SIGIL -Oz | Rust raw | Rust -Oz | SIGIL/Rust raw |");
        println!("|---|---:|---:|---:|---:|---:|");
    } else {
        println!("| Pair | SIGIL raw | Rust raw | SIGIL/Rust raw |");
        println!("|---|---:|---:|---:|");
    }

    for pair in collect_pairs() {
        let pair_name = pair
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("?")
            .to_string();

        let (inner, outer) = compile_sigil(&pair);
        let sigil_raw = inner + outer;

        let rust_wasm = compile_rust(&pair);
        let rust_raw = fs::metadata(&rust_wasm).expect("rust wasm metadata").len() as usize;

        if have_wasm_opt {
            let module_paths = write_sigil_modules(&pair);
            let sigil_opt: usize = module_paths
                .iter()
                .map(|p| {
                    let n =
                        wasm_opt(p).unwrap_or_else(|| panic!("wasm-opt failed on {}", p.display()));
                    n as usize
                })
                .sum();
            for p in &module_paths {
                let _ = fs::remove_file(p);
            }
            let rust_opt = wasm_opt(&rust_wasm)
                .unwrap_or_else(|| panic!("wasm-opt failed on {}", rust_wasm.display()))
                as usize;
            let ratio = if rust_raw == 0 {
                0.0
            } else {
                sigil_raw as f64 / rust_raw as f64
            };
            println!(
                "| {} | {} | {} | {} | {} | {:.2}× |",
                pair_name, sigil_raw, sigil_opt, rust_raw, rust_opt, ratio
            );
        } else {
            let ratio = if rust_raw == 0 {
                0.0
            } else {
                sigil_raw as f64 / rust_raw as f64
            };
            println!(
                "| {} | {} | {} | {:.2}× |",
                pair_name, sigil_raw, rust_raw, ratio
            );
        }
    }
    println!();
    println!(
        "Notes: SIGIL `raw` is `wasm_inner.len() + wasm_outer.len()`. \
         Rust `raw` is the cdylib `.wasm` produced by `cargo build --release \
         --target wasm32-unknown-unknown`. Every Rust pair pins identical \
         `[profile.release]` (opt-level=\"s\", panic=\"abort\", lto=true, \
         strip=true, codegen-units=1) — see each `Cargo.toml`."
    );
}
