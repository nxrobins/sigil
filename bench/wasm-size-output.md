# Wasm output size — SIGIL vs Rust → Wasm

- rustc: `rustc 1.95.0 (59807616e 2026-04-14)`
- cargo: `cargo 1.95.0 (f2d3ce0bd 2026-03-21)`
- wasm-opt: NOT FOUND on PATH (optimized columns omitted)

## Size table (bytes)

| Pair | SIGIL raw | Rust raw | SIGIL/Rust raw |
|---|---:|---:|---:|
| 01_fib | 347 | 163 | 2.13× |
| 02_echo_actor | 342 | 106 | 3.23× |
| 03_json_sum | 475 | 263 | 1.81× |
| 04_bounded_loop | 322 | 150 | 2.15× |
| 05_file_read_cap | 409 | 144 | 2.84× |

Notes: SIGIL `raw` is `wasm_inner.len() + wasm_outer.len()`. Rust `raw` is the cdylib `.wasm` produced by `cargo build --release --target wasm32-unknown-unknown`. Every Rust pair pins identical `[profile.release]` (opt-level="s", panic="abort", lto=false, strip=true, codegen-units=1) — see each `Cargo.toml`.
