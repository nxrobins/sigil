# bench/wasm-size — paired SIGIL + Rust → Wasm programs

Five paired programs measuring SIGIL's compiled Wasm size against
equivalent Rust → `wasm32-unknown-unknown` output. Each pair is
structurally pinned by
[`crates/sigil-compiler/tests/wasm_size_pairs.rs`](../../crates/sigil-compiler/tests/wasm_size_pairs.rs).

Measured numbers live in [`../../PERFORMANCE.md`](../../PERFORMANCE.md).
The [`COMPARISON.md`](../../COMPARISON.md) places SIGIL next to
Pony / Rust / Joe-E / Erlang / Caja at the feature level.

## Layout

```
bench/wasm-size/
├── README.md                # this file
├── rust-toolchain.toml      # pins rustc + wasm32-unknown-unknown target
├── 01_fib/                  # pure compute, no caps
├── 02_echo_actor/           # spawn + capability move
├── 03_json_sum/             # ! { Alloc } effect declared and used
├── 04_bounded_loop/         # fuel decrement (per-iter)
└── 05_file_read_cap/        # outer-ring + ! { FFI } extern
```

Per-pair:

```
0N_<slug>/
├── SPEC.md          # Input / Expected output / Error mode / Exit code
├── main.sigil       # SIGIL implementation
├── main.rs          # Rust implementation
└── Cargo.toml       # crate-type = ["cdylib"]; [profile.release] pinned
```

## Reproducibility

```powershell
# Install the target once
rustup target add wasm32-unknown-unknown

# Build + measure all 5 pairs; emits a markdown table to stdout
cargo run --release --quiet --example wasm_size -p sigil-compiler

# Driver: 10 structural checks (pair structure, SIGIL clean compile,
# feature invocation, Rust profile pinning, SPEC schema, contiguous
# numbering + slugs in PERFORMANCE.md, rust-toolchain pinned, cross-
# links to PERFORMANCE.md + COMPARISON.md, citation pre-flight ref)
cargo test --release -p sigil-compiler --test wasm_size_pairs
```

## What the driver enforces (and what it doesn't)

The driver enforces structural integrity, NOT behavioural equivalence.
Four of five SIGIL fixtures require host-import stubs (spawn / send
/ alloc / FFI / fuel) that would require a mini-runtime in the
driver. Equivalence is verified by manual inspection of each
`SPEC.md`; honest disclosure of this gap is recorded in
PERFORMANCE.md.

## Mandated Rust release profile

Every pair's `Cargo.toml` must contain this block verbatim. The
driver's `rust_release_profile_pinned` test fails the build if any
pair drifts.

```toml
[profile.release]
opt-level = "s"
panic = "abort"
lto = false
strip = true
codegen-units = 1
```

This block exists to defeat the "Rust side is bloated by default
panic unwinding" attack. SIGIL emits abort-on-trap by default; the
pinned profile matches Rust's surface area to SIGIL's.

## Adding a new pair

1. Bump the contiguous-numbering check by deciding on a slug; create
   `bench/wasm-size/06_<slug>/`.
2. Add `SPEC.md` with the four named fields (`Input:`, `Expected
   output:`, `Error mode:`, `Exit code:`) populated with literal
   values, not descriptions.
3. Write `main.sigil` invoking the feature your slug advertises.
4. Write `main.rs` matching the SPEC (start from any existing pair's
   `main.rs`).
5. Add the per-slug feature-invocation regex to
   `feature_invocation()` in [`wasm_size_pairs.rs`](../../crates/sigil-compiler/tests/wasm_size_pairs.rs)
   so the driver checks your fixture actually invokes the named
   feature (closes MC-1 for the new pair).
6. Add a row in PERFORMANCE.md's size table containing the slug
   string verbatim.
7. Update `EXPECTED_PAIRS` constant in the driver.

Every step is a driver-enforced check — skipping any step fails CI.
