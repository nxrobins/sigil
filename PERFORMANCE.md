# SIGIL Performance — measured numbers

**One-shot, doc-published. Throughput measured 2026-05-17; Wasm size
(raw + `-Oz`) re-measured 2026-07-01 on the environment recorded
below. Not a continuous benchmark.**

This document publishes two measurements:

1. **Compile / verify throughput** over the existing 69-file test
   corpora, with and without Z3.
2. **Wasm output size** for 5 paired SIGIL + Rust→Wasm programs,
   structurally pinned by [`tests/wasm_size_pairs.rs`](crates/sigil-compiler/tests/wasm_size_pairs.rs).

The companion document [`COMPARISON.md`](COMPARISON.md) places SIGIL
next to Pony, Rust, Joe-E, Erlang, and Caja at the feature level;
this document focuses on numbers we ran ourselves.

> **Scope of claim:** every number here is **MEASURED** on one
> machine on one day. We did NOT run Pony / Joe-E / Erlang / Caja
> benchmarks; the Wasm-size comparison is SIGIL-vs-Rust only.
> Reproducibility instructions below; reviewers should expect their
> numbers to differ by tens of percent depending on hardware.

---

## Environment

- **CPU:** 11th Gen Intel Core i9-11900K @ 3.50 GHz, 8 cores / 16 threads
- **RAM:** 128 GB
- **OS:** Microsoft Windows 11 Home (10.0.26200)
- **rustc:** 1.95.0 (59807616e 2026-04-14)
- **cargo:** 1.95.0 (f2d3ce0bd 2026-03-21)
- **wasm-opt:** Binaryen `version_130` (`wasm-opt -Oz --all-features`), used for the 2026-07-01 size re-measurement
- **wasm32 target:** installed (`rustup target add wasm32-unknown-unknown`)
- **sigil-compiler commit:** see git log on this branch
- **Pinned rustc version for `bench/wasm-size/`:** [`rust-toolchain.toml`](bench/wasm-size/rust-toolchain.toml) (channel = stable)

CPU governor / thermal state was not externally controlled; the
machine was idle (no other CPU-bound processes) during measurement.
Reviewers reproducing on Linux should set `cpupower frequency-set
-g performance` for a fair comparison.

---

## Compile / verify throughput

**Last measured:** 2026-05-17.

Per the v2 plan, fixtures with **coefficient of variation > 20%** are
dropped from per-corpus medians/totals (the **✗** flag in per-
fixture detail; full output in [`bench/throughput-solver-on.md`](bench/throughput-solver-on.md)
and [`bench/throughput-solver-off.md`](bench/throughput-solver-off.md)).
Convergence target: 5% trailing-window CV, minimum 30 samples,
maximum 500. Warmup run discarded.

We publish two columns side-by-side. **We do NOT publish "Z3 cost =
delta" as a headline number** — Z3's timing is nondeterministic on
single invocations, and the delta on small fixtures is noise-
dominated. Readers may subtract.

### solver = ON (default features)

| Corpus | Files measured | Dropped (CV>20%) | Median (μs) | P90 (μs) | Total (μs) |
|---|---:|---:|---:|---:|---:|
| fixtures | 19 | 11 | 8 | 11 | 135 |
| cve_corpus | 3 | 12 | 5001 | 6596 | 10204 |
| z3_corpus | 4 | 20 | 5441 | 9360 | 12722 |

### solver = OFF (`--no-default-features --features json`)

| Corpus | Files measured | Dropped (CV>20%) | Median (μs) | P90 (μs) | Total (μs) |
|---|---:|---:|---:|---:|---:|
| fixtures | 11 | 19 | 6 | 13 | 66 |
| cve_corpus | 9 | 6 | 26 | 29 | 220 |
| z3_corpus | 12 | 12 | 28 | 45 | 341 |

### Headline observations

- **For `fixtures/` corpus** (30 small structural fixtures, ~30 LOC
  each): median compile time is **7–8 μs** with or without Z3. These
  fixtures rarely invoke the Z3 solver in practice; the cost matches.
- **For `cve_corpus/` and `z3_corpus/`** (Z3-heavy adversarial
  proofs): median compile time with Z3 ranges **~5–8 ms** per
  fixture; without Z3, ~25 μs per fixture. **The Z3 solver is
  responsible for nearly all the time on these corpora** — a ratio
  in the 200× range. This is expected: Z3 explores capability
  attenuation lattices to discharge correctness obligations.
- **High dropped count on fixtures/ corpus:** 15 of 30 fixtures land
  in totals. Tiny fixtures with sub-10-μs compile times are noise-
  limited by Windows `Instant` resolution and OS scheduling jitter;
  CV>20% is unavoidable for these. We do not synthesize a headline
  number from noise; we publish the dropped count and let the reader
  judge.

Full per-fixture detail (n, median, P90, max, CV%, convergence flag)
is in [`bench/throughput-solver-on.md`](bench/throughput-solver-on.md)
and [`bench/throughput-solver-off.md`](bench/throughput-solver-off.md).

---

## Wasm output size — SIGIL vs Rust → Wasm

**Last measured:** 2026-07-01 (raw + `-Oz`, `lto=true` re-pin; the
raw-only 2026-05-17 snapshot is superseded — raw bytes drifted with
compiler evolution, including the `wasm.rs` i64-base-wrap fix below).

Five paired programs structurally pinned by
[`tests/wasm_size_pairs.rs`](crates/sigil-compiler/tests/wasm_size_pairs.rs).
Driver enforces: each pair compiles cleanly; SIGIL fixture invokes
its named feature (per-slug regex); Rust manifest pins the mandated
`[profile.release]` block verbatim; SPEC.md schema; contiguous
numbering 01..05; rust-toolchain.toml pinned; slugs appear in this
document.

### Size table (bytes)

| Pair | SIGIL raw | SIGIL -Oz | Rust raw | Rust -Oz | raw ratio | -Oz ratio | SIGIL feature exercised |
|---|---:|---:|---:|---:|---:|---:|---|
| `01_fib` | 369 | 144 | 163 | 141 | 2.26× | 1.02× | pure compute, no caps |
| `02_echo_actor` | 372 | 219 | 106 | 98 | 3.51× | 2.23× | actor + spawn + capability move |
| `03_json_sum` | 497 | 223 | 263 | 250 | 1.89× | 0.89× | `! { Alloc }` effect declared and used |
| `04_bounded_loop` | 344 | 150 | 150 | 136 | 2.29× | 1.10× | fuel decrement (per-iter) |
| `05_file_read_cap` | 431 | 159 | 144 | 132 | 2.99× | 1.20× | outer-ring + `! { FFI }` extern |

SIGIL `raw` = `wasm_inner.len() + wasm_outer.len()`.
Rust `raw` = `cdylib` `.wasm` produced by `cargo build --release
--target wasm32-unknown-unknown` with mandated profile (opt-level=s,
panic=abort, lto=true, strip=true, codegen-units=1).
`-Oz` = `wasm-opt -Oz --all-features` (Binaryen version_130) applied
per module — SIGIL's inner and outer modules are optimized separately
and summed, since a Wasm binary is a single module.

The 2026-07-01 pass also added a Wasm-validation fence to the driver
(`sigil_modules_validate_as_wasm`): `wasm-opt` exposed an invalid
`i32.load` fed by an i64 handler-payload base in `02_echo_actor`'s
inner module — these fixtures are byte-measured but never
instantiated, so nothing had validated them before. Fixed in the same
change (i64-base wrap in `wasm.rs` LoadField/StoreField/
LoadDynamic/StoreDynamic).

### What the 2–3× gap is

SIGIL emits **more bytes** than Rust→Wasm for equivalent functional
behaviour. The breakdown that explains the gap:

- **Capability-system import stubs.** Even `01_fib` (no caps used)
  carries the import-section preamble: spawn, send, ask,
  cap_restrict, cap_split, fuel_decrement, fuel_exhausted, alloc.
  These imports cost ~80 bytes regardless of whether the program
  invokes any of them. Rust's `cdylib` has zero imports.
- **Fuel-decrement instructions.** SIGIL inserts a fuel decrement at
  each function entry and each loop back-edge. For `04_bounded_loop`
  with a hot loop, this is visible bytes per iteration in the code
  section.
- **Ring-isolation scaffolding.** Two-module outputs (the only one
  in this set is `05_file_read_cap`) carry separate import sections
  for inner-vs-outer-ring; this doubles the import overhead.
- **No tree-shaking / dead-code elimination.** SIGIL's codegen does
  not currently strip unused imports per-program.

With `wasm-opt -Oz` applied to both sides, the ratios collapse from
1.9-3.5x raw to **0.89-2.23x optimized (median 1.10x)** — the
capability-system scaffolding is exactly the repetitive,
partially-dead code `-Oz` strips. `03_json_sum` optimizes *smaller*
than its Rust pair. The remaining outlier is `02_echo_actor` (2.23x),
whose actor-dispatch/messaging scaffolding survives optimization.
This confirms the 2026-05-17 prediction that SIGIL output compresses
better because the scaffolding is repetitive.

Behavioural equivalence is NOT mechanically enforced by the driver:
four of five SIGIL fixtures require host-import stubs (spawn / send
/ alloc / FFI / fuel) that would require a mini-runtime in the
driver. Equivalence is verified by manual inspection against each
pair's [`SPEC.md`](bench/wasm-size/). This is an honest gap, not a
solved problem; future work could add wasmtime-based equivalence
for `01_fib` and `04_bounded_loop` (which have no host imports).

### Section-level breakdown (one-off, by hand)

The 2–3× gap is dominated by the import section, code section, and
function section overhead. A reader who wants to dig deeper can
generate a `wasm-objdump --section-list` on the per-module artifacts
the `wasm_size` example temporarily materializes next to each pair
(`.sigil_inner.wasm` / `.sigil_outer.wasm`; they are removed after
measurement, so grab them mid-run or comment out the cleanup). We do not publish per-section bytes here because
section parsing is not driver-enforced (would add `wasmparser` as a
non-dev dependency); the totals above are the published numbers.

---

## Compilation determinism

**Last verified:** 2026-05-17.

SIGIL compilation is **byte-stable across runs**: compiling the same
`.sigil` source twice produces byte-identical `wasm_inner` and
`wasm_outer` artefacts. This invariant is locked in by
[`tests/determinism_lock.rs`](crates/sigil-compiler/tests/determinism_lock.rs),
which walks the full test corpus (`tests/fixtures/` +
`tests/cve_corpus/` + `tests/z3_corpus/` = ~70 fixtures), compiles
each one twice via the public `compile_named_module` API, and asserts
byte-equality.

Run with:

```powershell
cargo test --release -p sigil-compiler --test determinism_lock
```

**Why this matters for agent-driven workflows.** Agents that
generate, compile, and reason about SIGIL programs can use the
compiled-Wasm SHA-256 as a memoization key. A `(source → wasm)` map
is stable across runs and across machines (within the same compiler
version), enabling:

- Skip re-compilation in agent workflows when a source matches a
  previously-seen hash.
- Use `wasm_inner SHA-256` as a content-addressed cache key in tool
  registries (the [`sigil-registry`](crates/sigil-registry/) crate
  already uses content fingerprints; this invariant makes its
  guarantees stronger).
- Verify a third party's compiled Wasm matches a known source SHA
  via `sigil verify-cert --wasm <file>`.

**What is NOT covered by this test:**

- **Cross-platform stability.** The test runs on whichever host the
  suite is invoked on. Determinism across Windows/Linux/macOS hosts
  is not asserted here; a separate harness (not in this PR) would
  cross-compare artefacts produced on each.
- **Cross-version stability.** `sigil-compiler` version bumps are
  allowed to change output bytes. The test only asserts run-over-
  run stability within a single binary; the verification certificate
  records the compiler version that produced a given Wasm artefact.
- **Z3 timing determinism.** Z3's wall-clock time is famously
  nondeterministic (see the variance discussion above); only Z3's
  OUTPUT for a given query is stable, which is what this test
  asserts via the resulting Wasm bytes.

**Honest caveat.** Hash-stable compilation is an invariant we now
*verify*, not one we *proved at design time*. If a future pass
introduces nondeterminism (e.g., a `HashMap` iteration leaking into
emitted bytecode, a thread-pool scheduling change in a parallel
pass, a system-clock dependency), the lock test will catch it on
the next CI run. The codebase already uses `BTreeMap` / `BTreeSet`
heavily where iteration order matters; the test confirms that
discipline holds across the full pipeline as of this PR.

---

## Methodology

### Throughput

- For each `.sigil` fixture in `tests/fixtures/`, `tests/cve_corpus/`,
  `tests/z3_corpus/`:
  - One warm-up call to `compile_named_module` (discarded).
  - Loop: time the call with `std::time::Instant::now()` → samples
    vector. Continue until trailing 30-sample CV < 5%, or sample
    count reaches 500.
  - Report `n`, median, P90, max, CV%, convergence flag.
- Per-corpus aggregation excludes fixtures with CV ≥ 20% (the **✗**
  flag) from medians/P90s/totals. Dropped count is published.
- Source: [`crates/sigil-compiler/examples/throughput.rs`](crates/sigil-compiler/examples/throughput.rs)

### Wasm size

- For each pair `bench/wasm-size/0N_<slug>/`:
  - Compile `main.sigil` via the public compiler API; record
    `wasm_inner.len() + wasm_outer.len()`.
  - `cargo clean --manifest-path .../Cargo.toml` (defeats incremental
    cache contamination — fence MI-4).
  - `cargo build --release --target wasm32-unknown-unknown
    --manifest-path .../Cargo.toml`; record the produced `.wasm`'s
    `fs::metadata().len()`.
- The mandated `[profile.release]` block (opt-level=s, panic=abort,
  lto=true, strip=true, codegen-units=1) is verbatim-pinned by
  driver test `rust_release_profile_pinned` (lto flipped to `true`
  2026-07-01 so the Rust side is best-effort).
- If `wasm-opt` is on PATH, `-Oz --all-features` is applied per
  module and the optimized columns are emitted; SIGIL inner/outer
  are optimized separately and summed.
- Source: [`crates/sigil-compiler/examples/wasm_size.rs`](crates/sigil-compiler/examples/wasm_size.rs)

---

## Reproducibility

```powershell
# Throughput, default features (solver ON)
cargo run --release --quiet --example throughput -p sigil-compiler

# Throughput, no solver
cargo run --release --quiet --no-default-features --features json --example throughput -p sigil-compiler

# Wasm size (requires wasm32-unknown-unknown target; put Binaryen's
# wasm-opt on PATH to get the -Oz columns)
rustup target add wasm32-unknown-unknown
cargo run --release --quiet --example wasm_size -p sigil-compiler

# Driver: 10 structural checks
cargo test --release -p sigil-compiler --test wasm_size_pairs
```

Expect numbers to differ from the published table on different
hardware. Differences in the order of 50% are not unusual between
laptop / desktop / VM environments; we do not claim these numbers
are universal.

---

## Honest caveats

- **n = 5 paired programs is a credibility instrument, not a
  performance characterization.** Workloads are author-chosen and
  skew toward small, capability-mediated programs. We do not
  benchmark crypto, heavy numeric, or GC-heavy workloads.
- **No CI gating.** These numbers are reproducible artefacts, not
  continuous integration assertions. They may drift between PRs.
  The driver pins structure, not numerical values.
- **`-Oz` numbers depend on the Binaryen release.** Measured with
  version_130; other releases will shift optimized bytes by a few
  percent. Raw numbers remain the toolchain-independent baseline.
- **Behavioural equivalence between SIGIL and Rust modules is not
  driver-enforced.** Four of five pairs need SIGIL host imports
  (spawn, send, alloc, FFI, fuel) that would require a mini-runtime.
  Equivalence is verified by manual inspection of each pair's
  `SPEC.md`. Reviewers can read both sources side-by-side in ~5
  minutes per pair.
- **Z3 timing variance dominates CV on Z3-heavy fixtures.** The
  median is what we publish; the P90 and max columns show how heavy
  the tail can be. Z3's portfolio solver is nondeterministic; a
  fixture that compiles in 5 ms on one run may take 15 ms on the
  next.

---

## Cross-references

- [`COMPARISON.md`](COMPARISON.md) — feature comparison vs Pony /
  Rust / Joe-E / Erlang / Caja with cited primary sources.
- [`bench/comparison/PRE-FLIGHT.md`](bench/comparison/PRE-FLIGHT.md)
  — citation pre-flight (source of truth for COMPARISON.md).
- [`bench/throughput-solver-on.md`](bench/throughput-solver-on.md)
  and [`bench/throughput-solver-off.md`](bench/throughput-solver-off.md)
  — full per-fixture throughput detail.
- [`tests/wasm_size_pairs.rs`](crates/sigil-compiler/tests/wasm_size_pairs.rs)
  — driver enforcing structural pinning.
- [`ATTACK-MATRIX.md`](ATTACK-MATRIX.md) and
  [`CVE-MATRIX.md`](CVE-MATRIX.md) — the security story.
