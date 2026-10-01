# SIGIL Performance — measured numbers

**One-shot, doc-published. Throughput measured 2026-05-17; Wasm size
(raw + `-Oz`) re-measured 2026-07-01; fuel-instrumentation runtime
overhead measured 2026-09-30 on an idle host, six runs at two recorded
clock settings (a 2026-09-20 run on a contended host is kept as a
secondary table), all on the environment recorded below. Not a
continuous benchmark.**

This document publishes three measurements:

1. **Compile / verify throughput** over the existing 69-file test
   corpora, with and without Z3.
2. **Wasm output size** for 5 paired SIGIL + Rust→Wasm programs,
   structurally pinned by [`tests/wasm_size_pairs.rs`](crates/sigil-compiler/tests/wasm_size_pairs.rs).
3. **Fuel-instrumentation runtime overhead** for one metering-heavy
   tool run through the forge path, with the host-call decrements
   and the Wasmtime backstop separated
   ([`bench/fuel-overhead/`](bench/fuel-overhead/)).

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
- **For the runtime-overhead measurements (2026-09-20 and
  2026-09-30):** same CPU / RAM (re-confirmed from `Win32_Processor` /
  `Win32_ComputerSystem` on each day); OS build 10.0.26200 on 09-20 and
  10.0.26300 on 09-30; rustc 1.98.0 (88d9e12ae 2026-08-18); cargo
  1.98.0 (797e8a9bc 2026-08-05); target `x86_64-pc-windows-gnu`;
  wasmtime 47.0.4 (the version `Cargo.lock` pins for `sigil-runtime`)

CPU governor / thermal state was not externally controlled. The
machine was idle (no other CPU-bound processes) for the 2026-05-17
and 2026-07-01 measurements. For the runtime-overhead runs the host
state is *recorded* rather than asserted: each of the six 2026-09-30
runs was admitted by a runner that requires a 60 s window under 5 %
mean / 15 % peak load with no compiler process alive, logs the load
once per second through the run, and records the clock the OS
reported before and after it (the headline's record:
[`bench/fuel-overhead/2026-09-30-idle-fullclock/host_state.json`](bench/fuel-overhead/2026-09-30-idle-fullclock/host_state.json);
five of the six record a capped clock, see *The clock* in that
section); the 2026-09-20 run was **not** idle (see its table's caveat).
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
- **Fuel-decrement instructions.** SIGIL inserts a fuel decrement
  before each direct call site and at each loop back-edge (corrected
  2026-09-20: this bullet said "at each function entry"; the count
  per direct call is the same, but the decrement is emitted at the
  call site, and the full placement rule — including what is *not*
  charged — is in the runtime-overhead section below). For
  `04_bounded_loop` with a hot loop, this is visible bytes per
  iteration in the code section.
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

## Fuel-instrumentation runtime overhead

**Last measured:** 2026-09-30 (release build, one workload, one
machine, one day, idle host, six runs at two recorded clock settings;
a 2026-09-20 contended run is kept as a secondary table). This is a
*metering-cost* measurement on a metering-heavy tool, not a general
runtime characterization; read the caveats at the end of this section
before quoting it.

Everything above this section times the **compiler**. This section
times the forge step that follows verification — what an agent
waits on when `sigil forge` runs an already-compiled tool: a fresh
Wasmtime `Store`, a fresh `Instance`, the input copy, and the
metered execution — and isolates what the fuel instrumentation
costs inside it.

### Where fuel is charged

The compiler emits every fuel decrement as `i32.const N; call
sigil.fuel_decrement`: a call from Wasm into a host closure, not an
inline global subtraction. Decrements sit before each direct call,
`send`, `ask` and `spawn`; at each AIR loop back-edge; at record and
static allocations; and per byte for `str ==`. They do **not** sit
at indirect calls, at dynamic `alloc(n)`, or inside the intrinsic
contains-scan loops, which are fuel-exempt. Independently of those,
`execute_ephemeral` runs every module with Wasmtime's own
`consume_fuel` backstop on (a 10^10-unit cap, so a hostile module
that never calls the import still cannot loop forever). Two meters
are therefore active on every shipped tool run, and the benchmark
separates them.

### Workload

[`tools/task098_levenshtein_distance.sigil`](tools/task098_levenshtein_distance.sigil):
a two-row Levenshtein DP over two strings split at the first `\n`.
Its inner loop makes five direct calls per DP cell (`read_u32` ×3,
`min3`, `write_u32`) plus the back-edge, so it pays about six
host-call decrements per cell (fuel consumed ÷ L² = 6.07 at L=100,
6.01 at L=500 and L=1000) and exercises no other metered construct.
That is what makes it *metering-heavy*: the useful work per cell is
a few loads, adds and compares; every decrement is a host call; and
nothing in the loop is fuel-exempt.

Inputs are two seeded-random `[a-z]` strings of length L joined by
one `\n`, for L ∈ {0, 100, 500, 1000}; L=0 is the bare `\n` and
measures the fixed per-call cost. The seed, each input's SHA-256,
the expected distance and the fuel budget passed are recorded in
each run's `summary.md` under
[`bench/fuel-overhead/`](bench/fuel-overhead/);
`kitten\nsitting` → `3` is asserted on every condition before any
timing.

### Modules and conditions

- **A0** — the tool's Wasm exactly as `sigil forge` compiles it
  (`compile_tool_with_limits_and_context` with the default limits and
  context, the call `crates/sigil-cli/src/forge.rs` makes): 2012
  bytes, sha256 `f6fc24c7…`. The harness asserts these bytes equal
  plain `compile_tool`'s, and they equal what `sigil check
  --emit-wasm` writes from the `main` binary at this commit.
- **A1** — A0 with each of its 15 `call 0` sites re-encoded as `drop`
  (`sigil.fuel_decrement` is import 0 in every module the compiler
  emits, and every call to it follows an `i32.const`, so the body
  stays well-typed). Only the code section is re-encoded; the other
  8 sections are copied byte-for-byte and their digests compared;
  the result validates; and it must produce byte-identical output on
  every input or the run aborts.

| Condition | Module | Path | Fuel active |
|---|---|---|---|
| **A** | A0 | shipped `execute_ephemeral` | host-call decrements + Wasmtime backstop — what `sigil forge` runs |
| **B** | A1 | shipped `execute_ephemeral` | Wasmtime backstop only |
| **C** | A1 | bench-only mirror, `consume_fuel(false)` | none — the fuel-free baseline |
| **D** | A0 | bench-only mirror, `consume_fuel(false)` | host-call decrements only |
| A′, B′ | A0, A1 | bench-only mirror, `consume_fuel(true)` | as A, B — reported so the mirror's agreement with the shipped path is itself a measured number |

The shipped runtime has no seam that turns the backstop off, and
this measurement adds none: C and D run on a mirror of
`execute_ephemeral_inner` built inside the harness (same fuel shim,
same bump allocator, same 16 MB wall, unused imports bound to
traps). What `sigil forge` executes is unchanged. The fuel budget
passed per L is twice what A consumed on a calibration run — never
the CLI's default 100,000, which L ≥ 500 would exhaust — and every
sample must return `Ok` with the expected output.

### Results

Six runs were taken on 2026-09-30 through the same runner, the same
harness binary (SHA-256 `91cb6548…`, recorded in every
`host_state.json`) and the same inputs, and they fall into two sets by
the clock the runner recorded. The runner stores psutil's `cpu_freq`
(WMI `CurrentClockSpeed` on Windows) before its idle check and after
the run. The five runs taken between 14:11 and 14:45 UTC record
3203 of 3504 MHz, both times, in every one of them — the
**capped-clock** set; the run taken at 20:20 UTC records
3504 of 3504 MHz — the **full-clock** run. The author reports a
Windows maximum-processor-state cap in force during the first five and
lifted before the sixth; this document relies only on what
`host_state.json` recorded. The harness cannot observe the
instantaneous clock, so nothing here states the frequency the CPU
actually ran at (see *The clock* below for what the two sets' timings
say about it).

The **headline for absolute figures** — ns per DP cell, ns per
`fuel_decrement`, the fixed per-call cost and the cold first call — is
the full-clock run, because it is the one run whose recorded clock
equals the processor's recorded maximum (3504 of 3504 MHz). Full
per-block tables, input hashes and block order in
[`bench/fuel-overhead/2026-09-30-idle-fullclock/summary.md`](bench/fuel-overhead/2026-09-30-idle-fullclock/summary.md),
every sample in
[`samples.tsv`](bench/fuel-overhead/2026-09-30-idle-fullclock/samples.tsv),
the load log and thresholds in
[`host_samples.tsv`](bench/fuel-overhead/2026-09-30-idle-fullclock/host_samples.tsv)
/ [`host_state.json`](bench/fuel-overhead/2026-09-30-idle-fullclock/host_state.json).
Host **idle**, runner-admitted: 60 s window mean 1.9 %, peak 10.9 %,
no compiler process; during the 8 s run mean 7.9 %, peak 14.2 %, no
compiler process, no sample at or above 15 %; harness pinned to one
logical CPU at High priority; seed `0x5347494c2d443500`.

The five capped-clock runs are the **repeatability set**: the author's
[`2026-09-30-idle/`](bench/fuel-overhead/2026-09-30-idle/) — the set's
reference and the first of the set, taken at 14:11 UTC — and the two runs
taken immediately after it
([`2026-09-30-idle-repeat2/`](bench/fuel-overhead/2026-09-30-idle-repeat2/),
[`2026-09-30-idle-repeat3/`](bench/fuel-overhead/2026-09-30-idle-repeat3/)),
then two the reviewer took through the same runner about half an hour
later
([`2026-09-30-idle-review4/`](bench/fuel-overhead/2026-09-30-idle-review4/),
[`2026-09-30-idle-review5/`](bench/fuel-overhead/2026-09-30-idle-review5/)).
They are compared with their own capped-clock reference, never with the
full-clock headline; *The clock* below compares the two sets.

One rule produces every statistic here and in the linked `summary.md`
files, the harness's own (`fn percentile` / `fn cv_pct` in the
source): median = sorted[round((n−1)/2)], P90 = sorted[round(0.9 (n−1))],
CV = sample standard deviation ÷ mean over all of a block's samples;
derived quantities are taken from the raw nanosecond statistics, never
from the rounded µs the tables print.
A "within X %" bound is the largest deviation rounded up to the next
tenth of a percent and an "under N %" bound to the next whole percent,
so no bound sits below the value it bounds; ranges and single values
are rounded to the printed precision.
[`bench/fuel-overhead/check_doc.py`](bench/fuel-overhead/check_doc.py)
recomputes every table and every number in this section from the
committed `samples.tsv`, `host_state.json` and `summary.md` files and
fails unless each pinned table and scalar appears in the section
verbatim exactly its expected number of times — a number this section
repeats is pinned at every occurrence, so a stale duplicate fails as
surely as a wrong one. What it cannot recompute it lists by name and
provenance and pins verbatim only: settings quoted from the harness
and runtime source, the tool's shape, and the 2026-09-20 session-log
figures below. The `bench-tests` CI job runs it and its `--self-test`.

In the full-clock run 16 of the 24 blocks converged at the 30-sample
floor; the other seven ran to n = 31–53 under the convergence rule
(trailing-30 CV < 5 % or 500 samples) and closed with a CV of
5.1–9.1 % (D:L0 7.6, A′:L0 5.1, B:L100 5.6, B′:L100 5.2, B:L500 5.4,
B′:L500 9.1, B:L1000 5.7), three of them at L ≥ 500; the harness marks
them ⚠ in the median table below. Over all 24 blocks CV 0.7–9.1 %, and
the largest median-over-minimum gap in any block is 3.3 % (B′ at L = 0;
within 1.3 % at L ≥ 500). In the repeatability set the capped-clock reference
flagged none of its 24 blocks and the other four flagged 1–4 blocks
each, 11 in all, every one at L ≤ 100. This is disclosed as an
observation; its cause was not measured. Clock variation under turbo is
a plausible hypothesis for the wider spread at the full clock and is
only that — nothing in the record tests it. What protects the quoted
figures is the existing rule that they come from the L ≥ 500 rows,
where the two statistics agree to 1.3 %; both are published.

Per-block **minimum** (µs), full-clock run:

| L | A | B | C | D | A′ | B′ |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 56.6 | 55.9 | 30.4 | 30.8 | 30.6 | 30.3 |
| 100 | 420.9 | 200.4 | 118.2 | 351.6 | 396.3 | 174.2 |
| 500 | 9108.8 | 3649.1 | 2271.5 | 7954.3 | 9159.0 | 3639.5 |
| 1000 | 36368.0 | 14439.9 | 8972.5 | 31734.8 | 36541.5 | 14381.2 |

Per-block **median** (µs), each with n, P90 (µs), CV (%) and the
harness's flag (✓ CV < 5 %, ⚠ < 20 %):

| L | A | B | C | D | A′ | B′ |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 57.2 (30; 59.3; 3.2 ✓) | 56.7 (30; 59.2; 3.1 ✓) | 31.1 (30; 31.8; 2.1 ✓) | 31.6 (31; 34.9; 7.6 ⚠) | 31.2 (31; 32.4; 5.1 ⚠) | 31.3 (30; 33.2; 4.3 ✓) |
| 100 | 427.0 (30; 438.5; 1.6 ✓) | 204.8 (53; 213.8; 5.6 ⚠) | 121.3 (30; 124.5; 3.2 ✓) | 356.1 (30; 361.2; 2.7 ✓) | 402.5 (48; 414.5; 4.7 ✓) | 175.3 (32; 181.2; 5.2 ⚠) |
| 500 | 9220.6 (30; 9514.1; 1.9 ✓) | 3667.9 (49; 3710.0; 5.4 ⚠) | 2282.1 (30; 2316.0; 1.0 ✓) | 8007.6 (30; 8122.6; 2.4 ✓) | 9246.0 (30; 9519.6; 1.5 ✓) | 3669.3 (32; 3743.9; 9.1 ⚠) |
| 1000 | 36567.2 (30; 37861.0; 1.7 ✓) | 14526.5 (43; 15310.9; 5.7 ⚠) | 9009.2 (30; 9056.9; 0.7 ✓) | 31844.6 (30; 32264.9; 1.0 ✓) | 36693.1 (30; 37767.3; 1.2 ✓) | 14455.8 (30; 14622.8; 0.8 ✓) |

Derived, on **net minima** (each condition minus its own L=0 minimum;
fuel = what A consumed; A′/A and B′/B also on net values):

| L | A/C | B/C | D/C | (A−B)/L² | (B−C)/L² | (A−B)/fuel | fuel (A) | A′/A | B′/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 100 | 4.15 | 1.65 | 3.65 | 22.0 ns | 5.7 ns | 3.62 ns | 60,714 | 1.004 | 0.996 |
| 500 | 4.04 | 1.60 | 3.54 | 21.8 ns | 5.4 ns | 3.63 ns | 1,503,516 | 1.008 | 1.004 |
| 1000 | 4.06 | 1.61 | 3.55 | 21.9 ns | 5.4 ns | 3.65 ns | 6,007,016 | 1.005 | 0.998 |

The same on **net medians** (the convention the throughput section
uses):

| L | A/C | B/C | D/C | (A−B)/L² | (B−C)/L² | (A−B)/fuel | A′/A | B′/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 100 | 4.10 | 1.64 | 3.60 | 22.2 ns | 5.8 ns | 3.65 ns | 1.004 | 0.972 |
| 500 | 4.07 | 1.60 | 3.54 | 22.2 ns | 5.4 ns | 3.69 ns | 1.006 | 1.007 |
| 1000 | 4.07 | 1.61 | 3.54 | 22.0 ns | 5.5 ns | 3.67 ns | 1.004 | 0.997 |

Repeatability — the same derived quantities on net minima in the five
capped-clock runs (capped reference / repeat 2 / repeat 3 / review 4 /
review 5; the first three the author's consecutive runs, the last two
the reviewer's through the same binary and inputs). Their ns columns
are at the capped clock and are not the headline's:

| quantity | L = 500 | L = 1000 |
|---|---|---|
| A/C | 4.05 / 4.05 / 4.05 / 4.34 / 4.06 | 4.06 / 4.07 / 4.06 / 4.36 / 4.05 |
| B/C | 1.60 / 1.60 / 1.60 / 1.60 / 1.61 | 1.61 / 1.61 / 1.61 / 1.61 / 1.61 |
| D/C | 3.54 / 3.55 / 3.54 / 3.55 / 3.56 | 3.57 / 3.55 / 3.55 / 3.55 / 3.54 |
| (A−B)/L² | 35.0 / 35.0 / 35.0 / 39.2 / 35.0 ns | 35.0 / 35.0 / 35.0 / 39.2 / 34.9 ns |
| (B−C)/L² | 8.6 / 8.6 / 8.6 / 8.6 / 8.7 ns | 8.7 / 8.7 / 8.7 / 8.7 / 8.7 ns |
| (A−B)/fuel | 5.82 / 5.82 / 5.81 / 6.51 / 5.81 ns | 5.83 / 5.83 / 5.82 / 6.53 / 5.81 ns |
| C net / L² | 14.3 / 14.3 / 14.3 / 14.3 / 14.2 ns | 14.3 / 14.3 / 14.3 / 14.3 / 14.3 ns |
| A′/A | 1.176 / 1.009 / 1.003 / 0.939 / 1.005 | 1.178 / 1.008 / 1.005 / 0.937 / 1.006 |
| B′/B | 1.000 / 0.998 / 0.999 / 0.999 / 1.001 | 0.999 / 1.000 / 0.999 / 0.998 / 1.000 |

Cold first call through the shipped path (a module-cache miss, so it
includes Wasmtime's compilation of the 2 KB module): 3.3–4.0 ms over
its 6 calls in the full-clock run, process pinned to one logical CPU;
5.3–6.4 ms over the five capped-clock runs' 30 calls.
`Module::from_binary` alone on the mirror at the full clock: 2.6–3.0 ms
with fuel off, 3.1–3.6 ms with fuel on (the fuel instrumentation is
compile-time work too); at the capped clock 4.0–4.6 ms off / 5.1–6.5 ms
on.

### Reading the numbers

Quote the L = 500 and L = 1000 rows of the full-clock run; at L = 100
the L=0 subtraction is 8–28 % of the value depending on the condition.
Minima and medians agree within 1.3 % at L ≥ 500, so either statistic
gives the same figures to the precision below.

- **Per DP cell** (full-clock run, net minima at L = 1000): the fuel-free
  run costs 8.9 ns (C: 8942 µs net over 10⁶ cells); the Wasmtime
  backstop adds 5.4 ns (B − C); the host-call decrements add 21.9 ns
  (A − B), i.e. **3.7 ns per `sigil.fuel_decrement` call** at six calls
  per cell. With both meters on a cell costs 36.3 ns, **4.1× the
  fuel-free time**, of which the metering is 27.4 ns. The L = 500 row
  and the median-based table give the same figures to this precision.
- **Which meter costs what:** the host-call decrements are 80 % of the
  metering cost on this tool (D/C = 3.54–3.55 with the backstop off;
  B/C = 1.60–1.61 with only the backstop on), and the two costs add
  (A − C = 27.4 ns ≈ 21.9 + 5.4).
- **Between-process spread — the mirror and the shipped path:** within
  a process every block at L ≥ 500 has a CV under 10 % (under 5 % in
  all but three blocks of the full-clock run; at L ≤ 100 the largest CV
  in any idle-run block is 19.9 % (A′ at L = 0 in repeat 3), still
  within the harness's ⚠ band), and B′/B is 0.998–1.001 at L ≥ 500 in
  all five capped-clock runs. Across processes, one executor
  at a time has sat off the others, twice in six runs. In the
  capped-clock reference run (`2026-09-30-idle`) the mirror's
  A0-with-backstop executor ran 13–18 % slower than the shipped path at
  every L (A′/A 1.13–1.18). In review 4 it was the *shipped* A executor
  that ran 6.6–7.4 % slower than the capped reference at every L
  (medians 62657.6 vs 58399.6 µs at L = 1000, outside the 4.9 %
  within-run CV of the reference's A block), which puts that run's
  net-minima metering at 39.2 ns per cell, 6.51–6.53 ns per decrement
  and A/C 4.36 at L = 1000, while its B, C, D and B′ blocks reproduced
  the reference within 0.8 % at L ≥ 500 (minima and medians alike); at
  L = 100 they were 1.8–7.3 % above it and at L = 0 every one of the six
  blocks was 16–31 % above it — the fixed-cost rows, which the netting
  removes from every derived column. Repeats 2 and 3 and review 5
  reproduce the capped reference's every derived cell except A′/A
  within 1 % (largest 0.8 %, D/C at L = 1000 in review 5); their A′/A is
  14.2–14.7 % below it, which is the reference's own A′ drift seen from
  the other side. In the full-clock headline neither executor drifted:
  A′/A is 1.005–1.008 and B′/B 0.998–1.004 on net minima (1.004–1.006
  and 0.997–1.007 on net medians) at L ≥ 500. Each executor owns its
  own `Engine` and compiled module, so code placement is the
  hypothesis; the effect was not reproduced on demand. Every run is
  published as measured, none dropped. The consequence for quoting: the
  within-process spread would support three significant figures, the
  between-process spread does not — in the capped-clock set A/C is
  4.05–4.07 in four runs and 4.34–4.36 in one, the per-decrement cost
  5.81–5.83 ns in four and 6.51–6.53 ns in one, while B/C (1.60–1.61)
  and D/C (3.54–3.57) hold in all five. Quote ratios to two significant
  figures and say which run they come from.
- **Fixed per-call cost** (L=0 minima): 56–57 µs through `execute_ephemeral`
  and 30–31 µs on the mirror in the full-clock run; 82–96 µs and
  42–56 µs in the five capped-clock runs, where review 4 alone carries
  the top of both ranges, on every executor (the netting removes it
  from that run's derived columns). The shipped path registers 23 host
  closures on every call in the measured `--no-default-features` build
  — the 9 `sigil.*` imports (`fuel_decrement`, `fuel_exhausted`,
  `alloc`, `send`, `ask`, `spawn`, `cap_restrict`, `cap_split`,
  `cap_mint`) plus the 14 `ffi.*` shims of `link_ffi_imports`, twelve
  of which clone the grants; a `--features solver` build adds
  `ffi.z3_check` for 24 — whether or not the module imports them
  (counted as `.func_wrap(` call sites in
  `crates/sigil-runtime/src/ephemeral.rs`). The module under test
  imports only `sigil.*` (eight of them), so the mirror wraps two and
  traps the rest. The fixed cost is netted out of every derived column.
- **The clock.** Two settings are in the record, distinguished only by
  what `host_state.json` stored (psutil `cpu_freq`, WMI
  `CurrentClockSpeed`, read before the idle check and after the run and
  equal both times in every run): 3203 of 3504 MHz in the five
  capped-clock runs, 3504 of 3504 MHz in the full-clock run. What the
  two sets agree on and where they differ, at L ≥ 500 on net minima:
  the ratio columns A/C, B/C, D/C and B′/B of every capped-clock run
  agree with the full-clock run within 0.7 %, except A/C in review 4,
  +7.4–7.5 % (that run's A drift), and A′/A within 0.5 % in the three
  runs in which neither executor drifted (repeats 2 and 3, review 5);
  the absolute net columns (A−B)/L², (B−C)/L², (A−B)/fuel and
  C net / L² scale by 1.59–1.60×, except review 4's two A-bearing cells,
  which read 1.79× (the same drift); and the ends of the cold-first-call
  range 1.60–1.61× (the capped runs' fastest over the headline's
  fastest, slowest over slowest). The recorded clock figures differ by
  1.09× (3504 / 3203), not by 1.6×, so at most one of the two recorded
  figures can be the effective clock of its set, and the record cannot
  say which (as general background, not something measured here: WMI
  reports the package clock coarsely and records no turbo state); this
  document therefore quotes nanoseconds, not cycles. The 2026-09-20 run
  below, whose clock was not recorded, reproduces the full-clock
  headline's net minima: all nine derived columns within 1.3 % and
  every per-block minimum within 0.8 % at L ≥ 500 (A/C 4.07–4.08
  against 4.04–4.06, (A−B)/L² 21.9–22.2 against 21.8–21.9 ns). Its
  minima were that run's honest cells, and this agreement is consistent
  with, but does not record, the same clock.
- **What this does and does not say:** a tool whose inner loop is five
  direct calls per cell pays ~4× for metering in the shipped runtime,
  3.7 ns per decrement at the full clock (5.8 ns at the capped clock).
  A tool that spends its time in unmetered or per-byte-metered
  constructs pays a different, unknown fraction. This section is a
  cost-of-instrumentation measurement, not an execution-speed claim,
  and the paper may cite it only once this section is present at the
  commit the paper pins — ratios to two significant figures with the
  between-process spread stated (4.1×, 1.6×, 3.5× — A/C read 4.3–4.4× in
  one of six runs), absolute costs from the full-clock run with its
  clock record stated.

### The 2026-09-20 run (contended host, secondary)

The first measurement, kept as part of the record and **not** quotable
on its own: the host was not idle. Its `summary.md` header records
a resting load of 13–25 % (of the host's 16 logical CPUs) with other
`cargo` builds intermittent, and a 79 s wall time; the rest of this
paragraph is from that session's scratch-runner log, which is not in
the repository: three other agent sessions ran `cargo` builds on the
host; the scratch runner waited for 5 s under 25 % with no compiler
process alive, pinned the harness to one logical CPU at High priority,
sampled total CPU once per second, and recorded no clock; the published
attempt (18 of 18) saw during-run load mean 24.1 %, max 50.4 %, with a
mostly idle `rustc` alive for 49 of its 79 s. Full tables in
[`bench/fuel-overhead/2026-09-20-contended/summary.md`](bench/fuel-overhead/2026-09-20-contended/summary.md)
(its derived tables' A′/A and B′/B columns are raw ratios; the net
values are here).

Per-block **minimum** (µs):

| L | A | B | C | D | A′ | B′ |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 64.7 | 57.2 | 31.3 | 30.3 | 60.3 | 59.5 |
| 100 | 421.9 | 200.4 | 118.5 | 351.8 | 398.7 | 175.5 |
| 500 | 9137.7 | 3651.1 | 2261.1 | 7968.5 | 9152.4 | 3624.0 |
| 1000 | 36631.0 | 14465.6 | 8992.8 | 31853.6 | 36568.0 | 14416.2 |

Per-block **median** (µs), with n and the convergence flag (✓ CV <
5 %, ⚠ < 20 %, ✗ ≥ 20 %; n = 500 means the block hit the ceiling
without converging):

| L | A | B | C | D | A′ | B′ |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 107.3 (35 ⚠) | 58.4 (30 ✓) | 32.0 (30 ✓) | 31.3 (31 ⚠) | 62.0 (30 ✓) | 61.8 (32 ⚠) |
| 100 | 429.7 (46 ✗) | 207.2 (84 ✗) | 121.8 (84 ⚠) | 521.2 (266 ✗) | 415.5 (50 ✗) | 243.3 (247 ✗) |
| 500 | 10785.7 (500 ⚠) | 3787.0 (500 ✗) | 2326.2 (500 ✗) | 9579.8 (500 ✗) | 9235.6 (30 ✓) | 3893.5 (500 ✗) |
| 1000 | 50736.2 (500 ⚠) | 14532.7 (58 ✓) | 9532.4 (500 ⚠) | 38696.4 (500 ⚠) | 36683.7 (30 ✓) | 17988.6 (500 ⚠) |

Derived on **net minima** (the only statistic that survived the load;
A′/A and B′/B computed net here):

| L | A/C | B/C | D/C | (A−B)/L² | (B−C)/L² | (A−B)/fuel | A′/A | B′/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 100 | 4.10 | 1.64 | 3.69 | 21.4 ns | 5.6 ns | 3.52 ns | 0.947 | 0.810 |
| 500 | 4.07 | 1.61 | 3.56 | 21.9 ns | 5.5 ns | 3.64 ns | 1.002 | 0.992 |
| 1000 | 4.08 | 1.61 | 3.55 | 22.2 ns | 5.4 ns | 3.69 ns | 0.998 | 0.996 |

On net medians the same columns read 3.59 / 4.65 / 5.33 for A/C at
L = 100 / 500 / 1000 — contaminated: three of the four shipped A and B
blocks at L ≥ 500 ran to the 500-sample ceiling under load while the
mirror's A′ blocks converged at 30 samples, and its medians ran up to
66 % above its minima. That is what the idle re-runs replaced. Against the
full-clock headline this run's net minima agree on every derived column
within 1.3 % (see *The clock* above), so the per-decrement figure reads
3.7 ns on both at L = 1000 (3.6 ns on both at L = 500); against the
capped-clock set the ratios hold and the ns columns differ by the clock
factor stated there. The full-clock headline's medians equal its
minima to 1.3 % at L ≥ 500.

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

### Fuel-instrumentation runtime overhead

- Build A0 and A1 as described in that section; A1 must validate and
  must produce byte-identical output on every input.
- Sanity (`kitten\nsitting` → `3` on every condition) and calibration
  (fuel consumed by A per L; budget passed = 2×) before any timing.
- Cold first calls: alternate A0 and A1 through the shipped path so
  each call misses the runtime's one-entry module cache and includes
  Wasmtime compilation; reported separately, never mixed into blocks.
- One block per (condition, L), blocks in seeded-random order, never
  alternating modules inside a block (the one-entry cache is keyed by
  bytes and would recompile on every switch). Per block: one warm-up
  call discarded; then time each `execute_ephemeral` (or mirror) call
  with `std::time::Instant`; stop at trailing-30-sample CV < 5% or at
  500 samples — the throughput rule above.
- Report n, min, median, P90, max, CV%, flag and fuel consumed per
  block. Derived ratios are taken on *net* values (each condition
  minus its own L=0 value) so the two paths' different fixed costs
  cancel, and are reported twice: on medians (the convention above)
  and on minima (the uncontended cost; see the host-state note in
  that section for why both are published).
- The harness is driven by
  [`bench/fuel-overhead/quiet_run.py`](bench/fuel-overhead/quiet_run.py):
  it samples total CPU load once per second and starts the harness
  only after a full 60 s window with mean < 5 % and peak < 15 % and no
  `cargo` / `rustc` / `rustdoc` / `clippy-driver` / `lean` / `lake`
  process alive (retrying up to 20 min, then refusing); it starts the
  harness suspended, pins it to one logical CPU, raises it to High
  priority, resumes it, and keeps sampling until it exits. The
  thresholds it used, the accepted window, the during-run load and the
  harness's SHA-256 are written beside the run (`host_state.json`,
  `host_samples.tsv`). The 2026-09-20 run used an earlier scratch
  runner with the same pin and priority but a 5 s window under 25 % —
  a figure from that session's scratch-runner log, which is not in the
  repository.
- Source: [`crates/sigil-runtime/examples/fuel_overhead.rs`](crates/sigil-runtime/examples/fuel_overhead.rs);
  raw samples, host-load samples and the harness's own summary per
  run in [`bench/fuel-overhead/`](bench/fuel-overhead/). Every table
  and number the section quotes is re-derived from those samples under
  the harness's rule by
  [`bench/fuel-overhead/check_doc.py`](bench/fuel-overhead/check_doc.py),
  which fails unless each pinned table and scalar appears verbatim
  exactly its expected number of times (the constants it cannot
  recompute are listed with their provenance and pinned verbatim);
  `--self-test` plants changes, a stale duplicate of a repeated number
  among them, and requires every one to be caught. The `bench-tests`
  CI job runs both.

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

# Fuel-instrumentation runtime overhead (release only: the harness
# refuses a debug build unless --allow-debug is passed, and a debug
# number is not one this document publishes). Build first, on its
# own — the build is load — then let the quiet-window runner admit
# the run once the machine is idle (needs psutil). Output lands in
# bench/fuel-overhead/<today>-idle/; the directory's .gitignore keeps
# the harness's a0.wasm / a1.wasm out of git.
cargo build --release --no-default-features -p sigil-runtime --example fuel_overhead
python bench/fuel-overhead/quiet_run.py
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
  The driver pins structure, not numerical values. The fuel-overhead
  section is the one exception: `check_doc.py` re-derives its numbers
  from the committed samples in the `bench-tests` job — a consistency
  gate on the document, not a re-measurement.
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
- **The runtime-overhead ratio is a metering-cost figure for one
  metering-heavy tool, not SIGIL's general execution overhead.** The
  Levenshtein tool pays ~6 host-call decrements per DP cell against a
  few loads, adds and compares. A tool whose time goes to dynamic
  `alloc(n)` (unmetered), to the intrinsic contains-scans
  (fuel-exempt), or to `str ==` (charged per byte, not per call)
  meters differently, and we did not measure one. n = 1 workload.
- **The fuel-free baseline does not run on `sigil forge`.** The
  shipped runtime cannot turn its Wasmtime backstop off, so
  conditions C and D run on a bench-only mirror of the same path.
  The A′/A and B′/B columns are the measured agreement between the
  mirror and the shipped path; the derived ratios net out the two
  paths' fixed costs before comparing them.
- **Idle is proven for the 2026-09-30 runs only.** Each of the six was
  admitted by the runner after a 60 s window under 5 % mean / 15 % peak
  load, with the load logged throughout; the 2026-09-20 run, kept as a
  secondary table, ran on a host with 13–25 % resting load and other
  cargo builds, and its medians for the long shipped-path blocks are
  contaminated. Only the idle runs are quotable.
- **The clock is recorded, not controlled.** Five of the six idle runs
  record 3203 of 3504 MHz and the full-clock headline 3504 of 3504 MHz
  (WMI `CurrentClockSpeed`, which as general background records no turbo
  state); the two sets' absolute times differ by about 1.6×, their
  ratios agree, and at most one of the two recorded figures can be the
  effective clock of its set — the record cannot say which. Absolute
  figures are quoted from the full-clock run with that record stated,
  never as cycles.
- **One executor per process can sit 7–18 % off the others.** Within a
  run every block at L ≥ 500 has a CV under 10 % (under 5 % in all but
  three blocks of the full-clock run), but across the six idle runs the
  mirror's A′ executor (capped-clock reference, 13–18 % slow) and the
  shipped A executor (review 4, 6.6–7.4 % slow) each drifted once while
  the other blocks held to 1 % at L ≥ 500; the full-clock headline shows
  neither drift. Ratios are therefore quotable to two significant figures with
  the spread stated (A/C 4.05–4.36 across the five capped-clock runs,
  4.04–4.06 in the full-clock headline), not to three.

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
- [`bench/fuel-overhead/`](bench/fuel-overhead/) — one dated
  directory per fuel-instrumentation runtime overhead run: raw samples
  (`samples.tsv`), the harness's own summary, the exact inputs and,
  for quiet-window runs, the host-load log; plus the runner.
- [`ATTACK-MATRIX.md`](ATTACK-MATRIX.md) and
  [`CVE-MATRIX.md`](CVE-MATRIX.md) — the security story.
