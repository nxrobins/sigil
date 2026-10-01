# Fuel-instrumentation runtime overhead — evidence directory

The numbers in PERFORMANCE.md's "Fuel-instrumentation runtime overhead"
section are read from here. One dated subdirectory per run; the harness is
[`crates/sigil-runtime/examples/fuel_overhead.rs`](../../crates/sigil-runtime/examples/fuel_overhead.rs).

| path | what |
|---|---|
| `2026-09-30-idle-fullclock/` | **the headline run** for absolute figures: idle host, proven by `host_samples.tsv` / `host_state.json`, which also records the full clock (psutil `cpu_freq` 3504 of 3504 MHz before and after) |
| `2026-09-30-idle/` | the **capped-clock reference** of the repeatability set: same gate and binary, `host_state.json` records 3203 of 3504 MHz; the run in which the mirror's A′ executor sat 13–18 % slow |
| `2026-09-30-idle-repeat2/`, `-repeat3/` | two further capped-clock runs under the same gate, taken by the author immediately after the reference |
| `2026-09-30-idle-review4/`, `-review5/` | two capped-clock runs the reviewer took through the same runner and binary about half an hour later (`--max-wait 300`, every threshold at its default); review4 is the run in which the shipped A executor sat 6.6–7.4 % slower than the reference — the between-process spread PERFORMANCE.md states |
| `2026-09-20-contended/` | the first run, on a host with other agents' builds; kept as the secondary table |
| `quiet_run.py` | the quiet-window runner: idle precondition, one-CPU pin, high priority, load log |
| `check_doc.py` | recomputes every table and number in PERFORMANCE.md's section from the committed `samples.tsv`, `host_state.json` and `summary.md` files under the harness's one statistics rule and fails unless each pinned table and scalar appears verbatim exactly its expected number of times (a repeated number is pinned at every occurrence); the constants it cannot recompute — harness and runtime settings, the tool's shape, the 2026-09-20 session-log figures — are listed with their provenance and pinned verbatim only; `--emit` prints the tables and pins to paste, `--self-test` proves the check fires on planted changes, a stale duplicate of a repeated number among them; the `bench-tests` CI job runs both |
| `.gitignore` | keeps the harness's `a0.wasm` / `a1.wasm` out of git (their SHA-256s are in each `summary.md`) |

Per run: `samples.tsv` (every timing sample, nanoseconds, one row per block, in
run order), `summary.md` (the harness's own report: input hashes, module
digests, per-block and derived tables, block order), `input_L*.txt` (the
seeded inputs). Quiet-window runs add `host_samples.tsv` (total CPU load once
per second through the idle check and the run), `host_state.json` (thresholds
used, accepted window, during-run load, the OS-reported CPU clock before and
after, pinned CPU, priority, harness SHA-256 and exit code) and
`harness_stdout.txt`.

## Redo

Two commands, from the repository root, the build on its own first (it is
load) and the measurement only once the machine is otherwise idle:

    cargo build --release --no-default-features -p sigil-runtime --example fuel_overhead
    python bench/fuel-overhead/quiet_run.py

The runner needs `psutil` (declared as the `fuel-overhead` extra of
`bench/pyproject.toml`: `python -m pip install -e "bench[fuel-overhead]"`, or
just `python -m pip install psutil`; without it the runner exits with a message
and writes nothing). It refuses to start the harness until a full 60 s window
shows mean load < 5 % and peak < 15 % with no cargo / rustc / lean / lake
process alive (retrying for up to 20 min, then giving up), and it records the
thresholds it used, so a run with relaxed ones cannot pass as strict. Harness
options go after a `--`, which separates them from the runner's own:

    python bench/fuel-overhead/quiet_run.py -- --seed 1 --lengths 0,100

(without the `--`, argparse rejects them: `--seed` is not a runner option).
