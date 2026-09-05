# sigil-bench — AutoForge Benchmark Harness

A Python harness that drives Claude through the [`sigil-mcp`](../crates/sigil-mcp)
agent loop and measures whether the AutoForge thesis actually works:
**given a blank-slate task description and only the three MCP tools
(`sigil_check`, `sigil_forge`, `sigil_lookup_error`), can a model
regenerate a working Sigil tool — and in how many attempts?**

This is the empirical pass on Phase 4 of the Sigil project. Step 1 made
diagnostics machine-readable (121 stable codes, JSON wire). Step 2 built
the MCP server. Step 3 (this) measures whether the structured feedback
is actually agent-actionable.

## What it does

For each task in [`tasks/`](tasks/):

1. Spawns a fresh `sigil-mcp` subprocess.
2. Asks Claude for a `.sigil` source given the task description, signature,
   required attributes, required effects, and host-supplied grants.
3. Compiles via `sigil_check`. On error, replays the diagnostics back to
   Claude (with a compact summary of older attempts to bound token cost)
   and asks for a corrected source. Loops up to `--max-attempts` times.
4. Once `sigil_check` is clean, runs `sigil_forge` once per input and
   compares `output_text` against the ground truth captured from the
   reference source (or a literal expected output for non-deterministic
   tasks like the HTTP fetcher).
5. Records pass/fail, attempt count, fuel consumed, and the failure-code
   histogram into a per-run directory under `bench/runs/<UTC-timestamp>/`.

## Install

From the repo root:

```bash
cargo build --release -p sigil-mcp           # builds the binary the harness drives
cd bench
python -m venv .venv
.venv/Scripts/python -m pip install -e .     # Windows
# or: .venv/bin/python -m pip install -e .   # macOS / Linux
```

Python 3.12+ is required.

## Configure

```bash
cp .env.example .env
# edit .env, paste your ANTHROPIC_API_KEY
```

The `.env` file is git-ignored. You can also export `ANTHROPIC_API_KEY`
in the shell. If neither is set, only `--dry-run` mode works.

Optional overrides (env vars, also documented in `.env.example`):

| Var | Purpose |
|---|---|
| `SIGIL_MCP_BINARY` | Override the path to the `sigil-mcp` binary. Defaults to `target/release/sigil-mcp[.exe]`, falls back to `target/debug`. |
| `BENCH_MODEL` | Anthropic model. Defaults to `claude-sonnet-4-6`. |
| `BENCH_MAX_ATTEMPTS` | Per-task attempt cap. Defaults to `5`. |
| `BENCH_FUEL_BUDGET` | Fuel budget passed to `sigil_forge`. Defaults to `100_000`. |

## Smoke test (no API spend)

```bash
.venv/Scripts/python -m sigil_bench run --dry-run
```

This runs every configured task with the `OracleStub` generator, which returns
the canonical reference source verbatim. It verifies the harness pipeline
end-to-end without any LLM calls; every listed task must pass.

## Single-task live run (~$0.05–$0.20)

```bash
.venv/Scripts/python -m sigil_bench run --task task001_echo
```

Prints the cost estimate first, asks for confirmation (skip with `--yes`),
then runs the loop and writes the results.

## Full bench (~$0.50–$2)

```bash
.venv/Scripts/python -m sigil_bench run            # interactive confirmation
.venv/Scripts/python -m sigil_bench run --yes      # skip confirmation
```

The harness prints a worst-case cost estimate before any spending. Real
cost is typically lower because passing tasks exit early.

Outputs land in `bench/runs/<UTC-timestamp>/`:

```
bench/runs/20260507T120000Z/
├── results.json           # full RunReport, every TaskResult inline
├── report.md              # human-readable narrative + failure-code histogram
└── transcripts/
    ├── task001_echo.jsonl       # one JSON object per attempt + summary
    ├── task011_palindrome.jsonl
    └── ...
```

## Resume

If a run is interrupted (Ctrl-C, network blip, etc.), resume by passing
the run-dir name:

```bash
.venv/Scripts/python -m sigil_bench run --resume 20260507T120000Z
```

Tasks whose transcripts already exist in that dir are skipped. The
report covers only the tasks executed during the resume invocation.

## Tasks

The 5 initial tasks span the difficulty range:

| ID | Difficulty | What it tests |
|---|---|---|
| `task001_echo` | trivial | Packed-pointer ABI literacy. Pure passthrough. |
| `task011_palindrome` | basic | Two-pointer scan, branching, multi-byte string return. |
| `task020_rot13` | intermediate | Nested byte-range conditionals, helper fns, full alloc/load/store loop. |
| `task028_count_lines` | ffi_fs | `extern "C" fn fs_read`, `FsIO` grant, decimal rendering, `@Internal` taint. |
| `task151_http_size` | ffi_net | `extern "C" fn http_get`, `NetIO` grant, host-pattern grant matching. |

Each spec is a YAML file in [`tasks/`](tasks/) — see comments in
[task028_count_lines.yaml](tasks/task028_count_lines.yaml) for grant
syntax and the resolution rules.

## Architecture

```
bench/src/sigil_bench/
├── cli.py            argparse entry; orchestrates a run end-to-end
├── config.py         Settings dataclass; .env / env-var loading
├── tasks.py          TaskSpec pydantic model + YAML loader
├── mcp_client.py     SigilMCP: subprocess + JSON-RPC over stdio
├── generator.py      Generator protocol + OracleStub/BrokenStub/RecoverStub + AnthropicGenerator
├── runner.py         run_task: generate → check → iterate → forge → score
├── scoring.py        RunReport aggregate + console/JSON/markdown writers + cost estimator
└── prompts/
    ├── system.md     Role + output contract (cache block 1)
    └── recipes.md    Tool-writing recipes (cache block 2 prefix)
```

The Anthropic system prompt is three cache-controlled blocks:
1. `system.md` (role + output contract)
2. `recipes.md` + `lang-ref.md` (tool patterns + language reference)
3. `docs/ERROR-CODES.md` (~700 lines, ~15k tokens — one-time cache write)

Cache TTL is 5 minutes; a typical full bench completes in 80–130s, well
within the window.

## Tests

```bash
.venv/Scripts/python -m pytest tests/ -v
```

Three suites, all CI-runnable without an API key:

* `test_mcp_client.py` — spawns the real `sigil-mcp` binary, exercises
  every method, asserts envelope shape.
* `test_tasks.py` — loads every YAML spec, validates pydantic, confirms
  reference sources resolve.
* `test_runner_stub.py` — drives the full agent loop with stub
  generators against a synthetic mini-task. Verifies pass-in-1, exhaust
  with code histogram, recover-in-2, ground-truth-mismatch reason, and
  harness-error catch.

## Interpreting results

The point of this benchmark is **not** to publish a single "Claude is X%
good at Sigil" number. It's to drive iteration on the diagnostic
registry. The two artifacts to read after a run:

1. **`report.md` → top failure codes**. Codes that appear repeatedly
   across attempts indicate hints the model couldn't act on. That's a
   signal to revisit [`crates/sigil-compiler/src/diagnostics/registry.rs`](../crates/sigil-compiler/src/diagnostics/registry.rs)
   and rewrite the offending hint with more concrete fix recipes.
2. **`transcripts/*.jsonl` → individual attempts**. For any task that
   failed unexpectedly, read the per-attempt source + diagnostics
   sequence to spot where the model got stuck. A common pattern is two
   diagnostics fighting each other (fixing one re-introduces the other);
   this usually means a missing precondition in the hint.

After registry changes, re-run the bench to confirm the failure rate
moved in the right direction.

## Standalone scripts

* [`scripts/z3_cache_bench.py`](scripts/z3_cache_bench.py) — Z3 cache
  effectiveness merge gate (axis-2 eighth touch). Measures cold vs.
  warm wall-clock per fixture in `crates/sigil-compiler/tests/fixtures/`
  and `tests/z3_corpus/`; gates on geomean speedup ≥ 2× across ≥ 10
  surviving fixtures. Run after
  `cargo build --release --bin sigil`.
