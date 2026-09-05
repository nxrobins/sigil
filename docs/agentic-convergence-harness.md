# Agentic convergence harness (`sigil_bench.agentic`)

A harness that runs the **"SIGIL Tool Generation"** system prompt over the task
corpus across many models, lets each model drive the `sigil_check` /
`sigil_forge` / `sigil_lookup_error` tools itself, and records how well each
model *converges* on a working tool.

## How it differs from `sigil_bench.runner`

| | `sigil_bench.runner` (existing) | `sigil_bench.agentic` (this) |
|---|---|---|
| Who calls `sigil_check`? | the **harness** | the **model** (tool use) |
| Loop driver | harness re-prompts with diagnostics | model reads diagnostics, retries on its own |
| System prompt | `prompts/system.md` + recipes + stdlib bundle | the verbatim "SIGIL Tool Generation" prompt |
| Models | Anthropic only | any provider (Anthropic + OpenAI-compatible) |
| Question answered | "can a model regenerate a tool given diagnostics?" | "can a model *drive the tools itself* to convergence?" |

The agentic loop is the faithful realization of the prompt, which instructs the
model: *"Call `sigil_check` with your source … read the diagnostics … fix and
retry … then call `sigil_forge`."*

## Architecture

```
cli.py            argument parsing, key loading, roster resolution
  └─ experiment.py   models × tasks × runs; streams results; writes report
       └─ loop.py        run_cell(): the agentic turn loop + CellResult metrics
            ├─ prompt.py      verbatim system prompt + per-task description block
            ├─ backends.py    Anthropic / OpenAI-compatible tool-use + scripted stub
            ├─ registry.py    model registry, .env key loading, backend construction
            └─ tooling.py     the 3 tool schemas + MCPToolExecutor (runs vs sigil-mcp)
```

Each cell spawns a **fresh `sigil-mcp` process** (reusing the existing
`sigil_bench.mcp_client.SigilMCP`). The model's tool calls are executed against
it; for tasks that declare `stdlib_imports`, the stdlib modules are linked in
with `compose_with_stdlib` before the source reaches the compiler — the same
path the on-disk reference takes.

## Providers

Keys are loaded from a `.env` (default: the repo-root `.env`)
without overriding the process environment. Two backend shapes cover every
provider:

- **Anthropic** native tools — `claude-*`
- **OpenAI-compatible** `tools` — OpenAI, OpenRouter, Nebius, xAI, Azure AI
  Foundry, Mistral, Moonshot

Name a registry key (`claude-sonnet`) or use a passthrough
(`or:deepseek/deepseek-chat`, `nebius:Qwen/Qwen2.5-72B`). `--list-models` prints
the registry with per-provider availability.

## Recorded metrics (per cell, in `results.jsonl`)

- **`first_pass_success`** — did the *first* `sigil_check` call pass?
- **`attempts_to_success`** — which `sigil_check` call first passed (`null` if never)
- **`check_attempts`** — number of `sigil_check` calls
- **`diagnostic_codes`** / **`distinct_codes`** — every code seen, with frequency
- **`final_outcome`** — `success` · `gave_up` · `hit_cap` · `exhausted_turns` · `harness_error`
- **`grants_requested`** — the `grants` objects the model passed to `sigil_forge`
- **`final_source_correct`** — authoritative verdict: the last source that passed
  `sigil_check`, run by the *harness* through `sigil_forge` over every task input
  (with the task's real grants) and compared to ground truth. Independent of
  whatever the model forged for itself.
- supporting: `forge_calls`, `forge_fuel_consumed`, `lookup_error_calls`,
  `model_turns`, `total_tool_calls`, token `usage`, `wall_seconds`, `stop_reason`.

Ground truth is captured **once per task** (a single reference forge per input)
and reused across every cell, so net-grant tasks hit the network once per task
rather than once per (model × run). Full transcripts live in the per-cell JSON
files; they are dropped from the in-memory result set after dumping, so a large
run's memory stays flat.

`summary.json` aggregates per model (first-pass rate, success rate, correct
rate, mean attempts-to-success, outcome counts, code frequency, grant kinds,
tokens). `report.md` is the human-readable table. Each cell's full transcript +
ordered tool log is dumped to `transcripts/<model>/<task>__r<i>.json`.

## Outcome semantics

| outcome | meaning |
|---|---|
| `success` | some `sigil_check` call passed (the model converged on a compiling tool) |
| `hit_cap` | `--max-attempts` failing `sigil_check` calls with no pass — gave up by cap |
| `gave_up` | model ended its turn (no tool call) without ever passing `sigil_check` |
| `exhausted_turns` | hit `--max-model-turns` / `--max-tool-calls` safety bound |
| `harness_error` | an exception in the cell (MCP/provider error); see `error` |

`success` is about *compiling clean* (the prompt's convergence target);
`final_source_correct` separately reports whether the converged tool is
behaviourally right. The grants are **not** given to the model — inferring the
right capabilities from the task is part of what `grants_requested` measures.

## Usage

```bash
# Offline smoke test (no API, no cost) — scripted stub exercises the loop.
python bench/run_agentic_experiment.py --dry-run --tasks task001_echo

# Live: default Claude+GPT roster over every task, retry cap 6.
python bench/run_agentic_experiment.py --models default --runs 1 --max-attempts 6

# Explicit models + tasks; cross-provider via OpenRouter passthrough.
python bench/run_agentic_experiment.py \
    --models claude-sonnet,gpt-4o,or:deepseek/deepseek-chat \
    --tasks task001_echo,task011_palindrome,task020_rot13

python bench/run_agentic_experiment.py --list-models   # registry + availability
```

Requires the `sigil-mcp` binary (`cargo build --release -p sigil-mcp`) and, for
non-Anthropic providers, the `openai` SDK (`pip install -e "bench[agentic]"`).

## Tests

`bench/tests/test_agentic_harness.py` — prompt rendering, registry resolution,
backend message conversion (fake clients), bad-tool-JSON tolerance, summary
aggregation, plus integration tests that drive `run_cell` through the **real**
`sigil-mcp` binary (broken→good convergence, first-pass success, hit-cap,
dry-run script). Skipped automatically if the binary isn't built.
