"""Agentic convergence harness for sigil-bench.

Unlike the top-level `sigil_bench.runner` (which is *harness-driven*: the
harness itself calls `sigil_check` and feeds diagnostics back into the next
prompt), this sub-package runs the **agentic / tool-use** experiment described
by the "SIGIL Tool Generation" system prompt: the *model itself* calls
`sigil_check` / `sigil_forge` / `sigil_lookup_error` as tools in a loop, reads
the diagnostics, and iterates until it is satisfied (or hits the retry cap).

The harness wires the three SIGIL tools to the model's native function-calling
API (Anthropic tools or OpenAI-compatible tools), executes each tool call
against the real `sigil-mcp` binary, and records per-cell convergence metrics:

  * first-pass success (did the FIRST `sigil_check` pass?)
  * attempts-to-success (which `sigil_check` call first passed?)
  * every diagnostic code encountered, with frequencies
  * final outcome (success / gave_up / hit_cap / exhausted_turns / harness_error)
  * grants requested (what the model passed to `sigil_forge`)

See `docs/agentic-convergence-harness.md` for the design.
"""

from __future__ import annotations

__all__ = [
    "CellResult",
    "run_cell",
    "run_experiment",
]

from .experiment import run_experiment
from .loop import CellResult, run_cell
