"""The agentic tool-use loop + per-cell convergence metrics.

`run_cell` drives ONE (model × task × run) cell: it renders the system prompt,
spawns a fresh `sigil-mcp`, and lets the model call `sigil_check` /
`sigil_forge` / `sigil_lookup_error` in a loop until it ends its turn, hits the
retry cap, or exhausts the turn/tool budget. It records the metrics the
experiment cares about and the full neutral transcript.
"""

from __future__ import annotations

import dataclasses
import time
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from sigil_bench.mcp_client import SigilMCP
from sigil_bench.tasks import TaskSpec

from .backends import Backend
from .prompt import KICKOFF_USER_MESSAGE, render_system_prompt
from .tooling import MCPToolExecutor, model_tool_specs


@dataclass
class CellResult:
    model_key: str
    display_name: str
    provider: str
    task_id: str
    run_index: int

    # ── the metrics the experiment records ──
    first_pass_success: bool
    attempts_to_success: int | None
    check_attempts: int
    final_outcome: str  # success | gave_up | hit_cap | exhausted_turns | harness_error
    diagnostic_codes: dict[str, int]
    distinct_codes: list[str]
    grants_requested: list[dict[str, Any]]
    final_source_correct: bool | None
    # Cheat detector (opt-in): a correct, grant-requiring source whose output is
    # unchanged with the grant revoked → the capability was never used.
    capability_unused: bool | None = None
    suspected_cheat: bool = False

    # ── supporting detail ──
    # Distinct models the provider reported serving this cell (`response.model`).
    # Provenance audit: should be exactly the requested model.
    served_models: list[str] = field(default_factory=list)
    forge_calls: int = 0
    forge_fuel_consumed: int = 0
    lookup_error_calls: int = 0
    model_turns: int = 0
    total_tool_calls: int = 0
    usage: dict[str, int] = field(default_factory=dict)
    wall_seconds: float = 0.0
    error: str | None = None
    stop_reason: str | None = None
    final_source: str | None = None
    final_verify: dict[str, Any] = field(default_factory=dict)

    # ── heavy fields excluded from the summary row ──
    transcript: list[dict[str, Any]] = field(default_factory=list, repr=False)
    tool_log: list[dict[str, Any]] = field(default_factory=list, repr=False)

    def to_row(self) -> dict[str, Any]:
        """Flat summary row (no transcript) for results.jsonl / CSV."""
        d = dataclasses.asdict(self)
        d.pop("transcript", None)
        d.pop("tool_log", None)
        return d


def run_cell(
    *,
    model_key: str,
    display_name: str,
    provider: str,
    backend: Backend,
    task: TaskSpec,
    mcp_factory: Callable[[], SigilMCP],
    repo_root: Path,
    max_check_attempts: int = 6,
    max_model_turns: int = 16,
    max_total_tool_calls: int = 40,
    fuel: int = 100_000,
    compose_stdlib: bool = True,
    verify_final: bool = True,
    check_capability_use: bool = False,
    expected_outputs: dict[str, str] | None = None,
    system_prompt: str | None = None,
    run_index: int = 0,
) -> CellResult:
    """Run one agentic cell end-to-end. Never raises — failures land in the
    `error` field with `final_outcome="harness_error"`.

    `system_prompt` overrides the rendered prompt (used by the red-team driver
    to swap in an adversarial, cheat-seeking prompt)."""
    start = time.perf_counter()
    system = system_prompt if system_prompt is not None else render_system_prompt(task)
    tools = model_tool_specs()
    messages: list[dict[str, Any]] = [{"role": "user", "text": KICKOFF_USER_MESSAGE}]
    usage_in = usage_out = 0
    turns = 0
    total_tool_calls = 0
    served: dict[str, None] = {}  # ordered set of distinct served models
    stop_reason: str | None = None
    error: str | None = None
    executor: MCPToolExecutor | None = None
    verify: dict[str, Any] = {}

    try:
        with mcp_factory() as mcp:
            executor = MCPToolExecutor(
                mcp, task, repo_root,
                max_check_attempts=max_check_attempts, fuel=fuel,
                compose_stdlib=compose_stdlib, expected_outputs=expected_outputs,
            )
            for _turn in range(max_model_turns):
                turns += 1
                at = backend.converse(system, tools, messages)
                usage_in += int(at.usage.get("input_tokens", 0))
                usage_out += int(at.usage.get("output_tokens", 0))
                if at.served_model:
                    served[at.served_model] = None
                messages.append({
                    "role": "assistant",
                    "text": at.text,
                    "tool_calls": [tc.as_dict() for tc in at.tool_calls],
                    "stop_reason": at.stop_reason,
                    "served_model": at.served_model,
                    # Verbatim content blocks for replay (Anthropic thinking);
                    # None for backends that reconstruct from text+tool_calls.
                    "_raw": at.raw_content,
                })
                if not at.tool_calls:
                    stop_reason = "model_end_turn"
                    break
                results: list[dict[str, Any]] = []
                stop = False
                for tc in at.tool_calls:
                    out, ctrl = executor.execute(tc.name, tc.arguments)
                    total_tool_calls += 1
                    results.append({"id": tc.id, "name": tc.name, "output": out})
                    if ctrl.stop:
                        stop = True
                        stop_reason = ctrl.reason
                    if total_tool_calls >= max_total_tool_calls:
                        stop = True
                        stop_reason = stop_reason or "max_tool_calls"
                    # Stop the moment a call trips the cap — do NOT execute the
                    # remaining calls in this batch (they would burn compile/run
                    # cost the model is no longer entitled to, and we break the
                    # outer loop next so they'd never be seen anyway).
                    if stop:
                        break
                messages.append({"role": "tool", "results": results})
                if stop:
                    break
            else:
                stop_reason = stop_reason or "max_model_turns"

            if verify_final:
                verify = executor.verify_final_source(check_capability_use=check_capability_use)
    except Exception as e:  # noqa: BLE001 — top-level cell boundary
        error = f"{type(e).__name__}: {e}"

    # ── derive outcome + metrics ──
    ex = executor
    any_passed = bool(ex and ex.any_check_passed)
    hit_cap = bool(ex and ex.hit_cap)
    if error is not None:
        outcome = "harness_error"
    elif any_passed:
        outcome = "success"
    elif hit_cap:
        outcome = "hit_cap"
    elif stop_reason == "model_end_turn":
        outcome = "gave_up"
    elif stop_reason in ("max_model_turns", "max_tool_calls"):
        outcome = "exhausted_turns"
    else:
        outcome = "gave_up"

    final_correct: bool | None = None
    if verify.get("ran"):
        final_correct = bool(verify.get("all_passed"))
    capability_unused = verify.get("capability_unused")
    suspected_cheat = bool(final_correct and capability_unused)

    return CellResult(
        model_key=model_key,
        display_name=display_name,
        provider=provider,
        task_id=task.id,
        run_index=run_index,
        first_pass_success=bool(ex and ex.first_check_ok),
        attempts_to_success=(ex.attempts_to_success if ex else None),
        check_attempts=(ex.check_attempts if ex else 0),
        final_outcome=outcome,
        diagnostic_codes=(dict(ex.code_counts) if ex else {}),
        distinct_codes=(sorted(ex.code_counts) if ex else []),
        grants_requested=(list(ex.grants_requested) if ex else []),
        final_source_correct=final_correct,
        capability_unused=capability_unused,
        suspected_cheat=suspected_cheat,
        served_models=list(served),
        forge_calls=(ex.forge_calls if ex else 0),
        forge_fuel_consumed=(ex.forge_fuel_consumed if ex else 0),
        lookup_error_calls=(ex.lookup_calls if ex else 0),
        model_turns=turns,
        total_tool_calls=total_tool_calls,
        usage={"input_tokens": usage_in, "output_tokens": usage_out},
        wall_seconds=round(time.perf_counter() - start, 3),
        error=error,
        stop_reason=stop_reason,
        final_source=(ex.last_passing_source if ex else None),
        final_verify=verify,
        transcript=messages,
        tool_log=[dataclasses.asdict(r) for r in (ex.tool_log if ex else [])],
    )
