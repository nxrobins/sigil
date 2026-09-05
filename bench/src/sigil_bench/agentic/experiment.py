"""Experiment orchestration: models × tasks × runs → metrics + report.

`run_experiment` iterates the roster over the task corpus, drives each cell
through `run_cell`, streams a summary row per cell to `results.jsonl`, dumps a
full transcript per cell, and writes `summary.json` + `report.md` at the end.
"""

from __future__ import annotations

import hashlib
import json
import re
import time
from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from sigil_bench.mcp_client import SigilMCP
from sigil_bench.runner import capture_ground_truth
from sigil_bench.tasks import TaskSpec, load_tasks

from . import registry
from .backends import Backend, ScriptedBackend, close_backend, make_dryrun_turns
from .loop import CellResult, run_cell
from .prompt import SYSTEM_PROMPT_TEMPLATE


@dataclass
class ExperimentConfig:
    repo_root: Path
    mcp_binary: Path
    tasks_dir: Path
    out_dir: Path
    models: list[str]
    task_ids: list[str] | None = None
    runs: int = 1
    max_check_attempts: int = 6
    max_model_turns: int = 16
    max_total_tool_calls: int = 40
    fuel: int = 100_000
    compose_stdlib: bool = True
    verify_final: bool = True
    check_capability_use: bool = False
    dry_run: bool = False
    request_timeout: float = 120.0
    anthropic_thinking: bool = False  # enable Anthropic adaptive thinking
    anthropic_effort: str = "high"  # effort level when thinking is on
    env_file_loaded: str | None = None


def _make_mcp_factory(binary: Path) -> Callable[[], SigilMCP]:
    def factory() -> SigilMCP:
        mcp = SigilMCP.spawn(binary)
        mcp.initialize()
        return mcp
    return factory


def _prompt_hash() -> str:
    return hashlib.sha256(SYSTEM_PROMPT_TEMPLATE.encode("utf-8")).hexdigest()[:16]


def run_experiment(cfg: ExperimentConfig, *, log: Callable[[str], None] = print) -> Path:
    tasks = load_tasks(cfg.tasks_dir, only=cfg.task_ids)
    if not tasks:
        raise ValueError("no tasks selected")

    # Resolve roster; in real mode skip models whose provider has no key.
    resolved: list[registry.ModelSpec] = []
    skipped: list[dict[str, str]] = []
    for name in cfg.models:
        spec = registry.resolve_model(name)
        if not cfg.dry_run and not registry.is_available(spec):
            skipped.append({"model": name, "reason": f"{spec.provider_info.key_env} not set"})
            log(f"[skip] {name}: {spec.provider_info.key_env} not set")
            continue
        resolved.append(spec)
    if not resolved:
        raise RuntimeError(
            "no runnable models. " + (
                "Set provider keys in the env file." if not cfg.dry_run else "dry-run resolved nothing."
            )
        )

    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    run_dir = cfg.out_dir / f"{ts}-agentic"
    transcripts_dir = run_dir / "transcripts"
    transcripts_dir.mkdir(parents=True, exist_ok=True)

    run_config = {
        "timestamp_utc": ts,
        "mode": "dry_run" if cfg.dry_run else "live",
        "models": [s.key for s in resolved],
        "models_skipped": skipped,
        "task_ids": [t.id for t in tasks],
        "runs": cfg.runs,
        "max_check_attempts": cfg.max_check_attempts,
        "max_model_turns": cfg.max_model_turns,
        "max_total_tool_calls": cfg.max_total_tool_calls,
        "fuel": cfg.fuel,
        "compose_stdlib": cfg.compose_stdlib,
        "verify_final": cfg.verify_final,
        "anthropic_thinking": cfg.anthropic_thinking,
        "anthropic_effort": cfg.anthropic_effort if cfg.anthropic_thinking else None,
        "check_capability_use": cfg.check_capability_use,
        "mcp_binary": str(cfg.mcp_binary),
        "env_file_loaded": cfg.env_file_loaded,
        "system_prompt_sha256_16": _prompt_hash(),
    }
    (run_dir / "run_config.json").write_text(json.dumps(run_config, indent=2), encoding="utf-8")

    mcp_factory = _make_mcp_factory(cfg.mcp_binary)

    # Ground truth is deterministic per task — capture it ONCE here (a single
    # reference forge per input) instead of once per cell inside every
    # verify_final_source call. Net-grant tasks thus hit the network once per
    # task, not once per (model×run).
    gt_cache: dict[str, dict[str, str] | None] = {}
    if cfg.verify_final:
        try:
            with mcp_factory() as gt_mcp:
                for task in tasks:
                    try:
                        gt_cache[task.id] = capture_ground_truth(task, cfg.repo_root, gt_mcp)
                    except Exception as e:  # noqa: BLE001 — per-cell verify will fall back
                        gt_cache[task.id] = None
                        log(f"[gt] {task.id}: ground-truth capture failed ({e}); will retry per cell")
        except Exception as e:  # noqa: BLE001
            log(f"[gt] ground-truth precompute unavailable ({e}); verifying per cell")

    results: list[CellResult] = []
    results_fp = (run_dir / "results.jsonl").open("w", encoding="utf-8")

    total_cells = len(resolved) * len(tasks) * cfg.runs
    cell_no = 0
    try:
        for spec in resolved:
            # Real backends are stateless across cells → build once per model.
            shared_backend: Backend | None = None
            if not cfg.dry_run:
                shared_backend = registry.build_backend(
                    spec, request_timeout=cfg.request_timeout,
                    thinking=cfg.anthropic_thinking, effort=cfg.anthropic_effort,
                )

            for task in tasks:
                for run_index in range(cfg.runs):
                    cell_no += 1
                    backend = _backend_for_cell(cfg, spec, task, shared_backend)
                    log(f"[{cell_no}/{total_cells}] {spec.key} | {task.id} | run {run_index}")
                    result = run_cell(
                        model_key=spec.key,
                        display_name=spec.display_name,
                        provider=spec.provider,
                        backend=backend,
                        task=task,
                        mcp_factory=mcp_factory,
                        repo_root=cfg.repo_root,
                        max_check_attempts=cfg.max_check_attempts,
                        max_model_turns=cfg.max_model_turns,
                        max_total_tool_calls=cfg.max_total_tool_calls,
                        fuel=cfg.fuel,
                        compose_stdlib=cfg.compose_stdlib,
                        verify_final=cfg.verify_final,
                        check_capability_use=cfg.check_capability_use,
                        expected_outputs=gt_cache.get(task.id),
                        run_index=run_index,
                    )
                    results_fp.write(json.dumps(result.to_row()) + "\n")
                    results_fp.flush()
                    _dump_transcript(transcripts_dir, result)
                    # Free the heavy fields now that they're on disk — the
                    # retained list only feeds scalar aggregation in summarize().
                    result.transcript = []
                    result.tool_log = []
                    results.append(result)
                    log(
                        f"    -> {result.final_outcome} "
                        f"(first_pass={result.first_pass_success}, "
                        f"attempts={result.attempts_to_success}, "
                        f"checks={result.check_attempts}, "
                        f"correct={result.final_source_correct})"
                    )
            if shared_backend is not None:
                close_backend(shared_backend)  # release the model's HTTP client
    finally:
        results_fp.close()

    summary = summarize(results)
    (run_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    (run_dir / "report.md").write_text(render_report(run_config, summary), encoding="utf-8")
    log(f"\nDone. {len(results)} cells -> {run_dir}")
    return run_dir


def _backend_for_cell(
    cfg: ExperimentConfig, spec: registry.ModelSpec, task: TaskSpec, shared: Backend | None
) -> Backend:
    if not cfg.dry_run:
        assert shared is not None
        return shared
    # Dry-run: a fresh scripted backend per cell, using the task's reference
    # source as the "good" attempt so the cell converges deterministically.
    ref_source = task.resolve_source(cfg.repo_root).read_text(encoding="utf-8")
    grants = task.required_grants.to_mcp() or None
    return ScriptedBackend(make_dryrun_turns(ref_source, grants=grants), name=f"dryrun:{spec.key}")


def _dump_transcript(transcripts_dir: Path, result: CellResult) -> None:
    # Passthrough model keys (e.g. "or:openai/gpt-4o") contain ':' and '/',
    # which are illegal in filesystem paths (esp. on Windows). Sanitize for the
    # directory name; the JSON `meta.model_key` still carries the real key.
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", result.model_key)
    model_dir = transcripts_dir / safe
    model_dir.mkdir(parents=True, exist_ok=True)
    path = model_dir / f"{result.task_id}__r{result.run_index}.json"
    payload = {
        "meta": result.to_row(),
        "transcript": result.transcript,
        "tool_log": result.tool_log,
    }
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


# ── Aggregation ──────────────────────────────────────────────────────────────


def _rate(num: int, den: int) -> float:
    return round(num / den, 4) if den else 0.0


def summarize(results: list[CellResult]) -> dict[str, Any]:
    by_model: dict[str, list[CellResult]] = {}
    for r in results:
        by_model.setdefault(r.model_key, []).append(r)

    def model_block(cells: list[CellResult]) -> dict[str, Any]:
        n = len(cells)
        # De-error: harness_error cells are infrastructure failures (API outage,
        # credit exhaustion), NOT model failures — exclude them from the success
        # denominator. (Counting 13 credit-outage cells as failures is what faked
        # "Opus 62%" in run-004.) Success/first-pass rates use the clean denom;
        # the raw incl-errors rate is kept for transparency.
        errors = [c for c in cells if c.final_outcome == "harness_error"]
        clean = [c for c in cells if c.final_outcome != "harness_error"]
        nclean = len(clean)
        successes = [c for c in cells if c.final_outcome == "success"]
        attempts = [c.attempts_to_success for c in successes if c.attempts_to_success is not None]
        verified = [c for c in cells if c.final_source_correct is not None]
        correct = [c for c in verified if c.final_source_correct]
        suspected = [c for c in cells if c.suspected_cheat]
        served: Counter[str] = Counter()
        for c in cells:
            served.update(c.served_models)
        outcome_counts = Counter(c.final_outcome for c in cells)
        code_freq: Counter[str] = Counter()
        for c in cells:
            code_freq.update(c.diagnostic_codes)
        grant_kinds: Counter[str] = Counter()
        for c in cells:
            for g in c.grants_requested:
                grant_kinds.update(k for k, v in g.items() if v)
        tok_in = sum(c.usage.get("input_tokens", 0) for c in cells)
        tok_out = sum(c.usage.get("output_tokens", 0) for c in cells)
        return {
            "display_name": cells[0].display_name,
            "provider": cells[0].provider,
            "cells": n,
            "harness_error_cells": len(errors),
            "first_pass_success_rate": _rate(sum(c.first_pass_success for c in clean), nclean),
            "success_rate": _rate(len(successes), nclean),
            "success_rate_incl_errors": _rate(len(successes), n),
            "final_correct_rate": _rate(len(correct), len(verified)) if verified else None,
            "served_models": dict(served),
            "suspected_cheat_count": len(suspected),
            "mean_attempts_to_success": round(sum(attempts) / len(attempts), 2) if attempts else None,
            "mean_check_attempts": round(sum(c.check_attempts for c in cells) / n, 2),
            "outcome_counts": dict(outcome_counts),
            "diagnostic_code_frequency": dict(code_freq.most_common()),
            "grant_kinds_requested": dict(grant_kinds),
            "tokens": {"input": tok_in, "output": tok_out},
            "mean_wall_seconds": round(sum(c.wall_seconds for c in cells) / n, 2),
        }

    overall_codes: Counter[str] = Counter()
    for r in results:
        overall_codes.update(r.diagnostic_codes)

    return {
        "n_cells": len(results),
        "by_model": {m: model_block(cells) for m, cells in by_model.items()},
        "overall_diagnostic_code_frequency": dict(overall_codes.most_common()),
    }


def render_report(run_config: dict[str, Any], summary: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# SIGIL agentic convergence — run report")
    lines.append("")
    lines.append(f"- Mode: **{run_config['mode']}**")
    lines.append(f"- Timestamp (UTC): {run_config['timestamp_utc']}")
    lines.append(f"- Tasks: {', '.join(run_config['task_ids'])}")
    lines.append(f"- Runs per cell: {run_config['runs']}")
    lines.append(f"- Retry cap (max `sigil_check` attempts): {run_config['max_check_attempts']}")
    lines.append(f"- System-prompt sha256[:16]: `{run_config['system_prompt_sha256_16']}`")
    lines.append(f"- Cells: {summary['n_cells']}")
    if run_config.get("models_skipped"):
        sk = ", ".join(f"{s['model']} ({s['reason']})" for s in run_config["models_skipped"])
        lines.append(f"- Skipped (no key): {sk}")
    lines.append("")
    lines.append("## Per-model")
    lines.append("")
    lines.append(
        "| Model | Cells | 1st-pass | Success | Correct | Mean attempts | Mean checks | hit_cap | gave_up |"
    )
    lines.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for key, b in sorted(summary["by_model"].items()):
        oc = b["outcome_counts"]
        correct = "—" if b["final_correct_rate"] is None else f"{b['final_correct_rate']:.0%}"
        attempts = "—" if b["mean_attempts_to_success"] is None else b["mean_attempts_to_success"]
        lines.append(
            f"| {key} | {b['cells']} | {b['first_pass_success_rate']:.0%} | "
            f"{b['success_rate']:.0%} | {correct} | {attempts} | {b['mean_check_attempts']} | "
            f"{oc.get('hit_cap', 0)} | {oc.get('gave_up', 0)} |"
        )
    lines.append("")
    lines.append("## Most-encountered diagnostic codes (all cells)")
    lines.append("")
    freq = summary["overall_diagnostic_code_frequency"]
    if not freq:
        lines.append("_None — every first attempt compiled clean._")
    else:
        for code, count in list(freq.items())[:25]:
            lines.append(f"- `{code}`: {count}")
    lines.append("")
    return "\n".join(lines)
