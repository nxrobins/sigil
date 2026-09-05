#!/usr/bin/env python3
"""Run the cross-language Python BASELINE for the agent-convergence table.

Same 24 tasks, same models, same convergence loop as the SIGIL agentic harness
(`sigil_bench.agentic`), but the target language is plain Python. See
`sigil_bench.agentic.baseline_py` for the framing and what it measures.

Ground truth is captured once from the authoritative SIGIL reference forge so
both harnesses grade against byte-identical outputs.

Usage:
  python bench/scripts/run_baseline.py --models gpt-5.5-azure claude-sonnet \\
      --runs 1 --out bench/runs
  python bench/scripts/run_baseline.py --dump-prompts   # print the 24 briefs, no API calls
"""
from __future__ import annotations

import argparse
import dataclasses
import json
import time
from collections import Counter
from pathlib import Path

from sigil_bench.agentic import registry
from sigil_bench.agentic.backends import close_backend
from sigil_bench.agentic.baseline_py import (
    KICKOFF_USER_MESSAGE,
    PyToolExecutor,
    functional_brief,
    input_kind,
    model_tool_specs,
    render_system_prompt,
)
from sigil_bench.mcp_client import SigilMCP
from sigil_bench.runner import capture_ground_truth
from sigil_bench.tasks import load_tasks

REPO_ROOT = Path(__file__).resolve().parents[2]

# The 24-task slice used by run-004 (same set the SIGIL table reports).
TASK_IDS = [
    "task001_echo", "task002_reverse", "task004_uppercase", "task011_palindrome",
    "task015_ascii_sum", "task020_rot13", "task021_fibonacci", "task023_dec_to_hex",
    "task026_read_file", "task028_count_lines", "task029_count_lines_via_stdlib",
    "task032_sha256_hex", "task045_http_size_via_stdlib", "task061_json_field",
    "task085_eval_add_sub", "task101_secret_length", "task103_secret_mask",
    "task105_secret_xor_hex", "task121_secret_rot13", "task127_fs_sort_lines",
    "task129_fs_grep_error", "task151_http_size", "task152_http_lines", "task154_http_wc",
]


def dump_prompts(tasks_dir: Path) -> None:
    tasks = load_tasks(tasks_dir, only=TASK_IDS)
    for t in tasks:
        print(f"### {t.id}  [{input_kind(t)}]  grants={t.required_grants.to_mcp() or '{}'}")
        print(functional_brief(t))
        print(f"  inputs: {[(i.name, i.value) for i in t.inputs]}")
        print()


def _rate(num: int, den: int) -> float:
    return round(num / den, 4) if den else 0.0


def regrade(run_dir: Path, mcp_binary: Path) -> None:
    """Rebuild summary.json for a completed run by re-running each cell's stored
    final_source against a freshly captured ground truth, under the current
    (newline-tolerant) grader. No API calls — reuses stored sources."""
    from sigil_bench.agentic.baseline_py import PyToolExecutor

    tasks = {t.id: t for t in load_tasks(REPO_ROOT / "bench" / "tasks", only=TASK_IDS)}

    def mcp_factory() -> SigilMCP:
        m = SigilMCP.spawn(mcp_binary)
        m.initialize()
        return m

    gt: dict[str, dict[str, str] | None] = {}
    with mcp_factory() as mcp:
        for tid, t in tasks.items():
            gt[tid] = capture_ground_truth(t, REPO_ROOT, mcp)

    rows: list[dict] = []
    for tf in sorted((run_dir / "transcripts").glob("*/*.json")):
        cell = json.loads(tf.read_text(encoding="utf-8"))
        m = cell["meta"]
        src = m.get("final_source")
        if src is not None:
            ex = PyToolExecutor(tasks[m["task_id"]], REPO_ROOT, max_check_attempts=5,
                                expected_outputs=gt.get(m["task_id"]))
            ex.last_passing_source = src
            v = ex.verify_final_source()
            m["final_verify"] = v
            m["final_source_correct"] = bool(v.get("all_passed")) if v.get("ran") else None
            m["final_source_correct_exact"] = bool(v.get("all_passed_exact")) if v.get("ran") else None
            cell["meta"] = m
            tf.write_text(json.dumps(cell, indent=2), encoding="utf-8")
        rows.append(m)

    # rewrite results.jsonl too, so it matches the regraded transcripts
    with (run_dir / "results.jsonl").open("w", encoding="utf-8") as fp:
        for r in rows:
            fp.write(json.dumps(r) + "\n")
    summary = summarize(rows)
    (run_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"regraded {len(rows)} cells -> {run_dir}")
    for key, b in summary["by_model"].items():
        ex = b.get("exact_correct_count")
        print(f"  {key:26s} compile {b['success_rate']:.0%}  "
              f"correct {b['final_correct_count']}/{b['verified_count']} "
              f"({b['final_correct_rate']:.0%})  exact {ex}/{b['verified_count']}")


def run(args: argparse.Namespace) -> None:
    tasks_dir = REPO_ROOT / "bench" / "tasks"
    if args.dump_prompts:
        dump_prompts(tasks_dir)
        return
    if args.regrade:
        registry.load_keys(Path(args.env_file) if args.env_file else None)
        regrade(Path(args.regrade), Path(args.mcp_binary))
        return

    registry.load_keys(Path(args.env_file) if args.env_file else None)
    tasks = load_tasks(tasks_dir, only=TASK_IDS)
    if len(tasks) != len(TASK_IDS):
        raise SystemExit(f"expected {len(TASK_IDS)} tasks, loaded {len(tasks)}")

    resolved, skipped = [], []
    for name in args.models:
        spec = registry.resolve_model(name)
        if not registry.is_available(spec):
            skipped.append(name)
            print(f"[skip] {name}: {spec.provider_info.key_env} not set")
            continue
        resolved.append(spec)
    if not resolved:
        raise SystemExit("no runnable models (missing provider keys)")

    mcp_binary = Path(args.mcp_binary)

    def mcp_factory() -> SigilMCP:
        m = SigilMCP.spawn(mcp_binary)
        m.initialize()
        return m

    # Ground truth from the authoritative SIGIL reference, once per task.
    print("[gt] capturing ground truth from SIGIL reference forge ...")
    gt: dict[str, dict[str, str] | None] = {}
    with mcp_factory() as gt_mcp:
        for t in tasks:
            try:
                gt[t.id] = capture_ground_truth(t, REPO_ROOT, gt_mcp)
                miss = [k for k, v in (gt[t.id] or {}).items() if v is None]
                print(f"[gt] {t.id}: {len(gt[t.id] or {})} inputs" + (f" MISSING {miss}" if miss else ""))
            except Exception as e:  # noqa: BLE001
                gt[t.id] = None
                print(f"[gt] {t.id}: FAILED ({e})")

    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    run_dir = Path(args.out) / f"{ts}-baseline-py"
    (run_dir / "transcripts").mkdir(parents=True, exist_ok=True)
    (run_dir / "run_config.json").write_text(json.dumps({
        "timestamp_utc": ts, "target_language": "python", "models": [s.key for s in resolved],
        "models_skipped": skipped, "task_ids": [t.id for t in tasks], "runs": args.runs,
        "max_check_attempts": args.max_check_attempts, "max_model_turns": args.max_model_turns,
        "max_total_tool_calls": args.max_total_tool_calls,
    }, indent=2), encoding="utf-8")

    tools = model_tool_specs()
    rows: list[dict] = []
    results_fp = (run_dir / "results.jsonl").open("w", encoding="utf-8")
    total = len(resolved) * len(tasks) * args.runs
    n = 0
    try:
        for spec in resolved:
            backend = registry.build_backend(spec, request_timeout=args.request_timeout)
            for task in tasks:
                for run_index in range(args.runs):
                    n += 1
                    print(f"[{n}/{total}] {spec.key} | {task.id} | run {run_index}")
                    row = run_cell_py(
                        spec, backend, task, mcp_factory, tools,
                        max_check_attempts=args.max_check_attempts,
                        max_model_turns=args.max_model_turns,
                        max_total_tool_calls=args.max_total_tool_calls,
                        expected_outputs=gt.get(task.id), run_index=run_index,
                    )
                    results_fp.write(json.dumps(row["meta"]) + "\n")
                    results_fp.flush()
                    safe = spec.key.replace(":", "_").replace("/", "_")
                    tdir = run_dir / "transcripts" / safe
                    tdir.mkdir(parents=True, exist_ok=True)
                    (tdir / f"{task.id}__r{run_index}.json").write_text(json.dumps(row, indent=2), encoding="utf-8")
                    rows.append(row["meta"])
                    m = row["meta"]
                    print(f"    -> {m['final_outcome']} (1st_pass={m['first_pass_success']}, "
                          f"attempts={m['attempts_to_success']}, correct={m['final_source_correct']})")
            close_backend(backend)
    finally:
        results_fp.close()

    summary = summarize(rows)
    (run_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"\nDone. {len(rows)} cells -> {run_dir}")
    for key, b in summary["by_model"].items():
        print(f"  {key:26s} compile {b['success_rate']:.0%} ({b['compiled']}/{b['cells']})  "
              f"1st-pass {b['first_pass_success_rate']:.0%}  "
              f"correct|compiled {b['final_correct_rate'] if b['final_correct_rate'] is not None else '-'}")


def run_cell_py(spec, backend, task, mcp_factory, tools, *, max_check_attempts,
                max_model_turns, max_total_tool_calls, expected_outputs, run_index):
    """One baseline cell. Mirrors agentic.loop.run_cell; the Python executor
    needs no MCP, but ground-truth verify reuses the shared expected outputs."""
    start = time.perf_counter()
    system = render_system_prompt(task)
    messages: list[dict] = [{"role": "user", "text": KICKOFF_USER_MESSAGE}]
    usage_in = usage_out = 0
    turns = total_tool_calls = 0
    stop_reason = error = None
    ex = PyToolExecutor(task, REPO_ROOT, max_check_attempts=max_check_attempts, expected_outputs=expected_outputs)
    verify: dict = {}
    try:
        for _ in range(max_model_turns):
            turns += 1
            at = backend.converse(system, tools, messages)
            usage_in += int(at.usage.get("input_tokens", 0))
            usage_out += int(at.usage.get("output_tokens", 0))
            messages.append({"role": "assistant", "text": at.text,
                             "tool_calls": [tc.as_dict() for tc in at.tool_calls],
                             "stop_reason": at.stop_reason, "_raw": at.raw_content})
            if not at.tool_calls:
                stop_reason = "model_end_turn"
                break
            results, stop = [], False
            for tc in at.tool_calls:
                out, ctrl = ex.execute(tc.name, tc.arguments)
                total_tool_calls += 1
                results.append({"id": tc.id, "name": tc.name, "output": out})
                if ctrl.stop:
                    stop, stop_reason = True, ctrl.reason
                if total_tool_calls >= max_total_tool_calls:
                    stop, stop_reason = True, stop_reason or "max_tool_calls"
                if stop:
                    break
            messages.append({"role": "tool", "results": results})
            if stop:
                break
        else:
            stop_reason = stop_reason or "max_model_turns"
        verify = ex.verify_final_source()
    except Exception as e:  # noqa: BLE001
        error = f"{type(e).__name__}: {e}"

    any_passed = ex.any_check_passed
    if error is not None:
        outcome = "harness_error"
    elif any_passed:
        outcome = "success"
    elif ex.hit_cap:
        outcome = "hit_cap"
    elif stop_reason == "model_end_turn":
        outcome = "gave_up"
    elif stop_reason in ("max_model_turns", "max_tool_calls"):
        outcome = "exhausted_turns"
    else:
        outcome = "gave_up"
    final_correct = bool(verify.get("all_passed")) if verify.get("ran") else None

    meta = {
        "model_key": spec.key, "display_name": spec.display_name, "provider": spec.provider,
        "task_id": task.id, "run_index": run_index,
        "first_pass_success": bool(ex.first_check_ok),
        "attempts_to_success": ex.attempts_to_success, "check_attempts": ex.check_attempts,
        "final_outcome": outcome, "diagnostic_codes": dict(ex.code_counts),
        "final_source_correct": final_correct, "run_calls": ex.forge_calls,
        "model_turns": turns, "total_tool_calls": total_tool_calls,
        "usage": {"input_tokens": usage_in, "output_tokens": usage_out},
        "wall_seconds": round(time.perf_counter() - start, 3), "error": error,
        "stop_reason": stop_reason, "final_source": ex.last_passing_source, "final_verify": verify,
    }
    return {"meta": meta, "transcript": messages,
            "tool_log": [dataclasses.asdict(r) for r in ex.tool_log]}


def summarize(rows: list[dict]) -> dict:
    by_model: dict[str, list[dict]] = {}
    for r in rows:
        by_model.setdefault(r["model_key"], []).append(r)

    # Network tasks (all have "http" in the id) fetch a live URL; ground truth is
    # captured once and the model fetches independently, so a mismatch can be
    # fetch nondeterminism rather than a capability gap. We report them apart
    # from the deterministic tasks, whose oracle is exact and reproducible.
    def is_net(c: dict) -> bool:
        return "http" in c["task_id"]

    def block(cells: list[dict]) -> dict:
        n = len(cells)
        succ = [c for c in cells if c["final_outcome"] == "success"]
        att = [c["attempts_to_success"] for c in succ if c["attempts_to_success"] is not None]
        verified = [c for c in cells if c["final_source_correct"] is not None]
        correct = [c for c in verified if c["final_source_correct"]]
        exact = [c for c in verified if c.get("final_source_correct_exact")]
        det = [c for c in verified if not is_net(c)]
        net = [c for c in verified if is_net(c)]
        det_ok = [c for c in det if c["final_source_correct"]]
        net_ok = [c for c in net if c["final_source_correct"]]
        oc = Counter(c["final_outcome"] for c in cells)
        return {
            "display_name": cells[0]["display_name"], "provider": cells[0]["provider"], "cells": n,
            "compiled": len(succ), "success_rate": _rate(len(succ), n),
            "first_pass_success_rate": _rate(sum(c["first_pass_success"] for c in cells), n),
            "final_correct_rate": _rate(len(correct), len(verified)) if verified else None,
            "final_correct_count": len(correct), "verified_count": len(verified),
            "exact_correct_count": len(exact),
            "exact_correct_rate": _rate(len(exact), len(verified)) if verified else None,
            "deterministic_correct": f"{len(det_ok)}/{len(det)}",
            "deterministic_fails": sorted(c["task_id"] for c in det if not c["final_source_correct"]),
            "network_correct": f"{len(net_ok)}/{len(net)}",
            "network_fails": sorted(c["task_id"] for c in net if not c["final_source_correct"]),
            "mean_attempts_to_success": round(sum(att) / len(att), 2) if att else None,
            "outcome_counts": dict(oc),
        }

    return {"n_cells": len(rows), "by_model": {m: block(c) for m, c in by_model.items()}}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--models", nargs="+", default=[])
    ap.add_argument("--runs", type=int, default=1)
    ap.add_argument("--max-check-attempts", type=int, default=5)
    ap.add_argument("--max-model-turns", type=int, default=16)
    ap.add_argument("--max-total-tool-calls", type=int, default=40)
    ap.add_argument("--request-timeout", type=float, default=120.0)
    ap.add_argument("--out", default=str(REPO_ROOT / "bench" / "runs"))
    ap.add_argument("--mcp-binary", default=str(REPO_ROOT.parent / "SIGIL" / "target" / "debug" / "sigil-mcp.exe"))
    ap.add_argument("--env-file", default=None)
    ap.add_argument("--dump-prompts", action="store_true")
    ap.add_argument("--regrade", default=None, help="A completed run dir to re-grade from stored sources (no API).")
    args = ap.parse_args()
    if not args.dump_prompts and not args.regrade and not args.models:
        ap.error("--models is required unless --dump-prompts or --regrade")
    run(args)


if __name__ == "__main__":
    main()
