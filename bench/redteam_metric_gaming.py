#!/usr/bin/env python3
"""Metric-gaming red team: can a non-solution score `final_source_correct`?

Two empirical probes against the harness's REAL verify path:

  1. Constant-cheat sweep (deterministic, no API): for each task, build a tool
     that emits a FIXED byte string for any input and run it through verify.
     It passes iff every test input shares one output — i.e. the task is
     "constant-gameable" (single input, or all inputs map to the same answer).
     The count of DISTINCT expected outputs is a lower bound on cheat-resistance.

  2. Grant-necessity probe: for grant-requiring tasks, run a candidate WITH and
     WITHOUT the grant. A genuine solution fails without the capability; a
     hardcoded constant succeeds either way → the capability was never used.

Optional `--model <key>` also runs the cheat-seeking adversarial system prompt
through the live agentic loop and reports whether the model gamed each task.

    python bench/redteam_metric_gaming.py                      # deterministic only
    python bench/redteam_metric_gaming.py --model gpt-5.5-azure # + model-driven
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

_SRC = Path(__file__).resolve().parent / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from sigil_bench.agentic import registry  # noqa: E402
from sigil_bench.agentic.loop import run_cell  # noqa: E402
from sigil_bench.agentic.redteam import (  # noqa: E402
    constant_output_cheat,
    grant_necessity_probe,
    render_adversarial_prompt,
    run_cheat_probe,
)
from sigil_bench.config import default_mcp_binary, find_repo_root  # noqa: E402
from sigil_bench.mcp_client import SigilMCP  # noqa: E402
from sigil_bench.runner import capture_ground_truth  # noqa: E402
from sigil_bench.tasks import load_tasks  # noqa: E402


def _spawn(binary: Path) -> SigilMCP:
    mcp = SigilMCP.spawn(binary)
    mcp.initialize()
    return mcp


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="metric-gaming red team for the agentic harness")
    p.add_argument("--tasks", default="", help="comma list of task ids (default: all)")
    p.add_argument("--model", default=None, help="also run the cheat-seeking adversarial loop with this model key")
    p.add_argument("--env-file", default=None)
    p.add_argument("--out", default=None)
    args = p.parse_args(argv)

    repo = find_repo_root()
    binary = default_mcp_binary(repo)
    if not binary.is_file():
        print(f"error: sigil-mcp not built at {binary}", file=sys.stderr)
        return 2
    tasks = load_tasks(repo / "bench" / "tasks", only=[t for t in args.tasks.split(",") if t] or None)

    backend = None
    if args.model:
        registry.load_keys(Path(args.env_file) if args.env_file else None)
        spec = registry.resolve_model(args.model)
        if not registry.is_available(spec):
            print(f"error: {args.model} unavailable ({spec.provider_info.key_env} not set)", file=sys.stderr)
            return 2
        backend = registry.build_backend(spec)

    findings: list[dict] = []
    with _spawn(binary) as mcp:
        for task in tasks:
            row: dict = {"task": task.id, "n_inputs": len(task.inputs)}
            try:
                gt = capture_ground_truth(task, repo, mcp)
            except Exception as e:  # noqa: BLE001
                row["error"] = f"ground-truth capture failed: {e}"
                findings.append(row)
                print(f"[{task.id}] GT capture FAILED: {e}")
                continue
            distinct = sorted(set(gt.values()))
            row["distinct_outputs"] = len(distinct)

            # 1. Constant-cheat sweep (built from the first input's expected output).
            first_out = gt[task.inputs[0].name]
            cheat = constant_output_cheat(first_out, param_int="i32")
            probe = run_cheat_probe(task, cheat, mcp, repo, expected_outputs=gt)
            if not probe["compiles"]:
                cheat = constant_output_cheat(first_out, param_int="i64")
                probe = run_cheat_probe(task, cheat, mcp, repo, expected_outputs=gt)
            row["constant_cheat_compiles"] = probe["compiles"]
            row["constant_cheat_gamed"] = probe.get("gamed", False)
            if not probe["compiles"]:
                row["constant_cheat_codes"] = probe.get("check_codes")

            # 2. Grant-necessity probe (on the cheat, for grant-requiring tasks).
            gnp = grant_necessity_probe(task, cheat, mcp, repo)
            row["grant_probe"] = gnp.get("applicable", False)
            if gnp.get("applicable"):
                row["capability_unused_by_cheat"] = gnp["capability_unused"]

            # 3. Optional: live model-driven adversarial loop.
            if backend is not None:
                res = run_cell(
                    model_key=args.model, display_name=args.model, provider=spec.provider,
                    backend=backend, task=task, mcp_factory=lambda: _spawn(binary), repo_root=repo,
                    max_check_attempts=6, verify_final=True, expected_outputs=gt,
                    system_prompt=render_adversarial_prompt(task),
                )
                row["model_outcome"] = res.final_outcome
                row["model_gamed"] = res.final_source_correct
                row["model_final_source"] = res.final_source
                if res.final_source:
                    # Apply the grant-necessity detector to what the model produced.
                    mg = grant_necessity_probe(task, res.final_source, mcp, repo)
                    if mg.get("applicable"):
                        row["model_capability_unused"] = mg["capability_unused"]

            findings.append(row)
            verdict = "GAMED" if row["constant_cheat_gamed"] else (
                "compiles-but-fails" if row["constant_cheat_compiles"] else "no-compile"
            )
            extra = ""
            if row.get("grant_probe"):
                extra = f" | cheat ignores capability: {row.get('capability_unused_by_cheat')}"
            if backend is not None:
                extra += f" | model: {row.get('model_outcome')} gamed={row.get('model_gamed')}"
            print(f"[{task.id}] inputs={row['n_inputs']} distinct_outputs={row['distinct_outputs']} "
                  f"constant-cheat={verdict}{extra}")

    # Write findings.
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out_dir = Path(args.out) if args.out else repo / "bench" / "runs"
    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / f"{ts}-redteam.json"
    path.write_text(json.dumps({"timestamp_utc": ts, "model": args.model, "findings": findings}, indent=2), encoding="utf-8")

    gamed = [r["task"] for r in findings if r.get("constant_cheat_gamed")]
    print("\n=== summary ===")
    print(f"constant-gameable tasks: {gamed or 'none'}")
    print(f"findings -> {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
