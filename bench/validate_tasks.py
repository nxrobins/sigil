#!/usr/bin/env python3
"""Oracle-validity gate: capture ground truth for every task and report.

For each task: forge the reference over every input (with grants/stdlib) and
report n_inputs, distinct outputs (the cheat-resistance lower bound from the
metric-gaming red team), and a sample. Any task whose GT capture fails is a
broken oracle and must be fixed before the experiment runs.
"""
from __future__ import annotations

import collections
import sys
from pathlib import Path

_SRC = Path(__file__).resolve().parent / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from sigil_bench.config import default_mcp_binary, find_repo_root  # noqa: E402
from sigil_bench.mcp_client import SigilMCP  # noqa: E402
from sigil_bench.runner import capture_ground_truth  # noqa: E402
from sigil_bench.tasks import load_tasks  # noqa: E402

repo = find_repo_root()
only = [t for t in sys.argv[1].split(",")] if len(sys.argv) > 1 else None
tasks = load_tasks(repo / "bench" / "tasks", only=only)
mcp = SigilMCP.spawn(default_mcp_binary(repo))
mcp.initialize()

ok, broken = [], []
print(f"{'TASK':32} {'DIFFICULTY':10} {'IN':>3} {'DISTINCT':>8}  SAMPLE")
for task in tasks:
    try:
        gt = capture_ground_truth(task, repo, mcp)
        distinct = len(set(gt.values()))
        sample = repr(next(iter(gt.values()))[:32])
        flag = "  <- LOW" if distinct < 2 and len(task.inputs) > 1 else ""
        print(f"{task.id:32} {task.difficulty.value:10} {len(task.inputs):>3} {distinct:>8}  {sample}{flag}")
        ok.append(task.id)
    except Exception as e:  # noqa: BLE001
        print(f"{task.id:32} {task.difficulty.value:10}  BROKEN: {type(e).__name__}: {str(e)[:80]}")
        broken.append(task.id)
mcp.close()


spread = collections.Counter(t.difficulty.value for t in tasks)
print(f"\nOK {len(ok)} / {len(tasks)}   spread={dict(spread)}")
if broken:
    print(f"BROKEN: {broken}")
    sys.exit(1)
