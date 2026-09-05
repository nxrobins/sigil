#!/usr/bin/env python3
"""Compile-health sweep over tools/task*.sigil candidate reference programs.

For each file: extract its `use sigil::<m>;` imports, compose the stdlib in, run
`sigil_check`, and report PASS / FAIL(+first code). Used to pick which existing
reference programs are still valid oracles for new bench tasks.
"""
from __future__ import annotations

import collections
import re
import sys
from pathlib import Path

_SRC = Path(__file__).resolve().parent / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from sigil_bench.compose import compose_with_stdlib  # noqa: E402
from sigil_bench.config import default_mcp_binary, find_repo_root  # noqa: E402
from sigil_bench.mcp_client import SigilMCP  # noqa: E402

_USE = re.compile(r"use\s+sigil::([a-z_][a-z0-9_]*)\s*;")

repo = find_repo_root()
binary = default_mcp_binary(repo)
files = sorted((repo / "tools").glob("task*.sigil"))
mcp = SigilMCP.spawn(binary)
mcp.initialize()
passes, fails = [], []
for f in files:
    src = f.read_text(encoding="utf-8")
    mods = sorted(set(_USE.findall(src)))
    try:
        composed = compose_with_stdlib(src, mods, repo).text if mods else src
        env = mcp.check(composed)
        if env.get("status") == "ok":
            passes.append(f.stem)
        else:
            codes = [d.get("code") for d in env.get("diagnostics", []) if isinstance(d, dict)]
            fails.append((f.stem, mods, codes[:3]))
    except Exception as e:  # noqa: BLE001
        fails.append((f.stem, mods, [f"EXC:{type(e).__name__}"]))
mcp.close()

print(f"PASS {len(passes)} / {len(files)}")
print("\n=== FAILS ===")
for name, mods, codes in fails:
    print(f"  {name:40} imports={mods} codes={codes}")
print("\n=== PASS by category ===")

buckets = collections.Counter()
for p in passes:
    n = int(re.search(r"task(\d+)", p).group(1))
    band = (n - 1) // 25 * 25 + 1
    buckets[band] += 1
for band in sorted(buckets):
    print(f"  task{band:03d}-{band+24:03d}: {buckets[band]}")
