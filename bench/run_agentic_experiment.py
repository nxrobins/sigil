#!/usr/bin/env python3
"""Standalone launcher for the SIGIL agentic convergence experiment.

Bootstraps `bench/src` onto sys.path (so it runs without `pip install -e`),
then defers to `sigil_bench.agentic.cli`. See that module's docstring for
usage, or run `--help` / `--list-models`.

    python bench/run_agentic_experiment.py --dry-run --tasks task001_echo
    python bench/run_agentic_experiment.py --models default --runs 1
"""

from __future__ import annotations

import sys
from pathlib import Path

_SRC = Path(__file__).resolve().parent / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from sigil_bench.agentic.cli import main  # noqa: E402

if __name__ == "__main__":
    raise SystemExit(main())
