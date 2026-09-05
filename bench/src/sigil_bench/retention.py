"""Filesystem policy for retaining local benchmark runs."""

from __future__ import annotations

import shutil
import time
from pathlib import Path


def prune_old_run_dirs(runs_root: Path, keep_n: int) -> None:
    """Remove old inactive runs while keeping the newest eligible runs."""
    if keep_n < 0:
        raise ValueError("keep_n must be non-negative")
    if not runs_root.is_dir():
        return

    six_hours_ago = time.time() - (6 * 3600)
    candidates: list[tuple[float, Path]] = []
    for directory in runs_root.iterdir():
        if not directory.is_dir() or (directory / "lock").exists():
            continue
        run_id_file = directory / "run_id.txt"
        if run_id_file.is_file() and run_id_file.stat().st_mtime > six_hours_ago:
            continue
        candidates.append((directory.stat().st_mtime, directory))

    candidates.sort(reverse=True)
    for _mtime, directory in candidates[keep_n:]:
        try:
            shutil.rmtree(directory)
        except OSError:
            pass
