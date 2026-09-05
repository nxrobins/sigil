"""Properties for local benchmark run retention."""

from __future__ import annotations

import os
from pathlib import Path
from tempfile import TemporaryDirectory

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from sigil_bench.retention import prune_old_run_dirs


@given(
    mtimes=st.lists(
        st.integers(min_value=1, max_value=1_000_000_000),
        max_size=16,
        unique=True,
    ),
    keep_n=st.integers(min_value=0, max_value=20),
)
@settings(max_examples=50, deadline=None)
def test_pruning_keeps_exactly_the_newest_unlocked_runs(mtimes, keep_n) -> None:
    with TemporaryDirectory() as directory:
        root = Path(directory)
        runs = []
        for index, mtime in enumerate(mtimes):
            run = root / f"run-{index:02d}"
            run.mkdir()
            os.utime(run, (mtime, mtime))
            runs.append((mtime, run.name))

        prune_old_run_dirs(root, keep_n)

        expected = {name for _mtime, name in sorted(runs, reverse=True)[:keep_n]}
        actual = {path.name for path in root.iterdir()}
        assert actual == expected


def test_pruning_rejects_negative_retention(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="keep_n"):
        prune_old_run_dirs(tmp_path, -1)


def test_pruning_preserves_locked_and_recent_runs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    now = 1_000_000.0
    old_mtime = now - (8 * 3600)
    monkeypatch.setattr("time.time", lambda: now)

    stale = tmp_path / "stale"
    stale.mkdir()
    os.utime(stale, (old_mtime, old_mtime))

    locked = tmp_path / "locked"
    locked.mkdir()
    (locked / "lock").touch()
    os.utime(locked, (old_mtime, old_mtime))

    recent = tmp_path / "recent"
    recent.mkdir()
    run_id = recent / "run_id.txt"
    run_id.touch()
    os.utime(run_id, (now - 3600, now - 3600))
    os.utime(recent, (old_mtime, old_mtime))

    prune_old_run_dirs(tmp_path, keep_n=0)

    assert not stale.exists()
    assert locked.is_dir()
    assert recent.is_dir()
