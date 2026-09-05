"""E7 guard (diagnostics-axes a9): the scoreboard's `has_complete_ab_run`
counts ONLY a complete, live A/B — never a dry-run/stub, partial, single-arm,
or underpowered run. Loads tools/diag_axes_scoreboard.py directly so this is
CI-enforced (the scoreboard's own --self-test is not run by CI).
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


def _load_scoreboard():
    here = Path(__file__).resolve()
    for anc in here.parents:
        cand = anc / "tools" / "diag_axes_scoreboard.py"
        if cand.is_file():
            spec = importlib.util.spec_from_file_location("diag_axes_scoreboard", cand)
            mod = importlib.util.module_from_spec(spec)
            assert spec and spec.loader
            spec.loader.exec_module(mod)
            return mod
    pytest.skip("tools/diag_axes_scoreboard.py not found from test location")


def _summ(**kw) -> str:
    base = {
        "live": True,
        "arms_complete": True,
        "repeats": 5,
        "max_attempts": 5,
        "control_arm": "bare",
        "treatment_arm": "full",
    }
    base.update(kw)
    return json.dumps(base)


def _write(runs: Path, name: str, summ: str) -> None:
    (runs / name).mkdir()
    (runs / name / "ab_summary.json").write_text(summ, encoding="utf-8")


def test_incomplete_runs_do_not_flip_a9(tmp_path):
    sb = _load_scoreboard()
    runs = tmp_path / "runs"
    runs.mkdir()
    _write(runs, "dry", _summ(live=False))
    _write(runs, "partial", _summ(arms_complete=False))
    _write(runs, "underK", _summ(repeats=3))
    _write(runs, "underA", _summ(max_attempts=1))
    _write(runs, "onearm", _summ(treatment_arm="bare"))
    assert sb.has_complete_ab_run(runs) is False


def test_complete_live_ab_flips_a9(tmp_path):
    sb = _load_scoreboard()
    runs = tmp_path / "runs"
    runs.mkdir()
    _write(runs, "dry", _summ(live=False))  # decoy
    _write(runs, "good", _summ())
    assert sb.has_complete_ab_run(runs) is True


def test_missing_runs_dir_is_false(tmp_path):
    sb = _load_scoreboard()
    assert sb.has_complete_ab_run(tmp_path / "does_not_exist") is False
