"""Unit tests for the A/B comparison scorer (diagnostics-axes a9).

Pure functions over synthetic TaskResults — no MCP binary. Pins the comparison
constraints documented in docs/DIAGNOSTIC_EVIDENCE.md:
  E3  headline = (pass_rate, median_attempts_passers); exhausted excluded.
  E4  within-task pairing; differing task sets are rejected.
  E6  arms must share git SHA + config; otherwise PANIC.
  E8  the pre-registered decision rule cannot emit a win below threshold.
"""

from __future__ import annotations

import pytest

from sigil_bench.runner import TaskResult
from sigil_bench.scoring import (
    CommensurabilityError,
    _arm_summary,
    compare_conditions,
)


def _result(task_id: str, passed: bool, attempts: int, *, edits: int = 0) -> TaskResult:
    diagnostics = [
        {"code": "T060", "suggested_edits": [{"start": 0, "end": 1, "replacement": "x"}]}
        for _ in range(edits)
    ]
    attempt = {
        "attempt_no": 1,
        "source": "x",
        "check_envelope": {
            "status": "ok" if passed else "error",
            "diagnostics": diagnostics,
        },
        "failure_codes": [],
    }
    return TaskResult(
        task_id=task_id,
        passed=passed,
        reason="passed" if passed else "exhausted_attempts",
        attempts_used=attempts,
        attempts=[attempt],
    )


def _meta(arm: str, **over) -> dict:
    base = {
        "variable": "diagnostic_detail",
        "model": "m",
        "live": True,
        "git_sha": "deadbeef",
        "repeats": 5,
        "max_attempts": 5,
        "task_ids": ["a", "b", "c"],
        "arm": arm,
    }
    base.update(over)
    return base


def _arm(per_task: dict[str, int], *, edits_each: int = 0) -> list[TaskResult]:
    """per_task: task_id -> pass_count (of K=5). Passers use 2 attempts,
    failers exhaust at 5."""
    out: list[TaskResult] = []
    for task_id, npass in per_task.items():
        for i in range(5):
            passed = i < npass
            out.append(_result(task_id, passed, 2 if passed else 5, edits=edits_each if not passed else 0))
    return out


# ── E6 / E4 commensurability guard ────────────────────────────────────────


def test_e6_sha_mismatch_panics():
    with pytest.raises(CommensurabilityError):
        compare_conditions(
            _arm({"a": 5, "b": 5, "c": 5}),
            _arm({"a": 5, "b": 5, "c": 5}),
            control_meta=_meta("bare", git_sha="aaaa"),
            treatment_meta=_meta("full", git_sha="bbbb"),
        )


def test_e6_repeats_mismatch_panics():
    with pytest.raises(CommensurabilityError):
        compare_conditions(
            _arm({"a": 5, "b": 5, "c": 5}),
            _arm({"a": 5, "b": 5, "c": 5}),
            control_meta=_meta("bare", repeats=5),
            treatment_meta=_meta("full", repeats=3),
        )


def test_e4_task_set_mismatch_panics():
    with pytest.raises(CommensurabilityError):
        compare_conditions(
            _arm({"a": 5, "b": 5}),
            _arm({"a": 5, "b": 5}),
            control_meta=_meta("bare", task_ids=["a", "b"]),
            treatment_meta=_meta("full", task_ids=["a", "c"]),
        )


# ── E3 metric pair: median over passers, exhausted excluded ───────────────


def test_e3_median_excludes_exhausted():
    # task a: passers with 2 and 4 attempts + one exhausted (attempts_used 5).
    results = [
        _result("a", True, 2),
        _result("a", True, 4),
        _result("a", False, 5),
    ]
    s = _arm_summary("bare", results)
    assert s.passed == 2
    assert s.pass_rate == pytest.approx(2 / 3)
    assert s.median_attempts_passers == 3.0  # median(2,4) — the exhausted 5 excluded


# ── E8 decision rule ──────────────────────────────────────────────────────


def test_e8_treatment_helps_when_it_converts_failures():
    # treatment passes every task 5/5; control passes none. 3 task wins.
    report = compare_conditions(
        _arm({"a": 0, "b": 0, "c": 0}),
        _arm({"a": 5, "b": 5, "c": 5}),
        control_meta=_meta("bare"),
        treatment_meta=_meta("full"),
    )
    assert report.wins == {"treatment": 3, "control": 0, "tie": 0}
    assert report.verdict == "treatment_helps"
    # E3 headline pair is populated.
    assert report.treatment_summary.pass_rate == 1.0
    assert report.control_summary.pass_rate == 0.0


def test_e8_no_win_below_threshold():
    # treatment wins only task a; b and c tie (both 5/5). 1 win < min 3.
    report = compare_conditions(
        _arm({"a": 0, "b": 5, "c": 5}),
        _arm({"a": 5, "b": 5, "c": 5}),
        control_meta=_meta("bare"),
        treatment_meta=_meta("full"),
    )
    assert report.wins["treatment"] == 1
    assert report.verdict == "no_significant_difference"


def test_e8_attempts_tiebreak_only_when_pass_rate_ties():
    # Both arms pass all 5/5 on every task, but treatment converges faster
    # (median 2 vs 4) → attempts tie-break favors treatment on each task.
    control = []
    treatment = []
    for t in ("a", "b", "c"):
        for _ in range(5):
            control.append(_result(t, True, 4))
            treatment.append(_result(t, True, 2))
    report = compare_conditions(
        control,
        treatment,
        control_meta=_meta("bare"),
        treatment_meta=_meta("full"),
    )
    assert report.wins["treatment"] == 3
    assert report.verdict == "treatment_helps"


def test_compare_subcommand_parses():
    from sigil_bench.cli import build_parser

    args = build_parser().parse_args(
        ["compare", "--repeats", "5", "--dry-run", "--task", "task001_echo",
         "--model", "claude-haiku-4-5"]
    )
    assert args.cmd == "compare"
    assert args.repeats == 5
    assert args.dry_run is True
    assert args.task == ["task001_echo"]
    assert args.max_cost_usd == 25.0
    assert args.model == "claude-haiku-4-5"
    assert args.variable == "detail"  # default A/B variable


def test_compare_variable_edits_parses():
    from sigil_bench.cli import build_parser

    args = build_parser().parse_args(["compare", "--variable", "edits", "--dry-run"])
    assert args.variable == "edits"


def test_haiku_pricing_estimate_works():
    # iter 14: the weaker-model arm needs a pricing entry or the cost gate raises.
    from sigil_bench.scoring import estimate_cost

    est = estimate_cost(
        model="claude-haiku-4-5",
        system_tokens=80_000,
        avg_user_tokens=1_000,
        max_output_tokens=2_048,
        n_tasks=9,
        max_attempts=5,
    )
    assert est.total_max_usd > 0
    assert est.model == "claude-haiku-4-5"


def test_suggested_edits_presence_reported():
    # treatment failers each carry 2 edit-bearing diagnostics.
    report = compare_conditions(
        _arm({"a": 5, "b": 5, "c": 5}),
        _arm({"a": 0, "b": 0, "c": 0}, edits_each=2),
        control_meta=_meta("bare"),
        treatment_meta=_meta("full"),
    )
    se = report.suggested_edits_presence
    assert se["with_edits"] == se["total"]  # every treatment diagnostic had an edit
    assert se["total"] > 0
    assert se["fraction"] == 1.0


# ── E4 presence gate + E5 redundancy framing (suggested_edits experiment) ──


def _delivered_result(task_id: str, *, n_attempts: int = 3, edits_per_nonfinal: int = 1) -> TaskResult:
    """A passing run that retried `n_attempts` times, carrying `edits_per_nonfinal`
    edit-bearing diagnostics on every NON-final attempt (the ones actually shown
    to the agent on a retry). The final attempt is clean (it passed)."""
    attempts = []
    for i in range(n_attempts):
        is_final = i == n_attempts - 1
        diags = (
            []
            if is_final
            else [
                {"code": "P001", "suggested_edits": [{"start": 0, "end": 0, "replacement": ";"}]}
                for _ in range(edits_per_nonfinal)
            ]
        )
        attempts.append(
            {
                "attempt_no": i + 1,
                "source": "x",
                "check_envelope": {
                    "status": "ok" if is_final else "error",
                    "diagnostics": diags,
                },
                "failure_codes": [],
            }
        )
    return TaskResult(
        task_id=task_id,
        passed=True,
        reason="passed",
        attempts_used=n_attempts,
        attempts=attempts,
    )


def test_e4_edits_experiment_inconclusive_without_delivery():
    # Single-attempt runs deliver ZERO edits on a retry. Even a would-be
    # treatment win is gated to inconclusive — never "no effect", never a win.
    report = compare_conditions(
        _arm({"a": 0, "b": 0, "c": 0}),
        _arm({"a": 5, "b": 5, "c": 5}),  # treatment_helps in envelope mode
        control_meta=_meta("off", variable="suggested_edits"),
        treatment_meta=_meta("on", variable="suggested_edits"),
        experiment_kind="redundancy_restatement",
    )
    assert report.edits_delivered == 0
    assert report.verdict == "inconclusive_edits_not_delivered"
    assert report.experiment_kind == "redundancy_restatement"


def test_e4_edits_experiment_gate_opens_with_delivery():
    # Treatment retried with edits on the non-final attempts → edits were
    # delivered, so the gate opens and the normal decision rule applies.
    treatment = [_delivered_result(t) for t in ("a", "b", "c") for _ in range(5)]
    report = compare_conditions(
        _arm({"a": 0, "b": 0, "c": 0}),
        treatment,
        control_meta=_meta("off", variable="suggested_edits"),
        treatment_meta=_meta("on", variable="suggested_edits"),
        experiment_kind="redundancy_restatement",
    )
    assert report.edits_delivered >= 5
    assert report.verdict != "inconclusive_edits_not_delivered"
    assert report.verdict == "treatment_helps"  # 5/5 vs 0/5


def test_e5_redundancy_framing_makes_no_plus45_claim():
    treatment = [_delivered_result(t) for t in ("a", "b", "c") for _ in range(5)]
    report = compare_conditions(
        _arm({"a": 0, "b": 0, "c": 0}),
        treatment,
        control_meta=_meta("off", variable="suggested_edits"),
        treatment_meta=_meta("on", variable="suggested_edits"),
        experiment_kind="redundancy_restatement",
    )
    assert report.experiment_kind == "redundancy_restatement"
    assert any("REDUNDANCY TEST" in c for c in report.caveats)
    joined = " ".join(report.caveats).lower()
    assert "+45%" not in joined
    assert "concrete suggestion" not in joined
