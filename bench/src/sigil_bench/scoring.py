"""Aggregate `TaskResult`s into a `RunReport` and write console / JSON /
markdown outputs.

Keeps presentation decoupled from the loop runner so a CI lane can reuse
the report generator over already-completed runs (resume / replay).
"""

from __future__ import annotations

import hashlib
import json
import statistics
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from pydantic import BaseModel, Field
from rich.console import Console
from rich.table import Table

from .config import PRICING_PER_MTOK_USD, Settings
from .runner import TaskResult
from .tasks import TaskSpec

# Phase 5a-4 / I24 + Phase 6a-2 / I-OPS-16: transcripts carry a header
# line with schema_version, created_by_run_id, and transcript_sha256.
# `--resume` validates all three before consuming a previous run's
# transcripts. Bumping this constant is a breaking change for resume —
# existing transcripts at the old version are rejected with a clear
# error rather than silently misinterpreted.
#
# Phase 6a-2 (schema v3): the hash protocol changed from "body only"
# to "header + body via zeroed-field protocol." See `_full_file_sha256`
# for the protocol details and AP-OPS-13 for what the fix prevents.
TRANSCRIPT_SCHEMA_VERSION: int = 3

# Placeholder for the `transcript_sha256` field during hash computation.
# 64 zero hex chars matches the length of a real sha256 so the byte
# stream the hash covers has the same length whether we're computing
# or validating.
_ZEROED_HASH_PLACEHOLDER: str = "0" * 64

# Sentinel for "this header line failed validation in some way" — used
# by callers to distinguish "no header" from "header present but bad".
class TranscriptIntegrityError(ValueError):
    """Raised when --resume encounters a transcript whose header is
    missing, malformed, written by a different run, or whose body
    sha256 doesn't match the recorded value."""

# ── Aggregate models ─────────────────────────────────────────────────────


class RunReport(BaseModel):
    """One run's worth of aggregate stats. Pydantic so it round-trips
    cleanly to JSON for `runs/<ts>/results.json`."""

    run_id: str
    started_at: str
    finished_at: str
    model: str
    total_tasks: int
    passed: int
    failed: int
    pass_rate: float
    mean_attempts_passers: float | None
    median_attempts_passers: float | None
    mean_fuel_passers: float | None
    top_failure_codes: list[tuple[str, int]] = Field(default_factory=list)
    by_difficulty: dict[str, dict[str, int]] = Field(default_factory=dict)
    by_reason: dict[str, int] = Field(default_factory=dict)
    cost_estimate_usd: float | None = None
    results: list[TaskResult] = Field(default_factory=list)


# ── Aggregation ──────────────────────────────────────────────────────────


def aggregate(
    results: list[TaskResult],
    tasks: list[TaskSpec],
    *,
    run_id: str,
    started_at: datetime,
    finished_at: datetime,
    model: str,
    cost_estimate_usd: float | None = None,
) -> RunReport:
    """Build a RunReport from per-task results. `tasks` is parallel to
    `results` (same order, same length) so we can correlate difficulty
    bands without re-loading YAML."""
    if len(results) != len(tasks):
        raise ValueError(
            f"results and tasks must be the same length; "
            f"got results={len(results)} tasks={len(tasks)}"
        )

    passers = [r for r in results if r.passed]
    by_difficulty: dict[str, dict[str, int]] = {}
    for task, result in zip(tasks, results, strict=True):
        bucket = by_difficulty.setdefault(
            task.difficulty.value, {"passed": 0, "failed": 0}
        )
        bucket["passed" if result.passed else "failed"] += 1

    # Phase 6a-2 / I-OPS-17: failure_codes is now `list[dict]` with
    # `code` + `detail` fields. Bucket by `code` only — operator wants
    # to see "T060: 5 occurrences" not 5 separate entries with
    # different detail strings.
    code_counter: Counter[str] = Counter()
    for r in results:
        code_counter.update(entry["code"] for entry in r.failure_codes)

    reason_counter: Counter[str] = Counter(r.reason for r in results)

    mean_attempts = (
        statistics.fmean(r.attempts_used for r in passers) if passers else None
    )
    median_attempts = (
        statistics.median(r.attempts_used for r in passers) if passers else None
    )
    fuel_values = [r.total_fuel_consumed for r in passers if r.total_fuel_consumed > 0]
    mean_fuel = statistics.fmean(fuel_values) if fuel_values else None

    return RunReport(
        run_id=run_id,
        started_at=started_at.astimezone(UTC).isoformat(),
        finished_at=finished_at.astimezone(UTC).isoformat(),
        model=model,
        total_tasks=len(results),
        passed=len(passers),
        failed=len(results) - len(passers),
        pass_rate=(len(passers) / len(results)) if results else 0.0,
        mean_attempts_passers=mean_attempts,
        median_attempts_passers=float(median_attempts) if median_attempts is not None else None,
        mean_fuel_passers=mean_fuel,
        top_failure_codes=code_counter.most_common(5),
        by_difficulty=by_difficulty,
        by_reason=dict(reason_counter),
        cost_estimate_usd=cost_estimate_usd,
        results=results,
    )


# ── A/B comparison (diagnostics-axes a9: close the measurement loop) ───────
#
# Compares two arms — control (`bare` diagnostics) vs treatment (`full`
# envelope) — over K repeats × N tasks. Every integrity constraint from the
# comparison contract (docs/DIAGNOSTIC_EVIDENCE.md) lives here:
#   E3  the headline is the PAIR (pass_rate, median_attempts_passers);
#       exhausted tasks count only against pass_rate, never as a capped attempt.
#   E4  comparison is WITHIN-task (K vs K on the same id); aggregate is a
#       win/tie/lose COUNT, never a cross-task pooled mean.
#   E6  the two arms must share git SHA + config (except the variable);
#       compare_conditions PANICS otherwise.
#   E8  a fixed, pre-registered decision rule — cannot emit a win below
#       threshold.

# E8 decision-rule constants. Written verbatim into preregistration.json
# BEFORE the first LLM call, so the verdict cannot be tuned to the data.
PASS_DELTA_THRESHOLD = 2  # per-task: |Δ pass-count| ≥ this ⇒ a pass-rate win
ATTEMPTS_MARGIN = 1       # tie-break only: median-attempts lower by ≥ this
GLOBAL_MIN_WINS = 3       # global: an arm needs ≥ this many task wins …
GLOBAL_WIN_RATIO = 2      # … AND ≥ this × the other arm's wins


class ArmSummary(BaseModel):
    """Headline metric PAIR for one arm (E3)."""

    arm: str
    n_results: int  # K × N
    passed: int
    pass_rate: float
    median_attempts_passers: float | None  # passers only — exhausted excluded


class TaskComparison(BaseModel):
    task_id: str
    control_passed: int  # of K
    treatment_passed: int  # of K
    control_median_attempts: float | None  # passers only
    treatment_median_attempts: float | None
    verdict: str  # "treatment" | "control" | "tie"


class ComparisonReport(BaseModel):
    """One A/B's worth of results. Round-trips to JSON for ab_summary.json."""

    variable: str
    control_arm: str
    treatment_arm: str
    model: str
    live: bool
    git_sha: str
    repeats: int
    max_attempts: int
    n_tasks: int
    arms_complete: bool
    experiment_kind: str = "envelope"
    edits_delivered: int = 0
    control_summary: ArmSummary
    treatment_summary: ArmSummary
    per_task: list[TaskComparison]
    wins: dict[str, int]  # {"treatment": n, "control": n, "tie": n}
    verdict: str  # "treatment_helps" | "control_helps" | "no_significant_difference"
    decision_rule: dict[str, int]
    suggested_edits_presence: dict[str, float]  # {with_edits, total, fraction}
    caveats: list[str] = Field(default_factory=list)


def _arm_summary(arm: str, results: list[TaskResult]) -> ArmSummary:
    passers = [r for r in results if r.passed]
    med = (
        statistics.median(r.attempts_used for r in passers) if passers else None
    )
    return ArmSummary(
        arm=arm,
        n_results=len(results),
        passed=len(passers),
        pass_rate=(len(passers) / len(results)) if results else 0.0,
        median_attempts_passers=float(med) if med is not None else None,
    )


def _by_task(results: list[TaskResult]) -> dict[str, list[TaskResult]]:
    out: dict[str, list[TaskResult]] = {}
    for r in results:
        out.setdefault(r.task_id, []).append(r)
    return out


def _median_attempts(results: list[TaskResult]) -> float | None:
    passers = [r for r in results if r.passed]
    return statistics.median(r.attempts_used for r in passers) if passers else None


def _task_verdict(
    c_pass: int, t_pass: int, c_med: float | None, t_med: float | None, *, k: int
) -> str:
    """Pre-registered per-task rule (E8). Pass-rate is primary; attempts is
    a tie-break used ONLY when pass-counts tie and both arms reliably pass."""
    if t_pass - c_pass >= PASS_DELTA_THRESHOLD:
        return "treatment"
    if c_pass - t_pass >= PASS_DELTA_THRESHOLD:
        return "control"
    # pass-rate tie → convergence-speed tie-break, only if both pass a majority
    min_pass = (k + 1) // 2
    if (
        c_pass >= min_pass
        and t_pass >= min_pass
        and c_med is not None
        and t_med is not None
    ):
        if c_med - t_med >= ATTEMPTS_MARGIN:
            return "treatment"
        if t_med - c_med >= ATTEMPTS_MARGIN:
            return "control"
    return "tie"


def _global_verdict(treatment_wins: int, control_wins: int) -> str:
    """Pre-registered global rule (E8). Below threshold → no win can be emitted."""
    if treatment_wins >= GLOBAL_MIN_WINS and treatment_wins >= GLOBAL_WIN_RATIO * control_wins:
        return "treatment_helps"
    if control_wins >= GLOBAL_MIN_WINS and control_wins >= GLOBAL_WIN_RATIO * treatment_wins:
        return "control_helps"
    return "no_significant_difference"


def count_suggested_edits_presence(
    results: list[TaskResult],
) -> tuple[int, int]:
    """How many diagnostics across these runs carried a suggested_edit.
    The envelope-level claim never over-credits this one rare field — we
    report its actual presence so a reader can bound its contribution."""
    total = 0
    with_edits = 0
    for r in results:
        for a in r.attempts:
            for d in (a.check_envelope or {}).get("diagnostics") or []:
                total += 1
                if d.get("suggested_edits"):
                    with_edits += 1
    return with_edits, total


# E4: a redundancy/edits experiment's verdict is only valid if the edits
# actually reached the agent on a retry at least this many times.
EDITS_DELIVERED_FLOOR = 5


def edits_delivered_to_agent(results: list[TaskResult]) -> int:
    """Count edit-bearing diagnostics that were actually SHOWN to the agent on a
    retry — i.e. on an attempt that had a successor (the generator surfaces the
    most-recent attempt's diagnostics when producing the next one). An edit on a
    task's FINAL attempt was generated but never acted on, so it doesn't count."""
    delivered = 0
    for r in results:
        for a in r.attempts[:-1]:  # every attempt except the last was followed by a retry
            for d in (a.check_envelope or {}).get("diagnostics") or []:
                if d.get("suggested_edits"):
                    delivered += 1
    return delivered


class CommensurabilityError(ValueError):
    """Raised (E6) when the two arms are not comparable — different git SHA,
    model, repeats, max_attempts, or task set. Refusing to compare beats
    silently reporting a confounded delta."""


def _assert_commensurable(control_meta: dict, treatment_meta: dict) -> None:
    for key in ("git_sha", "model", "repeats", "max_attempts"):
        if control_meta.get(key) != treatment_meta.get(key):
            raise CommensurabilityError(
                f"arms differ in {key!r}: control={control_meta.get(key)!r} "
                f"treatment={treatment_meta.get(key)!r}; refusing to compare (E6)."
            )
    c_tasks = set(control_meta.get("task_ids") or [])
    t_tasks = set(treatment_meta.get("task_ids") or [])
    if c_tasks != t_tasks:
        raise CommensurabilityError(
            f"arms ran different task sets (E4): only-control={c_tasks - t_tasks}, "
            f"only-treatment={t_tasks - c_tasks}."
        )


def compare_conditions(
    control_results: list[TaskResult],
    treatment_results: list[TaskResult],
    *,
    control_meta: dict,
    treatment_meta: dict,
    arms_complete: bool = True,
    experiment_kind: str = "envelope",
) -> ComparisonReport:
    """Compare control (bare) vs treatment (full) per task (E4), score the
    headline pair (E3), apply the pre-registered rule (E8). PANICS unless the
    arms are commensurable (E6/E4)."""
    _assert_commensurable(control_meta, treatment_meta)

    k = int(control_meta["repeats"])
    by_c = _by_task(control_results)
    by_t = _by_task(treatment_results)
    if set(by_c) != set(by_t):
        raise CommensurabilityError(
            f"per-task result sets differ (E4): "
            f"only-control={set(by_c) - set(by_t)}, only-treatment={set(by_t) - set(by_c)}."
        )

    per_task: list[TaskComparison] = []
    wins = {"treatment": 0, "control": 0, "tie": 0}
    for task_id in sorted(by_c):
        c_runs, t_runs = by_c[task_id], by_t[task_id]
        c_pass = sum(1 for r in c_runs if r.passed)
        t_pass = sum(1 for r in t_runs if r.passed)
        c_med = _median_attempts(c_runs)
        t_med = _median_attempts(t_runs)
        verdict = _task_verdict(c_pass, t_pass, c_med, t_med, k=k)
        wins[verdict] += 1
        per_task.append(
            TaskComparison(
                task_id=task_id,
                control_passed=c_pass,
                treatment_passed=t_pass,
                control_median_attempts=c_med,
                treatment_median_attempts=t_med,
                verdict=verdict,
            )
        )

    with_edits, total_diags = count_suggested_edits_presence(treatment_results)
    delivered = edits_delivered_to_agent(treatment_results)
    global_verdict = _global_verdict(wins["treatment"], wins["control"])
    # E4: an edits/redundancy verdict is valid only if the edits actually
    # reached the agent on a retry; otherwise it's inconclusive, not "no effect".
    if experiment_kind == "redundancy_restatement" and delivered < EDITS_DELIVERED_FLOOR:
        global_verdict = "inconclusive_edits_not_delivered"

    caveats = [
        f"Underpowered: {len(per_task)} tasks × {k} repeats; temp≈1.0, no seed. "
        "Directional evidence, not proof.",
    ]
    if experiment_kind == "redundancy_restatement":
        caveats.append(
            "REDUNDANCY TEST — this is NOT a replication of the compiler-remarks speedup "
            "finding. The edited codes (P001/N007) largely restate their own message, so this "
            "measures whether a structured restatement of an already-stated fix helps or hurts "
            f"a weak model. edits_delivered={delivered} (floor {EDITS_DELIVERED_FLOOR})."
        )
    else:
        caveats.append(
            f"suggested_edits appeared on {with_edits}/{total_diags} treatment diagnostics; "
            "the envelope-level verdict is not attributable to that one field."
        )
    if not arms_complete:
        caveats.insert(0, "INCOMPLETE: not all arms/repeats finished — verdict is provisional.")

    return ComparisonReport(
        variable=control_meta.get("variable", "diagnostic_detail"),
        control_arm=control_meta.get("arm", "bare"),
        treatment_arm=treatment_meta.get("arm", "full"),
        model=control_meta["model"],
        live=bool(control_meta.get("live", False) and treatment_meta.get("live", False)),
        git_sha=control_meta["git_sha"],
        repeats=k,
        max_attempts=int(control_meta["max_attempts"]),
        n_tasks=len(per_task),
        arms_complete=arms_complete,
        experiment_kind=experiment_kind,
        edits_delivered=delivered,
        control_summary=_arm_summary(control_meta.get("arm", "bare"), control_results),
        treatment_summary=_arm_summary(treatment_meta.get("arm", "full"), treatment_results),
        per_task=per_task,
        wins=wins,
        verdict=global_verdict,
        decision_rule={
            "pass_delta_threshold": PASS_DELTA_THRESHOLD,
            "attempts_margin": ATTEMPTS_MARGIN,
            "global_min_wins": GLOBAL_MIN_WINS,
            "global_win_ratio": GLOBAL_WIN_RATIO,
        },
        suggested_edits_presence={
            "with_edits": with_edits,
            "total": total_diags,
            "fraction": round(with_edits / total_diags, 4) if total_diags else 0.0,
        },
        caveats=caveats,
    )


def write_comparison_markdown(report: ComparisonReport, path: Path) -> None:
    """Human-readable A/B report — the committed measurement artifact."""
    path.parent.mkdir(parents=True, exist_ok=True)
    lines: list[str] = []
    lines.append(f"# diagnostics-axes A/B — `{report.variable}` ({report.experiment_kind})")
    lines.append("")
    lines.append(f"- **Variable**: `{report.variable}` "
                 f"(control=`{report.control_arm}`, treatment=`{report.treatment_arm}`)")
    lines.append(f"- **Edits delivered to agent**: {report.edits_delivered}")
    lines.append(f"- **Model**: {report.model} · **live**: {report.live} · "
                 f"**git**: `{report.git_sha[:12]}`")
    lines.append(f"- **Design**: {report.n_tasks} tasks × {report.repeats} repeats/arm, "
                 f"max {report.max_attempts} attempts")
    lines.append(f"- **Verdict**: **{report.verdict}** "
                 f"(treatment wins {report.wins['treatment']}, control {report.wins['control']}, "
                 f"tie {report.wins['tie']})")
    lines.append("")
    lines.append("## Headline (per arm)")
    lines.append("")
    lines.append("| Arm | pass_rate | median attempts (passers) |")
    lines.append("|---|---:|---:|")
    for s in (report.control_summary, report.treatment_summary):
        med = f"{s.median_attempts_passers:.1f}" if s.median_attempts_passers is not None else "—"
        lines.append(f"| `{s.arm}` | {s.pass_rate * 100:.1f}% ({s.passed}/{s.n_results}) | {med} |")
    lines.append("")
    lines.append("## Per-task (within-task pairing)")
    lines.append("")
    lines.append("| Task | control pass | treatment pass | control med | treatment med | favors |")
    lines.append("|---|---:|---:|---:|---:|---|")
    for t in report.per_task:
        cm = f"{t.control_median_attempts:.1f}" if t.control_median_attempts is not None else "—"
        tm = f"{t.treatment_median_attempts:.1f}" if t.treatment_median_attempts is not None else "—"
        lines.append(
            f"| `{t.task_id}` | {t.control_passed}/{report.repeats} | "
            f"{t.treatment_passed}/{report.repeats} | {cm} | {tm} | {t.verdict} |"
        )
    lines.append("")
    lines.append("## Decision rule (pre-registered)")
    lines.append("")
    lines.append(f"- per-task win: |Δ pass-count| ≥ {report.decision_rule['pass_delta_threshold']} "
                 f"(else attempts tie-break by ≥ {report.decision_rule['attempts_margin']})")
    lines.append(f"- global: an arm needs ≥ {report.decision_rule['global_min_wins']} wins AND "
                 f"≥ {report.decision_rule['global_win_ratio']}× the other's")
    se = report.suggested_edits_presence
    lines.append("")
    lines.append("## Suggested edits")
    lines.append("")
    lines.append(f"- experiment kind: `{report.experiment_kind}`")
    lines.append(
        f"- present on {se['with_edits']}/{se['total']} treatment diagnostics "
        f"({se['fraction']:.1%})"
    )
    lines.append(f"- delivered to agent on a retry: {report.edits_delivered}")
    lines.append("")
    lines.append("## Caveats")
    lines.append("")
    for c in report.caveats:
        lines.append(f"- {c}")
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text("\n".join(lines) + "\n", encoding="utf-8")
    tmp.replace(path)


# ── Cost estimation ─────────────────────────────────────────────────────


class CostEstimate(BaseModel):
    """Pre-flight cost estimate. Used by the CLI to confirm before
    spending. All token counts are integer; USD figures are float."""

    model: str
    n_tasks: int
    max_attempts: int
    system_tokens: int
    avg_user_tokens: int
    max_output_tokens: int
    cache_writes: int
    cache_hits: int
    user_calls: int
    output_calls: int
    cost_cache_write_usd: float
    cost_cache_hit_usd: float
    cost_user_input_usd: float
    cost_output_usd: float
    total_max_usd: float


def estimate_cost(
    *,
    model: str,
    system_tokens: int,
    avg_user_tokens: int,
    max_output_tokens: int,
    n_tasks: int,
    max_attempts: int,
) -> CostEstimate:
    """Worst-case cost: every task pays one cache_write (conservative —
    in practice only the first call of the run does, since the cache
    blocks are identical across tasks within the 5-min TTL window)
    and every subsequent attempt pays a cache_hit. Output assumed to
    saturate `max_output_tokens` per call."""
    pricing = PRICING_PER_MTOK_USD.get(model)
    if pricing is None:
        raise ValueError(
            f"no pricing entry for model {model!r}; "
            f"add one to PRICING_PER_MTOK_USD or pass a known model"
        )
    cache_writes = n_tasks  # conservative: one per task
    total_calls = n_tasks * max_attempts
    cache_hits = total_calls - cache_writes
    user_calls = total_calls
    output_calls = total_calls

    cost_cache_write = (cache_writes * system_tokens) * pricing["cache_write"] / 1_000_000
    cost_cache_hit = (cache_hits * system_tokens) * pricing["cache_hit"] / 1_000_000
    cost_user = (user_calls * avg_user_tokens) * pricing["input"] / 1_000_000
    cost_output = (output_calls * max_output_tokens) * pricing["output"] / 1_000_000
    total = cost_cache_write + cost_cache_hit + cost_user + cost_output

    return CostEstimate(
        model=model,
        n_tasks=n_tasks,
        max_attempts=max_attempts,
        system_tokens=system_tokens,
        avg_user_tokens=avg_user_tokens,
        max_output_tokens=max_output_tokens,
        cache_writes=cache_writes,
        cache_hits=cache_hits,
        user_calls=user_calls,
        output_calls=output_calls,
        cost_cache_write_usd=cost_cache_write,
        cost_cache_hit_usd=cost_cache_hit,
        cost_user_input_usd=cost_user,
        cost_output_usd=cost_output,
        total_max_usd=total,
    )


# ── Writers ──────────────────────────────────────────────────────────────


def render_console(report: RunReport, console: Console | None = None) -> None:
    """Print a one-screen summary. Default console honors the user's
    terminal width."""
    console = console or Console()
    console.rule(f"[bold]sigil-bench[/bold] · run [cyan]{report.run_id}[/cyan]")

    summary = Table(show_header=False, box=None, pad_edge=False)
    summary.add_column(style="dim")
    summary.add_column()
    summary.add_row("model", report.model)
    summary.add_row("tasks", str(report.total_tasks))
    summary.add_row(
        "pass rate",
        f"[green]{report.passed}[/green]/{report.total_tasks} "
        f"({report.pass_rate * 100:.1f}%)",
    )
    if report.mean_attempts_passers is not None:
        summary.add_row(
            "attempts (passers)",
            f"mean {report.mean_attempts_passers:.1f}, "
            f"median {report.median_attempts_passers:.1f}",
        )
    if report.mean_fuel_passers is not None:
        summary.add_row(
            "fuel (passers)", f"mean {report.mean_fuel_passers:,.0f} units"
        )
    if report.cost_estimate_usd is not None:
        summary.add_row("est. cost", f"${report.cost_estimate_usd:.2f}")
    console.print(summary)

    per_task = Table(title="Per-task results", show_lines=False)
    per_task.add_column("task")
    per_task.add_column("status")
    per_task.add_column("reason")
    per_task.add_column("attempts", justify="right")
    per_task.add_column("fuel", justify="right")
    per_task.add_column("codes")
    for r in report.results:
        status = "[green]PASS[/green]" if r.passed else "[red]FAIL[/red]"
        # I-OPS-17: failure_codes entries are dicts; join codes for display.
        codes_str = ", ".join(sorted({e["code"] for e in r.failure_codes}))[:40]
        per_task.add_row(
            r.task_id,
            status,
            r.reason,
            str(r.attempts_used),
            f"{r.total_fuel_consumed:,}",
            codes_str,
        )
    console.print(per_task)

    if report.top_failure_codes:
        codes_tbl = Table(title="Top failure codes", show_header=True)
        codes_tbl.add_column("code")
        codes_tbl.add_column("count", justify="right")
        for code, count in report.top_failure_codes:
            codes_tbl.add_row(code, str(count))
        console.print(codes_tbl)

    if report.by_difficulty:
        diff_tbl = Table(title="By difficulty band")
        diff_tbl.add_column("difficulty")
        diff_tbl.add_column("passed", justify="right")
        diff_tbl.add_column("failed", justify="right")
        for band, stats in sorted(report.by_difficulty.items()):
            diff_tbl.add_row(band, str(stats["passed"]), str(stats["failed"]))
        console.print(diff_tbl)


def write_json(report: RunReport, path: Path) -> None:
    """Write the full report (including every TaskResult) as JSON.
    Atomic write via .tmp + rename."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(report.model_dump_json(indent=2), encoding="utf-8")
    tmp.replace(path)


def write_markdown(report: RunReport, path: Path) -> None:
    """Write a human-readable narrative with the failure-code histogram."""
    path.parent.mkdir(parents=True, exist_ok=True)
    lines: list[str] = []
    lines.append(f"# sigil-bench run `{report.run_id}`")
    lines.append("")
    lines.append(f"- **Model**: {report.model}")
    lines.append(f"- **Started**: {report.started_at}")
    lines.append(f"- **Finished**: {report.finished_at}")
    lines.append(
        f"- **Pass rate**: {report.passed}/{report.total_tasks} "
        f"({report.pass_rate * 100:.1f}%)"
    )
    if report.mean_attempts_passers is not None:
        lines.append(
            f"- **Attempts among passers**: "
            f"mean {report.mean_attempts_passers:.2f}, "
            f"median {report.median_attempts_passers}"
        )
    if report.mean_fuel_passers is not None:
        lines.append(
            f"- **Fuel consumed among passers**: "
            f"mean {report.mean_fuel_passers:,.0f}"
        )
    if report.cost_estimate_usd is not None:
        lines.append(f"- **Pre-flight cost estimate**: ${report.cost_estimate_usd:.2f}")

    lines.append("")
    lines.append("## Per-task results")
    lines.append("")
    lines.append("| Task | Status | Reason | Attempts | Fuel | Codes |")
    lines.append("|---|---|---|---:|---:|---|")
    for r in report.results:
        status = "✅ PASS" if r.passed else "❌ FAIL"
        codes_str = ", ".join(sorted({e["code"] for e in r.failure_codes})) or "—"
        lines.append(
            f"| `{r.task_id}` | {status} | `{r.reason}` | "
            f"{r.attempts_used} | {r.total_fuel_consumed:,} | {codes_str} |"
        )

    if report.top_failure_codes:
        lines.append("")
        lines.append("## Top failure codes")
        lines.append("")
        lines.append("| Code | Count |")
        lines.append("|---|---:|")
        for code, count in report.top_failure_codes:
            lines.append(f"| `{code}` | {count} |")

    if report.by_difficulty:
        lines.append("")
        lines.append("## By difficulty band")
        lines.append("")
        lines.append("| Difficulty | Passed | Failed |")
        lines.append("|---|---:|---:|")
        for band, stats in sorted(report.by_difficulty.items()):
            lines.append(f"| {band} | {stats['passed']} | {stats['failed']} |")

    if report.by_reason:
        lines.append("")
        lines.append("## By outcome reason")
        lines.append("")
        lines.append("| Reason | Count |")
        lines.append("|---|---:|")
        for reason, count in sorted(report.by_reason.items()):
            lines.append(f"| `{reason}` | {count} |")

    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text("\n".join(lines) + "\n", encoding="utf-8")
    tmp.replace(path)


def _full_file_sha256(header_dict: dict, body_lines: list[str]) -> str:
    """Compute the transcript's integrity hash via the zeroed-field
    protocol (per **I-OPS-16** / **AP-OPS-13**).

    Why the protocol exists: the header itself contains the hash field.
    Naively, hash(header + body) is a chicken-and-egg problem because
    the header carries the hash. The standard fix:

      1. Replace the `transcript_sha256` field in the header with a
         fixed-length placeholder (64 zero hex chars).
      2. Serialize header_with_zeros + body using deterministic JSON
         (`separators=(",", ":")`, `sort_keys=True`).
      3. Hash the resulting byte stream.

    Validation reverses step 1-3: read header, extract claimed_hash,
    replace with placeholder, serialize, hash, compare.

    The protocol covers BOTH the header (closing the run_id-spoofing
    window where a tamperer could swap `created_by_run_id` without
    invalidating a body-only hash) AND the body. Both writer and
    validator MUST use identical serialization parameters.
    """
    header_with_zero = dict(header_dict)
    header_with_zero["transcript_sha256"] = _ZEROED_HASH_PLACEHOLDER
    header_line = json.dumps(
        header_with_zero, separators=(",", ":"), sort_keys=True
    )
    body = "\n".join(body_lines)
    if body:
        body = body + "\n"
    full = header_line + "\n" + body
    return hashlib.sha256(full.encode("utf-8")).hexdigest()


def write_transcript(
    result: TaskResult, dir_path: Path, run_id: str
) -> Path:
    """Write `<task_id>.jsonl` — first line is the integrity HEADER
    (schema_version, created_by_run_id, transcript_sha256), then one
    JSON object per attempt + per forge_result + a final summary.
    Atomic via .tmp + rename, so a partial write can't poison a
    resumed run.

    Per I24: `transcript_sha256` covers the body (everything after
    the header). `created_by_run_id` lets `--resume` reject transcripts
    written by a different run (e.g. someone manually copied a
    transcript file from another run dir into this one)."""
    dir_path.mkdir(parents=True, exist_ok=True)
    out_path = dir_path / f"{result.task_id}.jsonl"
    # Body lines use sort_keys=True so the byte stream is deterministic
    # for the integrity hash. Phase 6a-2 / I-OPS-16 — hash protocol
    # requires byte-stable serialization on BOTH write and validate.
    body_lines: list[str] = []
    for attempt in result.attempts:
        body_lines.append(
            json.dumps(
                {"kind": "attempt", **attempt.model_dump()},
                separators=(",", ":"),
                sort_keys=True,
            )
        )
    for fr in result.forge_results:
        body_lines.append(
            json.dumps(
                {"kind": "forge_result", **fr.model_dump()},
                separators=(",", ":"),
                sort_keys=True,
            )
        )
    body_lines.append(
        json.dumps(
            {
                "kind": "summary",
                "task_id": result.task_id,
                "passed": result.passed,
                "reason": result.reason,
                "attempts_used": result.attempts_used,
                "total_fuel_consumed": result.total_fuel_consumed,
                "failure_codes": result.failure_codes,
                "harness_error": result.harness_error,
            },
            separators=(",", ":"),
            sort_keys=True,
        )
    )
    header_dict = {
        "kind": "header",
        "schema_version": TRANSCRIPT_SCHEMA_VERSION,
        "created_by_run_id": run_id,
        "transcript_sha256": _ZEROED_HASH_PLACEHOLDER,  # placeholder; replaced below
    }
    # Compute hash with the placeholder in place (the protocol).
    header_dict["transcript_sha256"] = _full_file_sha256(header_dict, body_lines)
    header_line = json.dumps(
        header_dict, separators=(",", ":"), sort_keys=True
    )
    all_lines = [header_line] + body_lines
    tmp = out_path.with_suffix(out_path.suffix + ".tmp")
    tmp.write_text("\n".join(all_lines) + "\n", encoding="utf-8")
    tmp.replace(out_path)
    return out_path


def transcript_exists(task_id: str, dir_path: Path) -> bool:
    """True iff a complete transcript for `task_id` already exists in
    `dir_path`. Used by `--resume` to skip already-finished tasks.
    Does NOT validate integrity — call `validate_transcript_integrity`
    for that."""
    return (dir_path / f"{task_id}.jsonl").is_file()


def validate_transcript_integrity(
    task_id: str, dir_path: Path, expected_run_id: str
) -> None:
    """Validate that `<task_id>.jsonl` was written by `expected_run_id`,
    has the current schema version, and that the body bytes match the
    recorded sha256. Raises `TranscriptIntegrityError` on any mismatch.

    Used by `--resume` BEFORE skipping the task — without this, a
    silently-corrupted transcript would be treated as authoritative.
    Per I24."""
    path = dir_path / f"{task_id}.jsonl"
    if not path.is_file():
        raise TranscriptIntegrityError(
            f"transcript missing: {path}"
        )
    raw = path.read_text(encoding="utf-8")
    if not raw.endswith("\n"):
        raise TranscriptIntegrityError(
            f"transcript {path}: trailing newline missing — possible truncation"
        )
    lines = raw.split("\n")
    # Trailing empty entry from the trailing \n.
    if lines and lines[-1] == "":
        lines = lines[:-1]
    if not lines:
        raise TranscriptIntegrityError(f"transcript {path}: empty file")
    try:
        header = json.loads(lines[0])
    except json.JSONDecodeError as exc:
        raise TranscriptIntegrityError(
            f"transcript {path}: header line not valid JSON ({exc})"
        ) from exc
    if header.get("kind") != "header":
        raise TranscriptIntegrityError(
            f"transcript {path}: first line is not a header (kind={header.get('kind')!r}); "
            "this transcript predates the integrity layer (I24) and cannot be resumed safely. "
            "Re-run the task without --resume."
        )
    schema = header.get("schema_version")
    if schema != TRANSCRIPT_SCHEMA_VERSION:
        raise TranscriptIntegrityError(
            f"transcript {path}: schema_version={schema!r} but harness expects "
            f"{TRANSCRIPT_SCHEMA_VERSION}; refusing to resume mismatched transcripts"
        )
    written_by = header.get("created_by_run_id")
    if written_by != expected_run_id:
        raise TranscriptIntegrityError(
            f"transcript {path}: written by run {written_by!r}, but resuming "
            f"run is {expected_run_id!r}. Cross-run transcript reuse rejected."
        )
    # Phase 6a-2 / I-OPS-16: validate via the zeroed-field protocol.
    # Replace the claimed hash with the placeholder, recompute, compare.
    # This catches header tampering AND body tampering uniformly —
    # the prior body-only protocol let `created_by_run_id` be swapped
    # without invalidating the hash (AP-OPS-13 — the chicken-and-egg
    # problem the spec called out).
    expected_hash = header.get("transcript_sha256")
    if not isinstance(expected_hash, str) or len(expected_hash) != 64:
        raise TranscriptIntegrityError(
            f"transcript {path}: header transcript_sha256 missing or "
            f"wrong length (expected 64 hex chars, got {expected_hash!r})"
        )
    actual_hash = _full_file_sha256(header, lines[1:])
    if expected_hash != actual_hash:
        raise TranscriptIntegrityError(
            f"transcript {path}: integrity hash mismatch "
            f"(header={expected_hash[:12]}…, computed={actual_hash[:12]}…). "
            "Either the header was tampered with (changing run_id, etc.) or "
            "the body was modified. Refusing to consume."
        )


def load_transcript_summary(
    task_id: str, dir_path: Path
) -> dict[str, Any] | None:
    """Read the summary line from a task's transcript. Returns None if
    the file is missing or malformed. Skips the integrity header — for
    integrity validation use `validate_transcript_integrity`."""
    path = dir_path / f"{task_id}.jsonl"
    if not path.is_file():
        return None
    try:
        for line in path.read_text(encoding="utf-8").splitlines():
            obj = json.loads(line)
            if obj.get("kind") == "summary":
                return obj
    except (json.JSONDecodeError, OSError):
        return None
    return None


def load_run_id(run_dir: Path) -> str | None:
    """Read the previously-assigned run_id from `<run_dir>/run_id.txt`.
    Returns None if the file doesn't exist (legacy run, or fresh dir)."""
    p = run_dir / "run_id.txt"
    if not p.is_file():
        return None
    return p.read_text(encoding="utf-8").strip()


def write_run_id(run_dir: Path, run_id: str) -> None:
    """Persist `run_id` to `<run_dir>/run_id.txt`. Called once at run
    start so `--resume` can recover the same id."""
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "run_id.txt").write_text(run_id + "\n", encoding="utf-8")


# ── Run dir helpers ──────────────────────────────────────────────────────


def new_run_dir(settings: Settings) -> Path:
    """Build `bench/runs/<UTC ISO timestamp>/` and ensure it exists."""
    ts = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    out = settings.repo_root / "bench" / "runs" / ts
    out.mkdir(parents=True, exist_ok=True)
    return out
