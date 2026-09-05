"""sigil-bench command-line interface.

Subcommands:
    sigil-bench version              Print package version and exit.
    sigil-bench run [opts]           Run the benchmark.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import uuid
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from rich.console import Console

from . import __version__
from .config import Settings, load_settings
from .generator import (
    AnthropicGenerator,
    Generator,
    OracleStub,
)
from .mcp_client import SigilMCP
from .retention import prune_old_run_dirs
from .runner import TaskResult, run_task
from .scoring import (
    TranscriptIntegrityError,
    aggregate,
    compare_conditions,
    estimate_cost,
    load_run_id,
    new_run_dir,
    render_console,
    transcript_exists,
    validate_transcript_integrity,
    write_comparison_markdown,
    write_json,
    write_markdown,
    write_run_id,
    write_transcript,
)
from .tasks import TaskSpec, load_tasks


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="sigil-bench",
        description="AutoForge benchmark harness for the Sigil compiler/runtime.",
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("version", help="Print the sigil-bench version and exit.")

    run = sub.add_parser("run", help="Run the benchmark.")
    run.add_argument(
        "--task",
        action="append",
        metavar="TASK_ID",
        help="Run only the named task(s). Repeatable. Default: all tasks.",
    )
    run.add_argument(
        "--dry-run",
        action="store_true",
        help="Use the OracleStub generator (no LLM calls). Verifies the harness pipeline.",
    )
    run.add_argument(
        "--resume",
        metavar="RUN_TS",
        help="Resume an existing run by directory name (skips tasks whose transcripts already exist).",
    )
    run.add_argument(
        "--max-attempts",
        type=int,
        help="Override the default per-task attempt cap (default: 5).",
    )
    run.add_argument(
        "--max-tokens",
        type=int,
        default=4096,
        help="Per-call max output tokens for the LLM (default: 4096).",
    )
    run.add_argument(
        "--yes",
        action="store_true",
        help="Skip the pre-flight cost-estimate confirmation prompt.",
    )

    # ── compare (diagnostics-axes a9: A/B full-envelope vs bare) ─────────
    compare = sub.add_parser(
        "compare",
        help="A/B: run every task under `full` and `bare` diagnostics and "
        "measure whether the richer envelope speeds agent convergence.",
    )
    compare.add_argument(
        "--task",
        action="append",
        metavar="TASK_ID",
        help="Run only the named task(s). Repeatable. Default: all tasks.",
    )
    compare.add_argument(
        "--variable",
        choices=["detail", "edits"],
        default="detail",
        help="A/B variable: `detail` = bare vs full envelope (default); "
        "`edits` = full with suggested_edits OFF vs ON (the redundancy test).",
    )
    compare.add_argument(
        "--repeats",
        type=int,
        default=5,
        help="Repeats per arm (temp~1.0 noise floor; default 5).",
    )
    compare.add_argument(
        "--max-attempts",
        type=int,
        help="Override the per-task attempt cap (default: 5).",
    )
    compare.add_argument(
        "--model",
        metavar="MODEL_ID",
        help="Override BENCH_MODEL for this A/B (e.g. claude-haiku-4-5 for the "
        "weaker-model arm). Default: claude-sonnet-4-6.",
    )
    compare.add_argument(
        "--max-tokens",
        type=int,
        default=4096,
        help="Per-call max output tokens for the LLM (default: 4096).",
    )
    compare.add_argument(
        "--max-cost-usd",
        type=float,
        default=25.0,
        help="Hard ceiling on the pre-flight estimate (2 arms x repeats). "
        "Abort if exceeded. Default: $25.",
    )
    compare.add_argument(
        "--dry-run",
        action="store_true",
        help="Use OracleStub for both arms (no LLM calls). Exercises the "
        "full A/B orchestration; both arms are identical so the verdict is "
        "'no_significant_difference' (the null path).",
    )
    compare.add_argument(
        "--yes",
        action="store_true",
        help="Skip the pre-flight cost-estimate confirmation prompt.",
    )

    # Phase 6a-2: --keep-last-runs on `run` subcommand for run-dir retention.
    run.add_argument(
        "--keep-last-runs",
        type=int,
        default=10,
        help="Auto-prune older bench/runs/* dirs before starting. "
        "Skips dirs with a `lock` sentinel or mtime within 6h "
        "(I-OPS-19). Default: keep last 10.",
    )

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    if args.cmd == "version":
        print(f"sigil-bench {__version__}")
        return 0

    if args.cmd == "run":
        return _cmd_run(args)

    if args.cmd == "compare":
        return _cmd_compare(args)

    parser.error(f"unknown subcommand: {args.cmd}")
    return 2  # unreachable; argparse exits


# ── run ──────────────────────────────────────────────────────────────────


def _cmd_run(args: argparse.Namespace) -> int:
    # legacy_windows=False routes through the modern Win32 API so unicode
    # in rich output (box characters, status glyphs) survives cp1252 stdout.
    console = Console(legacy_windows=False)
    settings = load_settings()

    if args.max_attempts is not None:
        settings.max_attempts = args.max_attempts

    # Resolve tasks
    tasks_dir = settings.repo_root / "bench" / "tasks"
    try:
        tasks = load_tasks(tasks_dir, only=args.task)
    except (FileNotFoundError, ValueError) as e:
        console.print(f"[red]error:[/red] {e}")
        return 2

    # Resolve run directory (new vs resume)
    if args.resume:
        run_dir = settings.repo_root / "bench" / "runs" / args.resume
        if not run_dir.is_dir():
            console.print(f"[red]error:[/red] resume dir not found: {run_dir}")
            return 2
        # Phase 5a-4 / I24: a resumed run REUSES the original run_id so
        # transcript-integrity checks know which run owns the existing
        # transcripts. Legacy runs that pre-date the integrity layer
        # have no run_id.txt — refuse to resume them rather than write
        # mixed-schema transcripts into the same dir.
        existing_run_id = load_run_id(run_dir)
        if existing_run_id is None:
            console.print(
                f"[red]error:[/red] {run_dir} has no run_id.txt; this run "
                "predates the integrity layer (Phase 5a-4) and cannot be "
                "resumed safely. Start a new run instead."
            )
            return 2
        run_id = existing_run_id
    else:
        # Phase 6a-2 / I-OPS-19: prune older run dirs BEFORE creating
        # the new one, so we don't accidentally count it among the
        # "kept" set. Skips dirs with `lock` sentinel or recent mtime.
        keep_n = getattr(args, "keep_last_runs", 10)
        if keep_n > 0:
            prune_old_run_dirs(settings.repo_root / "bench" / "runs", keep_n)
        run_dir = new_run_dir(settings)
        run_id = uuid.uuid4().hex
        write_run_id(run_dir, run_id)

    transcripts_dir = run_dir / "transcripts"

    # Build generator
    if args.dry_run:
        generator: Generator | None = None  # built per-task (oracle needs source path)
        console.print("[dim]dry-run mode: using OracleStub for every task[/dim]")
    else:
        generator = _build_anthropic_generator(
            settings, console, args.max_tokens
        )
        if generator is None:
            return 2

    # Pre-flight cost estimate (live mode only)
    cost_estimate = None
    if not args.dry_run and isinstance(generator, AnthropicGenerator):
        cost_estimate = _maybe_show_cost(
            generator, tasks, settings, console, args.yes
        )
        if cost_estimate is None:
            return 1  # user declined

    # MCP factory: spawn fresh subprocess per task.
    if not settings.mcp_binary.is_file():
        console.print(
            f"[red]error:[/red] sigil-mcp binary not found at {settings.mcp_binary}. "
            "Run `cargo build --release -p sigil-mcp`."
        )
        return 2

    def mcp_factory() -> SigilMCP:
        return SigilMCP.spawn(settings.mcp_binary)

    # Execute
    started = datetime.now(UTC)
    results: list[TaskResult] = []
    skipped = 0
    for task in tasks:
        if args.resume and transcript_exists(task.id, transcripts_dir):
            # Phase 5a-4 / I24: validate integrity BEFORE skipping. A
            # corrupted or cross-run transcript must NOT be silently
            # treated as authoritative.
            try:
                validate_transcript_integrity(task.id, transcripts_dir, run_id)
            except TranscriptIntegrityError as e:
                console.print(f"[red]error:[/red] {e}")
                return 2
            console.print(f"[dim]skip[/dim] {task.id} (already in run)")
            skipped += 1
            # Try to reload the result if needed for aggregation. For
            # simplicity, exclude resumed tasks from this run's report —
            # the report covers only tasks executed in this invocation.
            continue

        per_task_gen = (
            OracleStub(task.resolve_source(settings.repo_root))
            if args.dry_run
            else generator  # type: ignore[assignment]
        )
        assert per_task_gen is not None

        console.print(f"[cyan]>[/cyan] running {task.id} ({task.difficulty.value}) ...")
        result = run_task(
            task,
            per_task_gen,
            mcp_factory,
            settings.repo_root,
            max_attempts=settings.max_attempts,
        )
        write_transcript(result, transcripts_dir, run_id)
        results.append(result)
        status = "[green]PASS[/green]" if result.passed else "[red]FAIL[/red]"
        console.print(
            f"  {status} {result.reason} "
            f"(attempts={result.attempts_used}, fuel={result.total_fuel_consumed:,})"
        )

    finished = datetime.now(UTC)

    # Filter tasks parallel to results (only those actually executed).
    executed_task_ids = {r.task_id for r in results}
    executed_tasks = [t for t in tasks if t.id in executed_task_ids]

    if not results:
        console.print("[yellow]no tasks executed (all skipped via --resume)[/yellow]")
        return 0

    report = aggregate(
        results,
        executed_tasks,
        run_id=run_dir.name,
        started_at=started,
        finished_at=finished,
        model=settings.model if not args.dry_run else "OracleStub",
        cost_estimate_usd=cost_estimate.total_max_usd if cost_estimate else None,
    )

    write_json(report, run_dir / "results.json")
    write_markdown(report, run_dir / "report.md")
    render_console(report, console)
    console.print(
        f"\n[dim]wrote {run_dir / 'results.json'} and {run_dir / 'report.md'}[/dim]"
    )
    if skipped:
        console.print(f"[dim]({skipped} task(s) skipped via --resume)[/dim]")

    return 0 if report.failed == 0 else 1


# ── helpers ─────────────────────────────────────────────────────────────


def _build_anthropic_generator(
    settings: Settings,
    console: Console,
    max_tokens: int,
    detail: str = "full",
    include_suggested_edits: bool = True,
) -> AnthropicGenerator | None:
    if not settings.api_key:
        console.print(
            "[red]error:[/red] ANTHROPIC_API_KEY not set. "
            "Either export it, drop it in `bench/.env`, or pass `--dry-run`."
        )
        return None
    try:
        from anthropic import Anthropic
    except ImportError as e:
        console.print(f"[red]error:[/red] anthropic SDK not installed: {e}")
        return None
    client = Anthropic(api_key=settings.api_key)
    return AnthropicGenerator(
        client=client,
        model=settings.model,
        repo_root=settings.repo_root,
        max_tokens=max_tokens,
        detail=detail,
        include_suggested_edits=include_suggested_edits,
    )


def _maybe_show_cost(
    generator: AnthropicGenerator,
    tasks: list[TaskSpec],
    settings: Settings,
    console: Console,
    auto_yes: bool,
) -> Any:
    """Compute and display the pre-flight cost estimate. Returns the
    CostEstimate on confirmation, or None if the user declined."""
    console.print("[dim]counting tokens for pre-flight cost estimate ...[/dim]")
    try:
        system_tokens = generator.count_system_tokens()
        # Average over all tasks' attempt-1 user messages.
        user_counts = [
            generator.count_user_tokens_for(t) for t in tasks
        ]
    except Exception as e:  # noqa: BLE001 — surface API failures cleanly
        console.print(f"[yellow]warn:[/yellow] token count failed ({e}); skipping estimate")
        return type("Stub", (), {"total_max_usd": None})()

    avg_user = sum(user_counts) // len(user_counts) if user_counts else 0
    estimate = estimate_cost(
        model=settings.model,
        system_tokens=system_tokens,
        avg_user_tokens=avg_user,
        max_output_tokens=4096,
        n_tasks=len(tasks),
        max_attempts=settings.max_attempts,
    )

    console.print(
        f"\n[bold]Pre-flight cost estimate[/bold] "
        f"(worst-case, {len(tasks)} tasks × max {settings.max_attempts} attempts):"
    )
    console.print(f"  system tokens (cached):     {estimate.system_tokens:,}")
    console.print(f"  avg user tokens / call:     {estimate.avg_user_tokens:,}")
    console.print(f"  max output tokens / call:   {estimate.max_output_tokens:,}")
    console.print(f"  cache writes:               {estimate.cache_writes}")
    console.print(f"  cache hits:                 {estimate.cache_hits}")
    console.print(
        f"  cost breakdown:             "
        f"cache_write=${estimate.cost_cache_write_usd:.3f}  "
        f"cache_hit=${estimate.cost_cache_hit_usd:.3f}  "
        f"user=${estimate.cost_user_input_usd:.3f}  "
        f"output=${estimate.cost_output_usd:.3f}"
    )
    console.print(f"  [bold]total max: ${estimate.total_max_usd:.2f}[/bold]")

    if auto_yes:
        return estimate

    try:
        reply = input("\nProceed? [y/N] ").strip().lower()
    except EOFError:
        reply = ""
    if reply not in ("y", "yes"):
        console.print("[yellow]aborted[/yellow]")
        return None
    return estimate


# ── compare (diagnostics-axes a9: A/B full-envelope vs bare) ─────────────


def _git_sha(repo_root: Path) -> str:
    """HEAD commit, recorded in the prereg + every artifact (E6). The two
    arms MUST share this — compare_conditions panics otherwise."""
    try:
        out = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=True,
        )
        return out.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def _estimate_one_run(
    generator: AnthropicGenerator,
    tasks: list[TaskSpec],
    settings: Settings,
    console: Console,
    max_output_tokens: int,
) -> Any:
    """One-arm one-repeat cost estimate. Returns None on token-count
    failure — the caller fails closed (never spend without an estimate).
    `max_output_tokens` mirrors the run's --max-tokens so the ceiling gate
    reflects the actual output cap (output dominates the bill)."""
    console.print("[dim]counting tokens for pre-flight cost estimate ...[/dim]")
    try:
        system_tokens = generator.count_system_tokens()
        user_counts = [generator.count_user_tokens_for(t) for t in tasks]
    except Exception as e:  # noqa: BLE001 — surface API failures cleanly
        console.print(f"[yellow]warn:[/yellow] token count failed ({e}); cannot gate cost")
        return None
    avg_user = sum(user_counts) // len(user_counts) if user_counts else 0
    return estimate_cost(
        model=settings.model,
        system_tokens=system_tokens,
        avg_user_tokens=avg_user,
        max_output_tokens=max_output_tokens,
        n_tasks=len(tasks),
        max_attempts=settings.max_attempts,
    )


def _cmd_compare(args: argparse.Namespace) -> int:
    console = Console(legacy_windows=False)
    settings = load_settings()

    if args.max_attempts is not None:
        settings.max_attempts = args.max_attempts
    if args.model is not None:
        settings.model = args.model
    if args.repeats < 1:
        console.print("[red]error:[/red] --repeats must be >= 1")
        return 2

    tasks_dir = settings.repo_root / "bench" / "tasks"
    try:
        tasks = load_tasks(tasks_dir, only=args.task)
    except (FileNotFoundError, ValueError) as e:
        console.print(f"[red]error:[/red] {e}")
        return 2

    if not settings.mcp_binary.is_file():
        console.print(
            f"[red]error:[/red] sigil-mcp binary not found at {settings.mcp_binary}. "
            "Run `cargo build --release -p sigil-mcp`."
        )
        return 2

    live = not args.dry_run

    # Arm specification by --variable (C2: exactly one variable per A/B).
    #   detail: bare envelope vs full envelope (the a9 experiment).
    #   edits:  full envelope with suggested_edits OFF vs ON (the redundancy
    #           experiment) — both arms full; only the fix line differs.
    if args.variable == "edits":
        arm_specs = [("off", "full", False), ("on", "full", True)]
        variable_name = "suggested_edits"
        experiment_kind = "redundancy_restatement"
    else:
        arm_specs = [("bare", "bare", True), ("full", "full", True)]
        variable_name = "diagnostic_detail"
        experiment_kind = "envelope"
    control_name, treatment_name = arm_specs[0][0], arm_specs[1][0]

    # Per-arm generators built once (live) so the cache stays warm across
    # repeats; dry-run builds per-task OracleStubs inside the loop.
    generators: dict[str, AnthropicGenerator] = {}
    if live:
        for arm_name, detail, include_edits in arm_specs:
            gen = _build_anthropic_generator(
                settings,
                console,
                args.max_tokens,
                detail=detail,
                include_suggested_edits=include_edits,
            )
            if gen is None:
                return 2
            generators[arm_name] = gen
        # Cost ceiling: 2 arms × K repeats × one-run estimate (E: cost ceiling).
        est = _estimate_one_run(
            generators[treatment_name], tasks, settings, console, args.max_tokens
        )
        if est is None:
            return 2
        total = est.total_max_usd * 2 * args.repeats
        console.print(
            f"\n[bold]A/B pre-flight[/bold]: 2 arms x {args.repeats} repeats x "
            f"{len(tasks)} tasks -> est. max [bold]${total:.2f}[/bold] "
            f"(ceiling ${args.max_cost_usd:.2f})"
        )
        if total > args.max_cost_usd:
            console.print(
                f"[red]error:[/red] estimate ${total:.2f} exceeds ceiling "
                f"${args.max_cost_usd:.2f}; raise --max-cost-usd or lower --repeats."
            )
            return 1
        if not args.yes:
            try:
                reply = input("Proceed? [y/N] ").strip().lower()
            except EOFError:
                reply = ""
            if reply not in ("y", "yes"):
                console.print("[yellow]aborted[/yellow]")
                return 1

    # Run dir + preregistration written BEFORE the first LLM call (E5).
    ts = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    run_dir = settings.repo_root / "bench" / "runs" / f"{ts}-ab"
    run_dir.mkdir(parents=True, exist_ok=True)
    run_id = uuid.uuid4().hex
    write_run_id(run_dir, run_id)

    sha = _git_sha(settings.repo_root)
    model = settings.model if live else "OracleStub"
    decision_rule = {
        "pass_delta_threshold": 2,
        "attempts_margin": 1,
        "global_min_wins": 3,
        "global_win_ratio": 2,
    }
    prereg = {
        "kind": "ab_preregistration",
        "variable": variable_name,
        "experiment_kind": experiment_kind,
        "control_arm": control_name,
        "treatment_arm": treatment_name,
        "model": model,
        "live": live,
        "git_sha": sha,
        "repeats": args.repeats,
        "max_attempts": settings.max_attempts,
        "task_ids": [t.id for t in tasks],
        "primary_metric": "pass_rate + median_attempts_passers (within-task paired)",
        "decision_rule": decision_rule,
    }
    (run_dir / "preregistration.json").write_text(
        json.dumps(prereg, indent=2, sort_keys=True), encoding="utf-8"
    )
    console.print(f"[dim]wrote preregistration.json -> {run_dir.name}[/dim]")

    def mcp_factory() -> SigilMCP:
        return SigilMCP.spawn(settings.mcp_binary)

    transcripts_root = run_dir / "transcripts"
    results_by_arm: dict[str, list[TaskResult]] = {control_name: [], treatment_name: []}

    # Interleave arms per repeat (E6): balances cache/order effects.
    for k in range(1, args.repeats + 1):
        arm_order = (
            [control_name, treatment_name] if k % 2 == 1 else [treatment_name, control_name]
        )
        for arm in arm_order:
            for task in tasks:
                per_task_gen: Generator = (
                    OracleStub(task.resolve_source(settings.repo_root))
                    if args.dry_run
                    else generators[arm]
                )
                console.print(f"[cyan]>[/cyan] r{k} ({arm}) {task.id} ...")
                result = run_task(
                    task,
                    per_task_gen,
                    mcp_factory,
                    settings.repo_root,
                    max_attempts=settings.max_attempts,
                )
                write_transcript(result, transcripts_root / arm / f"r{k}", run_id)
                results_by_arm[arm].append(result)
                status = "[green]PASS[/green]" if result.passed else "[red]FAIL[/red]"
                console.print(f"    {status} (attempts={result.attempts_used})")

    # Score (E3/E4/E8) + commensurability guard (E6).
    base_meta = {
        "variable": variable_name,
        "model": model,
        "live": live,
        "git_sha": sha,
        "repeats": args.repeats,
        "max_attempts": settings.max_attempts,
        "task_ids": [t.id for t in tasks],
    }
    report = compare_conditions(
        results_by_arm[control_name],
        results_by_arm[treatment_name],
        control_meta={**base_meta, "arm": control_name},
        treatment_meta={**base_meta, "arm": treatment_name},
        arms_complete=True,
        experiment_kind=experiment_kind,
    )

    (run_dir / "ab_summary.json").write_text(
        report.model_dump_json(indent=2), encoding="utf-8"
    )
    write_comparison_markdown(report, run_dir / "report.md")
    console.print(
        f"\n[bold]verdict:[/bold] {report.verdict}  "
        f"(treatment {report.wins['treatment']} / control {report.wins['control']} / "
        f"tie {report.wins['tie']})"
    )
    console.print(f"[dim]wrote {run_dir / 'ab_summary.json'} and report.md[/dim]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
