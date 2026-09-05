"""Command-line entry for the agentic convergence experiment.

Examples:
    # Offline smoke test (no API, no cost) — exercises the whole loop.
    python -m sigil_bench.agentic --dry-run --tasks task001_echo

    # Live run: default Claude+GPT roster over every task, retry cap 6.
    python -m sigil_bench.agentic --models default --runs 1 --max-attempts 6

    # Pick models + tasks explicitly; cross-provider via OpenRouter passthrough.
    python -m sigil_bench.agentic --models claude-sonnet,gpt-4o,or:deepseek/deepseek-chat \\
        --tasks task001_echo,task011_palindrome,task020_rot13
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from sigil_bench.config import default_mcp_binary, find_repo_root

from . import registry
from .experiment import ExperimentConfig, run_experiment


def _parse_models(value: str) -> list[str]:
    value = value.strip()
    if value in ("default", ""):
        return list(registry.DEFAULT_ROSTER)
    if value == "all":
        return list(registry.REGISTRY)
    if value == "available":
        return [k for k, s in registry.REGISTRY.items() if registry.is_available(s)]
    return [m.strip() for m in value.split(",") if m.strip()]


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="sigil-agentic",
        description="Run the SIGIL Tool Generation prompt over a task corpus across models, "
        "logging every sigil_check call and recording convergence metrics.",
    )
    p.add_argument("--models", default="default",
                   help="comma list of model keys, or 'default' / 'all' / 'available'. "
                        "Passthrough form 'provider:model_id' (e.g. or:deepseek/deepseek-chat).")
    p.add_argument("--tasks", default="",
                   help="comma list of task ids (default: all tasks in the tasks dir).")
    p.add_argument("--runs", type=int, default=1, help="runs per (model,task) cell.")
    p.add_argument("--max-attempts", type=int, default=6,
                   help="retry cap: max failing sigil_check calls before giving up (5-7 typical).")
    p.add_argument("--max-model-turns", type=int, default=16, help="hard cap on model turns per cell.")
    p.add_argument("--max-tool-calls", type=int, default=40, help="hard cap on total tool calls per cell.")
    p.add_argument("--fuel", type=int, default=100_000, help="default forge fuel budget.")
    p.add_argument("--env-file", default=None,
                   help="path to the .env with provider keys (default: the repo-root .env).")
    p.add_argument("--out", default=None, help="output dir for runs (default: <repo>/bench/runs).")
    p.add_argument("--tasks-dir", default=None, help="tasks dir (default: <repo>/bench/tasks).")
    p.add_argument("--mcp-binary", default=None, help="path to sigil-mcp (default: target/{release,debug}).")
    p.add_argument("--request-timeout", type=float, default=120.0, help="per model request timeout (s).")
    p.add_argument("--anthropic-thinking", action="store_true",
                   help="enable Anthropic ADAPTIVE thinking (Opus 4.6+/Sonnet 4.6) for "
                        "reasoning parity with gpt-5.x. Depth set by --effort.")
    p.add_argument("--effort", default="high", choices=["low", "medium", "high", "xhigh", "max"],
                   help="effort level when --anthropic-thinking is on (default: high).")
    p.add_argument("--no-compose", action="store_true", help="do NOT link stdlib for stdlib_imports tasks.")
    p.add_argument("--no-verify", action="store_true", help="skip the authoritative final-source forge check.")
    p.add_argument("--check-capability-use", action="store_true",
                   help="cheat detector: for grant-requiring tasks, flag a 'correct' source whose output "
                        "is unchanged when the grant is revoked (it never used the capability).")
    p.add_argument("--dry-run", action="store_true", help="use a scripted stub model (no API, no cost).")
    p.add_argument("--list-models", action="store_true", help="print the registry + availability and exit.")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    repo_root = find_repo_root()

    env_file = Path(args.env_file) if args.env_file else None
    loaded = registry.load_keys(env_file)

    if args.list_models:
        print(f"env file loaded: {loaded}")
        print(f"{'KEY':<22} {'PROVIDER':<12} {'AVAILABLE':<10} MODEL_ID")
        for key, spec in registry.REGISTRY.items():
            avail = "yes" if registry.is_available(spec) else "no"
            print(f"{key:<22} {spec.provider:<12} {avail:<10} {spec.api_model_id}")
        print(f"\ndefault roster: {', '.join(registry.DEFAULT_ROSTER)}")
        return 0

    mcp_binary = Path(args.mcp_binary) if args.mcp_binary else default_mcp_binary(repo_root)
    if not mcp_binary.is_file():
        print(f"error: sigil-mcp binary not found at {mcp_binary}.\n"
              "Build it with: cargo build --release -p sigil-mcp", file=sys.stderr)
        return 2

    tasks_dir = Path(args.tasks_dir) if args.tasks_dir else repo_root / "bench" / "tasks"
    out_dir = Path(args.out) if args.out else repo_root / "bench" / "runs"
    task_ids = [t.strip() for t in args.tasks.split(",") if t.strip()] or None

    cfg = ExperimentConfig(
        repo_root=repo_root,
        mcp_binary=mcp_binary,
        tasks_dir=tasks_dir,
        out_dir=out_dir,
        models=_parse_models(args.models),
        task_ids=task_ids,
        runs=args.runs,
        max_check_attempts=args.max_attempts,
        max_model_turns=args.max_model_turns,
        max_total_tool_calls=args.max_tool_calls,
        fuel=args.fuel,
        compose_stdlib=not args.no_compose,
        verify_final=not args.no_verify,
        check_capability_use=args.check_capability_use,
        dry_run=args.dry_run,
        request_timeout=args.request_timeout,
        anthropic_thinking=args.anthropic_thinking,
        anthropic_effort=args.effort,
        env_file_loaded=str(loaded) if loaded else None,
    )
    run_experiment(cfg)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
