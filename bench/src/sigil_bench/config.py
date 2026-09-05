"""Runtime configuration for sigil-bench: paths, env vars, model defaults."""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from pathlib import Path

from dotenv import load_dotenv

# Anthropic Sonnet 4.6 pricing as of 2026-05; update if you bump the model.
# Used by the pre-flight cost estimator only — actual billing comes from Anthropic.
DEFAULT_MODEL = "claude-sonnet-4-6"
PRICING_PER_MTOK_USD = {
    # input_uncached, input_cache_write (1.25x in), input_cache_hit (0.1x in), output
    "claude-sonnet-4-6": {
        "input": 3.00,
        "cache_write": 3.75,
        "cache_hit": 0.30,
        "output": 15.00,
    },
    # diagnostics-axes a9 iter 14: the weaker-model arm. Haiku 4.5 pricing.
    "claude-haiku-4-5": {
        "input": 1.00,
        "cache_write": 1.25,
        "cache_hit": 0.10,
        "output": 5.00,
    },
}


@dataclass
class Settings:
    repo_root: Path
    mcp_binary: Path
    api_key: str | None
    model: str = DEFAULT_MODEL
    max_attempts: int = 5
    fuel_budget: int = 100_000
    # diagnostics-axes a9: the A/B variable. "full" = the complete
    # errors-as-API envelope (default; preserves `run` behavior); "bare"
    # = `[CODE]: message` only. The `compare` subcommand sets it per arm.
    diagnostic_detail: str = "full"


def find_repo_root(start: Path | None = None) -> Path:
    """Walk up from `start` (default: this file) until we find the workspace
    Cargo.toml. Sigil's workspace root has `[workspace]`; reject other Cargo
    files we might encounter on the way up.
    """
    here = (start or Path(__file__)).resolve()
    for ancestor in [here, *here.parents]:
        cargo = ancestor / "Cargo.toml"
        if cargo.is_file() and "[workspace]" in cargo.read_text(encoding="utf-8"):
            return ancestor
    raise RuntimeError(
        f"could not find workspace Cargo.toml walking up from {here}"
    )


def default_mcp_binary(repo_root: Path) -> Path:
    """Resolve the sigil-mcp binary path. Prefer release, fall back to debug.
    Append .exe on Windows."""
    suffix = ".exe" if sys.platform == "win32" else ""
    release = repo_root / "target" / "release" / f"sigil-mcp{suffix}"
    if release.is_file():
        return release
    return repo_root / "target" / "debug" / f"sigil-mcp{suffix}"


def load_settings() -> Settings:
    """Build a Settings from .env + environment overrides."""
    load_dotenv()  # no-op if .env is missing
    repo_root = find_repo_root()
    binary_override = os.environ.get("SIGIL_MCP_BINARY")
    mcp_binary = (
        Path(binary_override) if binary_override else default_mcp_binary(repo_root)
    )
    diagnostic_detail = os.environ.get("BENCH_DIAGNOSTIC_DETAIL", "full")
    if diagnostic_detail not in ("full", "bare"):
        raise ValueError(
            f"BENCH_DIAGNOSTIC_DETAIL must be 'full' or 'bare', got {diagnostic_detail!r}"
        )
    return Settings(
        repo_root=repo_root,
        mcp_binary=mcp_binary,
        api_key=os.environ.get("ANTHROPIC_API_KEY"),
        model=os.environ.get("BENCH_MODEL", DEFAULT_MODEL),
        max_attempts=int(os.environ.get("BENCH_MAX_ATTEMPTS", "5")),
        fuel_budget=int(os.environ.get("BENCH_FUEL_BUDGET", "100000")),
        diagnostic_detail=diagnostic_detail,
    )
