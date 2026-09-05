"""Stub-only integration tests for the agent loop runner.

Drives `run_task` with deterministic stub generators against a synthetic
minimal task. Verifies:
  * OracleStub-style generator passes in 1 attempt.
  * BrokenStub exhausts at max_attempts with T060 in failure_codes.
  * RecoverStub passes in 2 attempts (broken first, working second).

The stubs return strings the tests own — no dependency on tools/*.sigil
content drift. Spawns the real sigil-mcp binary so the runner exercises
the full wire (subprocess + stdio JSON-RPC). Skipped if the binary is
not built.
"""

from __future__ import annotations

from typing import Any

import pytest

from sigil_bench.config import load_settings
from sigil_bench.generator import BrokenStub, OracleStub, RecoverStub
from sigil_bench.mcp_client import SigilMCP
from sigil_bench.runner import resolve_input_value, run_task
from sigil_bench.tasks import Difficulty, TaskInput, TaskSpec, load_tasks

# ── Fixtures ──────────────────────────────────────────────────────────


@pytest.fixture(scope="module")
def settings():
    return load_settings()


@pytest.fixture(scope="module")
def binary_path(settings):
    if not settings.mcp_binary.is_file():
        pytest.skip(
            f"sigil-mcp binary not found at {settings.mcp_binary}. "
            "Run `cargo build --release -p sigil-mcp` first."
        )
    return settings.mcp_binary


@pytest.fixture
def mcp_factory(binary_path):
    """Returns a zero-arg callable that the runner uses to spawn a
    fresh MCP subprocess for the task. Each call yields a new
    SigilMCP usable as a context manager."""

    def factory() -> SigilMCP:
        return SigilMCP.spawn(binary_path)

    return factory


# A trivial tool that returns 0 (so output_bytes == 0, output_text == "").
# Owned by this test file — not coupled to any tools/*.sigil corpus file.
SYNTHETIC_SOURCE = (
    "module tool; "
    "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }"
)

SYNTHETIC_EXPECTED = {"empty": ""}


@pytest.fixture
def synthetic_task() -> TaskSpec:
    """Minimal task spec the runner can drive end-to-end. `source_path`
    is unused because the test supplies `expected_outputs` directly to
    `run_task`, bypassing the reference-source ground-truth path."""
    return TaskSpec(
        id="synthetic_zero",
        source_path="unused/synthetic.sigil",
        difficulty=Difficulty.TRIVIAL,
        description="Return 0 from tool_main; output_text is empty.",
        signature="pub fn tool_main(input_ptr: i64, input_len: i64) -> i64",
        inputs=[TaskInput(name="empty", value="")],
        expected_output_strategy="literal",
        expected_outputs=SYNTHETIC_EXPECTED,
        fuel_budget=100_000,
    )


class _ConstantGenerator:
    """Returns the same source on every call — the stub-equivalent of
    `OracleStub` but parameterized inline so tests own the source string."""

    name = "ConstantGenerator"

    def __init__(self, source: str) -> None:
        self._source = source

    def generate(self, task: TaskSpec, transcript: list[dict[str, Any]]) -> str:
        return self._source


# ── Tests ─────────────────────────────────────────────────────────────


def test_empty_input_remains_literal(settings):
    assert resolve_input_value("", settings.repo_root) == ""


def test_clean_source_passes_in_one_attempt(
    synthetic_task, mcp_factory, settings
):
    """Generator returns a clean source on the first try; loop exits
    after one check, forge succeeds, output matches."""
    gen = _ConstantGenerator(SYNTHETIC_SOURCE)

    result = run_task(
        synthetic_task,
        gen,
        mcp_factory,
        settings.repo_root,
        expected_outputs=SYNTHETIC_EXPECTED,
    )

    assert result.passed, (
        f"expected pass; got reason={result.reason}, "
        f"harness_error={result.harness_error}"
    )
    assert result.reason == "passed"
    assert result.attempts_used == 1
    assert result.final_source == SYNTHETIC_SOURCE
    assert result.attempts[0].failure_codes == []
    assert len(result.forge_results) == 1
    forge = result.forge_results[0]
    assert forge.passed
    assert forge.input_name == "empty"
    assert forge.output_text == ""
    assert forge.expected_output == ""


def test_sha256_oracle_passes_full_reference_path(
    mcp_factory, settings
):
    """The committed SHA-256 oracle must compose with crypto and forge."""
    task = load_tasks(
        settings.repo_root / "bench" / "tasks",
        only=["task032_sha256_hex"],
    )[0]
    result = run_task(
        task,
        OracleStub(task.resolve_source(settings.repo_root)),
        mcp_factory,
        settings.repo_root,
    )

    assert result.passed, (
        f"expected SHA-256 oracle pass; reason={result.reason}, "
        f"harness_error={result.harness_error}, codes={result.failure_codes}"
    )
    outputs = {outcome.input_name: outcome.output_text for outcome in result.forge_results}
    assert outputs["empty"] == (
        "e3b0c44298fc1c149afbf4c8996fb924"
        "27ae41e4649b934ca495991b7852b855"
    )
    assert outputs["hello"] == (
        "2cf24dba5fb0a30e26e83b2ac5b9e29e"
        "1b161e5c1fa7425e73043362938b9824"
    )
    assert len(outputs["longer"] or "") == 64


def test_broken_source_exhausts_attempts_with_T060(
    synthetic_task, mcp_factory, settings
):
    """BrokenStub returns check-failing source every call; runner gives
    up at max_attempts with T060 (undefined local) in the code histogram."""
    gen = BrokenStub()

    result = run_task(
        synthetic_task,
        gen,
        mcp_factory,
        settings.repo_root,
        max_attempts=3,
        expected_outputs=SYNTHETIC_EXPECTED,
    )

    assert not result.passed
    assert result.reason == "exhausted_attempts"
    assert result.attempts_used == 3
    assert len(result.attempts) == 3
    assert result.final_source is None
    # Phase 6a-2 / I-OPS-17: failure_codes is `list[dict]` with `code` field.
    codes_only = [e["code"] for e in result.failure_codes]
    assert "T060" in codes_only, (
        f"expected T060 in failure codes, got {result.failure_codes}"
    )
    # Every attempt logged its own T060.
    for attempt in result.attempts:
        attempt_codes = [e["code"] for e in attempt.failure_codes]
        assert "T060" in attempt_codes
    # Forge stage was never reached.
    assert result.forge_results == []


def test_recover_passes_in_two_attempts(
    synthetic_task, mcp_factory, settings
):
    """RecoverStub: first call broken (T060), second call clean. Runner
    converges, attempts_used=2, forge passes."""
    gen = RecoverStub(then_source=SYNTHETIC_SOURCE)

    result = run_task(
        synthetic_task,
        gen,
        mcp_factory,
        settings.repo_root,
        expected_outputs=SYNTHETIC_EXPECTED,
    )

    assert result.passed, (
        f"expected pass; got reason={result.reason}, "
        f"harness_error={result.harness_error}"
    )
    assert result.reason == "passed"
    assert result.attempts_used == 2
    assert result.final_source == SYNTHETIC_SOURCE
    # Phase 6a-2 / I-OPS-17: structured failure_codes.
    first_attempt_codes = [e["code"] for e in result.attempts[0].failure_codes]
    assert "T060" in first_attempt_codes
    assert result.attempts[1].failure_codes == []
    assert len(result.forge_results) == 1
    assert result.forge_results[0].passed


def test_ground_truth_mismatch_is_distinct_from_forge_failure(
    synthetic_task, mcp_factory, settings
):
    """If forge succeeds but the output doesn't match expected, the
    reason is `ground_truth_mismatch`, not `forge_failed`."""
    gen = _ConstantGenerator(SYNTHETIC_SOURCE)

    # Synthetic source produces output_text="" but we claim expected="nope".
    result = run_task(
        synthetic_task,
        gen,
        mcp_factory,
        settings.repo_root,
        expected_outputs={"empty": "nope"},
    )

    assert not result.passed
    assert result.reason == "ground_truth_mismatch"
    assert result.attempts_used == 1
    assert len(result.forge_results) == 1
    forge = result.forge_results[0]
    assert not forge.passed
    assert forge.output_text == ""
    assert forge.expected_output == "nope"
    assert forge.forge_envelope.get("status") == "ok"


def test_harness_error_on_mcp_failure(synthetic_task, settings):
    """If the MCP factory raises, the runner catches it and returns a
    harness_error TaskResult (not an unhandled exception)."""

    class _BoomFactory:
        def __call__(self) -> SigilMCP:
            raise RuntimeError("simulated spawn failure")

    gen = _ConstantGenerator(SYNTHETIC_SOURCE)
    result = run_task(
        synthetic_task,
        gen,
        _BoomFactory(),
        settings.repo_root,
        expected_outputs=SYNTHETIC_EXPECTED,
    )

    assert not result.passed
    assert result.reason == "harness_error"
    assert result.harness_error is not None
    assert "simulated spawn failure" in result.harness_error
