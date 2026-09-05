"""The agent loop: generate → check → iterate on diagnostics → forge.

The runner orchestrates a single task end-to-end. It does NOT spawn the
LLM (that's the Generator's job) and it does NOT spawn the MCP server
(it accepts a factory, so each task gets a fresh process).
"""

from __future__ import annotations

from collections.abc import Callable
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, Field, field_validator

from .compose import ComposedSource, compose_with_stdlib
from .generator import Generator
from .mcp_client import MCPError, SigilMCP
from .tasks import TaskSpec

# ── Result models ─────────────────────────────────────────────────────────


def _normalize_failure_code_entry(entry: object) -> dict[str, str]:
    """Phase 6a-2 / I-OPS-17: normalize a `failure_codes` entry to the
    structured shape `{"code": str, "detail": str}`. Accepts:
    - Bare string (legacy): becomes `{"code": <s>, "detail": ""}`
    - Dict with at least `code`: passes through (detail defaults to "")

    Raises ValueError on any other shape — a list of mixed types is a
    bug, not data we should accept silently."""
    if isinstance(entry, str):
        return {"code": entry, "detail": ""}
    if isinstance(entry, dict) and "code" in entry:
        code = str(entry["code"])
        if ":" in code:
            raise ValueError(
                "failure_codes entry `code` MUST NOT contain ':' "
                "(would re-introduce the embedded-delimiter parser hazard "
                "Phase 6a-2 / I-OPS-17 prohibits): " + repr(entry)
            )
        return {"code": code, "detail": str(entry.get("detail", ""))}
    raise ValueError(f"failure_codes entry has bad shape: {entry!r}")


def _normalize_failure_codes(entries: list[object]) -> list[dict[str, str]]:
    """Apply `_normalize_failure_code_entry` to every entry, preserving
    order. Used by Pydantic field validators on Attempt and TaskResult."""
    return [_normalize_failure_code_entry(e) for e in entries]


class Attempt(BaseModel):
    attempt_no: int
    source: str
    check_envelope: dict[str, Any]
    # Phase 6a-2 / I-OPS-17: structured failure codes. Entries are
    # `{"code": "T060", "detail": "<context>"}`. Old `list[str]` data
    # is auto-migrated by the validator.
    failure_codes: list[dict[str, str]] = Field(default_factory=list)
    # diagnostics-axes a9 iter 13: lines the prepended stdlib added ahead of
    # this attempt's source. The check_envelope's diagnostic line numbers are
    # in COMPOSED coordinates; subtract this to get the agent's source-space
    # line. 0 for tasks with no stdlib_imports. Additive — old transcripts
    # default to 0 (no remap), preserving their meaning.
    source_line_offset: int = 0

    @field_validator("failure_codes", mode="before")
    @classmethod
    def _migrate_failure_codes(cls, v: object) -> list[dict[str, str]]:
        if not isinstance(v, list):
            raise ValueError(f"failure_codes must be a list, got {type(v).__name__}")
        return _normalize_failure_codes(v)


class ForgeOutcome(BaseModel):
    input_name: str
    passed: bool
    output_text: str | None
    expected_output: str | None
    forge_envelope: dict[str, Any]


class TaskResult(BaseModel):
    task_id: str
    passed: bool
    reason: Literal[
        "passed",
        "exhausted_attempts",
        "compile_error_no_attempts",
        "forge_failed",
        "ground_truth_mismatch",
        # Phase 5a-4 / I10: parse-aware verifier rejected the source
        # because it didn't `use` one or more declared stdlib_imports.
        "stdlib_not_used",
        "harness_error",
    ]
    attempts_used: int
    attempts: list[Attempt] = Field(default_factory=list)
    forge_results: list[ForgeOutcome] = Field(default_factory=list)
    final_source: str | None = None
    total_fuel_consumed: int = 0
    # Phase 6a-2 / I-OPS-17: same structured shape as Attempt.
    failure_codes: list[dict[str, str]] = Field(default_factory=list)
    harness_error: str | None = None
    # Phase 5a-4: the stdlib_hash that was bound to this task's
    # composed source, for cross-referencing with the AnthropicGenerator
    # cache key. Empty for tasks with no stdlib_imports.
    stdlib_hash: str = ""
    # Per AP4: when the verifier rejected, list the imports the agent
    # was supposed to bring in but didn't. Phase 6a-2: ALSO surfaced
    # in failure_codes as `{"code": "STDLIB_MISSING", "detail": "fs,json"}`
    # so the operator can grep transcripts by code without reaching
    # for this side field.
    stdlib_missing: list[str] = Field(default_factory=list)

    @field_validator("failure_codes", mode="before")
    @classmethod
    def _migrate_failure_codes(cls, v: object) -> list[dict[str, str]]:
        if not isinstance(v, list):
            raise ValueError(f"failure_codes must be a list, got {type(v).__name__}")
        return _normalize_failure_codes(v)


# ── Path / grant resolution ───────────────────────────────────────────────


def resolve_input_value(value: str, repo_root: Path) -> str:
    """Inputs that name on-disk fixtures (paths starting with `bench/` or
    other repo-relative prefixes) get resolved to absolute. Pure-literal
    inputs (text, URLs, etc.) pass through unchanged."""
    if not value:
        return value
    candidate = Path(value)
    if candidate.is_absolute():
        return value
    # Only resolve to a path when the value names an actual FILE. The old
    # `exists()` check mis-resolved an empty value (`repo_root / "" ==
    # repo_root`, which exists as a directory) to the repo-root path — silently
    # feeding the repo-root path as the input bytes instead of empty. Requiring a
    # non-empty value AND `is_file()` keeps fixture paths resolving while
    # leaving empty/literal text inputs untouched.
    repo_relative = repo_root / value
    if value and repo_relative.is_file():
        return str(repo_relative.resolve())
    return value


def resolve_grants(
    grants: dict[str, list[str]], repo_root: Path
) -> dict[str, list[str]]:
    """Filesystem grant roots get resolved to absolute (and canonicalized
    via Path.resolve so the runtime's canonicalize() check matches).
    Network / time / random / secret grant kinds pass through unchanged.

    `kv` / `kv_write` entries are `namespace=path` pairs: the PATH half is a store root and needs the
    same absolutise+canonicalise treatment as `fs`, while the `namespace=` prefix must survive intact.
    Omitting these two kinds silently dropped the grant, so a KV task forged UNGRANTED and trapped
    with `-403` (R803) — which is why `rlx_kv_get`'s reference "failed forge" and `export_forge_sft`
    quietly skipped it, leaving the KV stratum empty despite the runtime supporting kv_get/kv_put.
    """
    out: dict[str, list[str]] = {}
    for fs_key in ("fs", "fs_write"):
        if fs_key in grants:
            resolved: list[str] = []
            for root in grants[fs_key]:
                p = Path(root)
                if not p.is_absolute():
                    p = repo_root / root
                if p.exists():
                    p = p.resolve()
                resolved.append(str(p))
            out[fs_key] = resolved
    for kv_key in ("kv", "kv_write"):
        if kv_key in grants:
            resolved_kv: list[str] = []
            for entry in grants[kv_key]:
                ns, sep, root = entry.partition("=")
                if not sep:  # bare namespace, no store root to resolve
                    resolved_kv.append(entry)
                    continue
                p = Path(root)
                if not p.is_absolute():
                    p = repo_root / root
                if p.exists():
                    p = p.resolve()
                resolved_kv.append(f"{ns}={p}")
            out[kv_key] = resolved_kv
    for passthrough_key in ("net", "time", "random", "secret"):
        if passthrough_key in grants:
            out[passthrough_key] = list(grants[passthrough_key])
    return out


# ── Diagnostic-code extraction ────────────────────────────────────────────


def extract_codes(check_envelope: dict[str, Any]) -> list[dict[str, str]]:
    """Phase 6a-2 / I-OPS-17: returns structured failure entries.
    Each diagnostic becomes `{"code": "T060", "detail": "<message>"}`.
    The detail carries the diagnostic message so downstream consumers
    don't need to re-parse the envelope to get a human-readable
    summary."""
    if check_envelope.get("status") != "error":
        return []
    out: list[dict[str, str]] = []
    for d in check_envelope.get("diagnostics", []):
        if not isinstance(d, dict) or "code" not in d:
            continue
        out.append({
            "code": str(d["code"]),
            "detail": str(d.get("message", "")),
        })
    return out


# ── Ground truth ──────────────────────────────────────────────────────────


def attach_driver(source: str, task: TaskSpec, repo_root: Path) -> str:
    """Append a module-shaped task's fixed driver to `source`.

    ONE definition, called on BOTH the reference path (`capture_ground_truth`) and the
    candidate path. Assembling the program differently on those two paths is the I-OPS-4 trap
    this module already warns about: ground truth captured against different bytes than the
    candidate runs on yields a silently-wrong verdict, not an error.

    Classic tasks have `driver_path == ""` and are returned unchanged.
    """
    if not task.driver_path:
        return source
    driver = (repo_root / task.driver_path).read_text(encoding="utf-8")
    return source.rstrip() + "\n\n" + driver.lstrip()


def capture_ground_truth(
    task: TaskSpec,
    repo_root: Path,
    mcp: SigilMCP,
    *,
    # Forwarded to compose_with_stdlib for candidate evaluation.
    override_modules: dict[str, str] | None = None,
) -> dict[str, str]:
    """Run the reference source through forge once per input; capture
    `output_text` per input as the ground truth. For `literal`-strategy
    tasks, return the spec's pre-baked expected outputs verbatim.

    Phase 5a-4: when the task declares `stdlib_imports`, the reference
    source is composed with stdlib before forge — same path the LLM
    source takes, so ground truth is captured against the SAME bytes
    the agent will be tested against.

    Phase 6a-1 / I-OPS-4: `override_modules` MUST flow through to the
    compose call. Without this, the evolve fitness path captures ground
    truth against the LIVE stdlib while the candidate runs against
    ITSELF — silently-wrong fitness, the canonical PR 6a-1 trap.
    """
    if task.expected_output_strategy == "literal":
        assert task.expected_outputs is not None
        return dict(task.expected_outputs)

    reference = task.resolve_source(repo_root).read_text(encoding="utf-8")
    reference = attach_driver(reference, task, repo_root)
    composed = compose_with_stdlib(
        reference, task.stdlib_imports, repo_root,
        override_modules=override_modules,
    )
    grants = resolve_grants(task.required_grants.to_mcp(), repo_root)
    expected: dict[str, str] = {}
    for inp in task.inputs:
        value = resolve_input_value(inp.value, repo_root)
        env = mcp.forge(
            composed.text, input=value, fuel=task.fuel_budget, grants=grants
        )
        if env.get("status") != "ok":
            raise RuntimeError(
                f"reference source for {task.id} failed forge on input "
                f"{inp.name!r}: {env}"
            )
        text = env.get("data", {}).get("output_text")
        if text is None:
            raise RuntimeError(
                f"reference forge for {task.id}/{inp.name} produced no output_text: {env}"
            )
        expected[inp.name] = text
    return expected


def verify_stdlib_uses(
    composed: ComposedSource,
    llm_source: str,
    expected_imports: list[str],
    mcp: SigilMCP,
) -> list[str]:
    """Phase 5a-4 / I10 / AP18: parse-aware stdlib-usage verifier.

    Calls `sigil_inspect_uses` on the COMPOSED source and confirms the
    tool module's resolved use_scope contains an entry for each
    `expected_imports` module. Comments and string literals containing
    `use sigil::...;` do NOT pass — the underlying tool only sees real
    `use` decls from the parser.

    Returns the list of MISSING modules. Empty list = all imports
    present.

    Implementation note: we inspect the composed text (stdlib + LLM
    source) so the tool module's `use` decls are visible alongside the
    stdlib modules they reference. The verifier looks at the LLM's
    module specifically — typically the one named "tool" — and checks
    its imports.
    """
    if not expected_imports:
        return []
    env = mcp.inspect_uses(composed.text)
    if env.get("status") != "ok":
        # If parse fails, the verifier can't say anything; surface as
        # missing-everything so the caller decides.
        return list(expected_imports)
    modules: dict[str, list[str]] = env.get("data", {}).get("modules", {}) or {}
    # Identify the LLM's module — the one that appears in `llm_source`
    # but NOT in any of the stdlib module sources. The most common case
    # is `module tool;`, but the LLM may name it differently. We look
    # at every module present in `modules` and union their imports;
    # then check that every expected_import is in the union. This is
    # robust to module-name variation in the LLM source.
    llm_module_imports: set[str] = set()
    stdlib_module_names = set(composed.modules_included)
    for module_name, imports in modules.items():
        if module_name in stdlib_module_names:
            continue
        llm_module_imports.update(imports)
    missing = [m for m in expected_imports if m not in llm_module_imports]
    return missing


# ── Loop runner ───────────────────────────────────────────────────────────


def run_task(
    task: TaskSpec,
    generator: Generator,
    mcp_factory: Callable[[], SigilMCP],
    repo_root: Path,
    *,
    max_attempts: int = 5,
    expected_outputs: dict[str, str] | None = None,
    # Forwarded through both composition paths for candidate evaluation.
    override_modules: dict[str, str] | None = None,
) -> TaskResult:
    """Execute one task end-to-end. Spawns its own MCP via `mcp_factory()`.

    Phase 6a-1: `override_modules`, when supplied, substitutes for the
    on-disk `stdlib/sigil/<name>.sigil` for any name in the dict. Used
    by the evolve fitness path to evaluate candidates without mutating
    the live stdlib. Per I-OPS-4 the parameter must thread through to
    BOTH the per-attempt compose AND the ground-truth capture compose;
    we do that below."""
    attempts: list[Attempt] = []
    accumulated_codes: list[str] = []
    final_source: str | None = None

    # Phase 5a-4: pre-compute the stdlib hash (constant for the lifetime
    # of this task per I5) so it can flow into TaskResult and the
    # generator's prompt-cache key. For tasks with empty stdlib_imports
    # this is a no-op: hash is the EMPTY_STDLIB_HASH sentinel.
    stdlib_modules = list(task.stdlib_imports)
    stdlib_missing: list[str] = []

    try:
        with mcp_factory() as mcp:
            # 1. Generate / check loop until clean or exhausted.
            #    Each attempt's source goes through compose_with_stdlib
            #    BEFORE check, so the agent's source sees stdlib modules
            #    in the same compilation unit.
            composed: ComposedSource | None = None
            for n in range(1, max_attempts + 1):
                source = generator.generate(
                    task, [a.model_dump() for a in attempts]
                )
                composed = compose_with_stdlib(
                    source, stdlib_modules, repo_root,
                    override_modules=override_modules,
                )
                check_env = mcp.check(composed.text)
                codes = extract_codes(check_env)
                accumulated_codes.extend(codes)
                attempts.append(
                    Attempt(
                        attempt_no=n,
                        source=source,
                        check_envelope=check_env,
                        failure_codes=codes,
                        source_line_offset=composed.stdlib_line_offset,
                    )
                )
                if check_env.get("status") == "ok":
                    final_source = source
                    break
            else:
                return TaskResult(
                    task_id=task.id,
                    passed=False,
                    reason="exhausted_attempts",
                    attempts_used=len(attempts),
                    attempts=attempts,
                    failure_codes=accumulated_codes,
                    stdlib_hash=composed.stdlib_hash if composed else "",
                )

            assert composed is not None and final_source is not None

            # 2. Phase 5a-4 / I10: parse-aware stdlib-usage verifier.
            #    Run BEFORE ground-truth capture and forge so a
            #    stdlib_not_used result short-circuits any pointless
            #    network/disk activity.
            if stdlib_modules:
                stdlib_missing = verify_stdlib_uses(
                    composed, final_source, stdlib_modules, mcp
                )
                if stdlib_missing:
                    # Phase 6a-2 / I-OPS-17: surface as a structured
                    # failure code so transcripts are greppable by `code`
                    # without parsing the side `stdlib_missing` field.
                    # Detail is sorted, comma-joined module names — no
                    # `:` allowed in the code field per the validator.
                    sorted_missing = sorted(stdlib_missing)
                    augmented_codes = list(accumulated_codes) + [{
                        "code": "STDLIB_MISSING",
                        "detail": ",".join(sorted_missing),
                    }]
                    return TaskResult(
                        task_id=task.id,
                        passed=False,
                        reason="stdlib_not_used",
                        attempts_used=len(attempts),
                        attempts=attempts,
                        final_source=final_source,
                        failure_codes=augmented_codes,
                        stdlib_hash=composed.stdlib_hash,
                        stdlib_missing=sorted_missing,
                    )

            # 3. Capture ground truth if not pre-supplied. We deliberately
            #    do NOT auto-forward `override_modules` here — that would
            #    make the GT tautological for the evolve path (candidate
            #    output trivially equals candidate output). The evolve
            #    fitness path pre-computes GT against the SEED via a
            #    separate `capture_ground_truth(..., override_modules=...)`
            #    call and passes the result via `expected_outputs=`.
            #    For non-evolve callers (no overrides anywhere), GT
            #    against disk is correct.
            if expected_outputs is None:
                expected_outputs = capture_ground_truth(task, repo_root, mcp)

            # 4. Forge the COMPOSED source (LLM + stdlib) against every
            #    input. The composed text is what the runtime executes.
            grants = resolve_grants(task.required_grants.to_mcp(), repo_root)
            forge_results: list[ForgeOutcome] = []
            total_fuel = 0
            all_passed = True
            for inp in task.inputs:
                value = resolve_input_value(inp.value, repo_root)
                env = mcp.forge(
                    composed.text,
                    input=value,
                    fuel=task.fuel_budget,
                    grants=grants,
                )
                output_text = (
                    env.get("data", {}).get("output_text")
                    if env.get("status") == "ok"
                    else None
                )
                expected = expected_outputs.get(inp.name)
                ok = env.get("status") == "ok" and output_text == expected
                if not ok:
                    all_passed = False
                if env.get("status") == "ok":
                    total_fuel += int(env["data"].get("fuel_consumed", 0))
                forge_results.append(
                    ForgeOutcome(
                        input_name=inp.name,
                        passed=ok,
                        output_text=output_text,
                        expected_output=expected,
                        forge_envelope=env,
                    )
                )

            if not all_passed:
                # Distinguish forge runtime failure from output mismatch.
                any_runtime_fail = any(
                    f.forge_envelope.get("status") != "ok" for f in forge_results
                )
                reason = "forge_failed" if any_runtime_fail else "ground_truth_mismatch"
                return TaskResult(
                    task_id=task.id,
                    passed=False,
                    reason=reason,
                    attempts_used=len(attempts),
                    attempts=attempts,
                    forge_results=forge_results,
                    final_source=final_source,
                    total_fuel_consumed=total_fuel,
                    failure_codes=accumulated_codes,
                    stdlib_hash=composed.stdlib_hash,
                )

            return TaskResult(
                task_id=task.id,
                passed=True,
                reason="passed",
                attempts_used=len(attempts),
                attempts=attempts,
                forge_results=forge_results,
                final_source=final_source,
                total_fuel_consumed=total_fuel,
                failure_codes=accumulated_codes,
                stdlib_hash=composed.stdlib_hash,
            )

    except MCPError as e:
        return TaskResult(
            task_id=task.id,
            passed=False,
            reason="harness_error",
            attempts_used=len(attempts),
            attempts=attempts,
            failure_codes=accumulated_codes,
            harness_error=f"MCP error: {e}",
        )
    except Exception as e:  # noqa: BLE001 — top-level harness boundary
        return TaskResult(
            task_id=task.id,
            passed=False,
            reason="harness_error",
            attempts_used=len(attempts),
            attempts=attempts,
            failure_codes=accumulated_codes,
            harness_error=f"{type(e).__name__}: {e}",
        )
