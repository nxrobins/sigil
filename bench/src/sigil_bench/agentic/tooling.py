"""Model-facing tool schemas + the executor that runs them against sigil-mcp.

`model_tool_specs()` are the three tools the "SIGIL Tool Generation" prompt
advertises. `MCPToolExecutor` runs each model tool call against the real
`sigil-mcp` binary and tracks the convergence metrics:

  * every `sigil_check` call: pass/fail, diagnostic codes, attempt number
  * the retry cap (N failing checks with no pass → stop, outcome `hit_cap`)
  * grants the model passes to `sigil_forge`
  * the last source that passed `sigil_check` (for an authoritative,
    harness-run correctness verdict against the task's ground truth)

Tasks that declare `stdlib_imports` have the stdlib modules linked in (via
`compose_with_stdlib`) before the source reaches the compiler — the same path
the on-disk reference takes — so a `use sigil::fs;` actually resolves.
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    # Imported lazily at call time inside `model_tool_specs` to avoid a
    # module-load import cycle (backends imports from this module); the
    # TYPE_CHECKING alias lets the forward-ref annotation resolve for linters.
    from .backends import ToolSpec

from sigil_bench.compose import compose_with_stdlib
from sigil_bench.mcp_client import SigilMCP
from sigil_bench.runner import (
    capture_ground_truth,
    extract_codes,
    resolve_grants,
    resolve_input_value,
)
from sigil_bench.tasks import TaskSpec

# ── Tool schemas (mirror crates/sigil-mcp/src/main.rs) ───────────────────────


def model_tool_specs() -> list["ToolSpec"]:
    from .backends import ToolSpec

    return [
        ToolSpec(
            name="sigil_check",
            description=(
                "Compile a SIGIL source string and return a structured JSON "
                "diagnostic envelope. On success `status` is \"ok\". On failure "
                "`status` is \"error\" and `diagnostics` is a non-empty array of "
                "errors with stable codes (e.g. T060, R001), messages, and fix "
                "hints. Call this in a loop to drive iterative source generation."
            ),
            input_schema={
                "type": "object",
                "properties": {
                    "source": {
                        "type": "string",
                        "description": "SIGIL source, including the `module <name>;` declaration.",
                    }
                },
                "required": ["source"],
            },
        ),
        ToolSpec(
            name="sigil_forge",
            description=(
                "Compile a SIGIL tool module and execute it once in an ephemeral "
                "Wasmtime sandbox. The source must export "
                "`pub fn tool_main(input_ptr: i64, input_len: i64) -> i64`. On "
                "success `data` includes `output_text`, `output_bytes`, and "
                "`fuel_consumed`. Network and filesystem access require explicit "
                "grants — without them, FFI calls return 403."
            ),
            input_schema={
                "type": "object",
                "properties": {
                    "source": {"type": "string", "description": "SIGIL tool source."},
                    "input": {
                        "type": "string",
                        "description": "Input bytes passed to the tool. Defaults to empty.",
                    },
                    "fuel": {
                        "type": "integer",
                        "description": "Fuel budget for execution. Defaults to 100000.",
                    },
                    "grants": {
                        "type": "object",
                        "description": (
                            "Optional I/O grants. `fs`/`fs_write`: filesystem roots; "
                            "`net`: host patterns the tool may reach; `time`: e.g. "
                            "[\"wall\"]; `random`: e.g. [\"secure\"]."
                        ),
                        "properties": {
                            "fs": {"type": "array", "items": {"type": "string"}},
                            "fs_write": {"type": "array", "items": {"type": "string"}},
                            "net": {"type": "array", "items": {"type": "string"}},
                            "time": {"type": "array", "items": {"type": "string"}},
                            "random": {"type": "array", "items": {"type": "string"}},
                        },
                    },
                },
                "required": ["source"],
            },
        ),
        ToolSpec(
            name="sigil_lookup_error",
            description=(
                "Look up a SIGIL diagnostic code (e.g. T060, R001) and return its "
                "title, default fix hint, category, and doc URL."
            ),
            input_schema={
                "type": "object",
                "properties": {
                    "code": {"type": "string", "description": "A SIGIL diagnostic code, e.g. T060."}
                },
                "required": ["code"],
            },
        ),
    ]


# ── Per-call log + executor state ────────────────────────────────────────────


@dataclass
class ToolCallRecord:
    index: int
    name: str
    ok: bool | None = None
    check_attempt: int | None = None
    codes: list[str] = field(default_factory=list)
    grants: dict[str, Any] | None = None
    forge_input: str | None = None
    forge_status: str | None = None
    output_text: str | None = None
    note: str | None = None
    error: str | None = None


@dataclass
class ExecControl:
    stop: bool = False
    reason: str | None = None


class MCPToolExecutor:
    """Executes the model's tool calls against a live `SigilMCP` and tracks
    convergence metrics. One instance per cell (model × task × run)."""

    def __init__(
        self,
        mcp: SigilMCP,
        task: TaskSpec,
        repo_root: Path,
        *,
        max_check_attempts: int,
        fuel: int,
        compose_stdlib: bool = True,
        expected_outputs: dict[str, str] | None = None,
    ) -> None:
        self._mcp = mcp
        self._task = task
        self._repo_root = repo_root
        self._max_check_attempts = max_check_attempts
        self._fuel = fuel
        self._compose_stdlib = compose_stdlib and bool(task.stdlib_imports)
        # Optional pre-captured ground truth (deterministic per task) so the
        # final-source verdict doesn't recompute it once per cell.
        self._expected_outputs = expected_outputs

        # ── metrics state ──
        self.check_attempts = 0
        self.first_check_ok: bool | None = None
        self.attempts_to_success: int | None = None
        self.any_check_passed = False
        self.hit_cap = False
        self.code_counts: Counter[str] = Counter()
        self.grants_requested: list[dict[str, Any]] = []
        self.forge_calls = 0
        self.forge_fuel_consumed = 0
        self.lookup_calls = 0
        self.tool_log: list[ToolCallRecord] = []
        self.last_passing_source: str | None = None
        self._last_passing_composed: str | None = None
        self._call_index = 0

    # ── helpers ──
    def _compose(self, source: str) -> str:
        if not self._compose_stdlib:
            return source
        return compose_with_stdlib(source, list(self._task.stdlib_imports), self._repo_root).text

    @staticmethod
    def _envelope_text(env: dict[str, Any]) -> str:
        return json.dumps(env, indent=2, sort_keys=True)

    # ── dispatch ──
    def execute(self, name: str, args: dict[str, Any]) -> tuple[str, ExecControl]:
        self._call_index += 1
        try:
            if name == "sigil_check":
                return self._do_check(args)
            if name == "sigil_forge":
                return self._do_forge(args)
            if name == "sigil_lookup_error":
                return self._do_lookup(args)
            rec = ToolCallRecord(self._call_index, name, ok=False, error="unknown tool")
            self.tool_log.append(rec)
            return (
                json.dumps({"status": "error", "message": f"unknown tool {name!r}"}),
                ExecControl(),
            )
        except Exception as e:  # noqa: BLE001 — tool boundary; surface to the model
            rec = ToolCallRecord(self._call_index, name, ok=False, error=f"{type(e).__name__}: {e}")
            self.tool_log.append(rec)
            return (
                json.dumps({"status": "error", "message": f"harness error running {name}: {e}"}),
                ExecControl(),
            )

    def _do_check(self, args: dict[str, Any]) -> tuple[str, ExecControl]:
        source = args.get("source")
        if not isinstance(source, str) or not source.strip():
            rec = ToolCallRecord(self._call_index, "sigil_check", ok=False, error="missing source")
            self.tool_log.append(rec)
            return (
                json.dumps({"status": "error", "message": "sigil_check requires a non-empty `source` string"}),
                ExecControl(),
            )
        try:
            composed = self._compose(source)
        except Exception as e:  # noqa: BLE001 — stdlib link failure is a failed check
            self.check_attempts += 1
            if self.first_check_ok is None:
                self.first_check_ok = False
            self.tool_log.append(
                ToolCallRecord(
                    self._call_index, "sigil_check", ok=False,
                    check_attempt=self.check_attempts, error=f"stdlib link failed: {e}",
                )
            )
            env_err = {
                "status": "error",
                "command": "check",
                "message": f"failed to link stdlib modules for this source: {e}",
                "diagnostics": [],
            }
            if not self.any_check_passed and self.check_attempts >= self._max_check_attempts:
                self.hit_cap = True
                return self._envelope_text(env_err), ExecControl(stop=True, reason="hit_cap")
            return self._envelope_text(env_err), ExecControl()
        env = self._mcp.check(composed)
        self.check_attempts += 1
        ok = env.get("status") == "ok"
        codes = [c["code"] for c in extract_codes(env)]
        self.code_counts.update(codes)
        if self.first_check_ok is None:
            self.first_check_ok = ok
        if ok:
            self.last_passing_source = source
            self._last_passing_composed = composed
            if not self.any_check_passed:
                self.any_check_passed = True
                self.attempts_to_success = self.check_attempts
        self.tool_log.append(
            ToolCallRecord(
                self._call_index, "sigil_check", ok=ok,
                check_attempt=self.check_attempts, codes=codes,
            )
        )
        # Retry cap: N failing checks with no pass yet → stop the cell.
        if not ok and not self.any_check_passed and self.check_attempts >= self._max_check_attempts:
            self.hit_cap = True
            return self._envelope_text(env), ExecControl(stop=True, reason="hit_cap")
        return self._envelope_text(env), ExecControl()

    def _do_forge(self, args: dict[str, Any]) -> tuple[str, ExecControl]:
        source = args.get("source")
        if not isinstance(source, str) or not source.strip():
            rec = ToolCallRecord(self._call_index, "sigil_forge", ok=False, error="missing source")
            self.tool_log.append(rec)
            return (
                json.dumps({"status": "error", "message": "sigil_forge requires a non-empty `source` string"}),
                ExecControl(),
            )
        self.forge_calls += 1
        raw_grants = args.get("grants") if isinstance(args.get("grants"), dict) else {}
        self.grants_requested.append(dict(raw_grants))
        resolved = resolve_grants(raw_grants, self._repo_root) if raw_grants else None
        fuel = int(args.get("fuel", self._fuel) or self._fuel)
        forge_input = args.get("input", "")
        if not isinstance(forge_input, str):
            forge_input = str(forge_input)
        composed = self._compose(source)
        env = self._mcp.forge(composed, input=forge_input, fuel=fuel, grants=resolved)
        status = env.get("status")
        output_text = env.get("data", {}).get("output_text") if status == "ok" else None
        if status == "ok":
            self.forge_fuel_consumed += int(env.get("data", {}).get("fuel_consumed", 0) or 0)
        self.tool_log.append(
            ToolCallRecord(
                self._call_index, "sigil_forge", ok=(status == "ok"),
                grants=dict(raw_grants), forge_input=forge_input,
                forge_status=status, output_text=output_text,
            )
        )
        return self._envelope_text(env), ExecControl()

    def _do_lookup(self, args: dict[str, Any]) -> tuple[str, ExecControl]:
        code = args.get("code")
        self.lookup_calls += 1
        if not isinstance(code, str) or not code:
            rec = ToolCallRecord(self._call_index, "sigil_lookup_error", ok=False, error="missing code")
            self.tool_log.append(rec)
            return (
                json.dumps({"status": "error", "message": "sigil_lookup_error requires a `code` string"}),
                ExecControl(),
            )
        env = self._mcp.lookup_error(code)
        self.tool_log.append(
            ToolCallRecord(self._call_index, "sigil_lookup_error", ok=(env.get("status") == "ok"), note=code)
        )
        return self._envelope_text(env), ExecControl()

    # ── authoritative final-source verdict (harness-run, not model-run) ──
    def verify_final_source(self, *, check_capability_use: bool = False) -> dict[str, Any]:
        """Run the LAST source that passed `sigil_check` through `sigil_forge`
        over every task input, with the task's *required* grants, and compare
        to ground truth. Independent of whatever the model itself forged.

        When `check_capability_use` is True and the task requires grants, a
        correct source is ALSO re-run with the grants revoked. If its output is
        unchanged (so the capability was never used), `capability_unused` is set
        — strong evidence the "solution" hardcoded the answer rather than doing
        the required I/O. See `redteam.grant_necessity_probe`."""
        if self._last_passing_composed is None:
            return {"ran": False, "reason": "no passing source"}
        try:
            expected = self._expected_outputs or capture_ground_truth(
                self._task, self._repo_root, self._mcp
            )
            grants = resolve_grants(self._task.required_grants.to_mcp(), self._repo_root)
            per_input: list[dict[str, Any]] = []
            all_passed = True
            for inp in self._task.inputs:
                value = resolve_input_value(inp.value, self._repo_root)
                env = self._mcp.forge(
                    self._last_passing_composed, input=value, fuel=self._task.fuel_budget, grants=grants
                )
                got = env.get("data", {}).get("output_text") if env.get("status") == "ok" else None
                want = expected.get(inp.name)
                passed = env.get("status") == "ok" and got == want
                all_passed = all_passed and passed
                per_input.append({"input": inp.name, "passed": passed, "status": env.get("status")})
            result: dict[str, Any] = {"ran": True, "all_passed": all_passed, "per_input": per_input}

            # Opt-in cheat detector: a correct, grant-requiring source that
            # produces identical output with the grant revoked never used the
            # capability → likely a hardcoded answer.
            if check_capability_use and all_passed and self._task.required_grants.to_mcp():
                capability_unused = True
                for inp in self._task.inputs:
                    value = resolve_input_value(inp.value, self._repo_root)
                    g_env = self._mcp.forge(
                        self._last_passing_composed, input=value,
                        fuel=self._task.fuel_budget, grants=grants,
                    )
                    n_env = self._mcp.forge(
                        self._last_passing_composed, input=value,
                        fuel=self._task.fuel_budget, grants=None,
                    )
                    g_out = g_env.get("data", {}).get("output_text") if g_env.get("status") == "ok" else None
                    n_ok = n_env.get("status") == "ok"
                    n_out = n_env.get("data", {}).get("output_text") if n_ok else None
                    if not (n_ok and g_out == n_out):
                        capability_unused = False
                result["capability_unused"] = capability_unused
            return result
        except Exception as e:  # noqa: BLE001
            return {"ran": False, "reason": f"{type(e).__name__}: {e}"}
