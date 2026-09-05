"""TaskSpec model + YAML loader.

Each task is a YAML file in `bench/tasks/`. The harness loads every
`task*.yaml` (sorted by id) and validates with Pydantic v2.
"""

from __future__ import annotations

import re
from enum import Enum
from pathlib import Path
from typing import Literal

import yaml
from pydantic import BaseModel, Field, model_validator

# Phase 5a-4 / I25: stdlib module names match `^[a-z_][a-z0-9_]*$`.
# Validated at task-load time so path-traversal characters and any other
# malformed input never reach `compose_with_stdlib`'s file I/O.
_MODULE_NAME_RE = re.compile(r"^[a-z_][a-z0-9_]*$")


class Difficulty(str, Enum):
    TRIVIAL = "trivial"
    BASIC = "basic"
    INTERMEDIATE = "intermediate"
    FFI_FS = "ffi_fs"
    FFI_NET = "ffi_net"


class TaskInput(BaseModel):
    name: str = Field(min_length=1)
    value: str = ""


class Grants(BaseModel):
    fs: list[str] = Field(default_factory=list)
    fs_write: list[str] = Field(default_factory=list)
    net: list[str] = Field(default_factory=list)
    # Phase 5a-4: time and random grant kinds (e.g. ["wall"], ["secure"]).
    # Mirror the sigil-mcp `GrantArgs` shape from PR #21. Invalid kinds
    # are silently dropped on the wire.
    time: list[str] = Field(default_factory=list)
    random: list[str] = Field(default_factory=list)
    # kv read/write grants as "NAMESPACE=DIR"; secret grants as "NAME=VALUE"
    # (the host-injected secrets http_post_secret substitutes). Mirror the
    # sigil-mcp GrantArgs so kv- and secret-using tools are gradeable.
    kv: list[str] = Field(default_factory=list)
    kv_write: list[str] = Field(default_factory=list)
    secret: list[str] = Field(default_factory=list)

    def to_mcp(self) -> dict[str, list[str]]:
        out: dict[str, list[str]] = {}
        if self.fs:
            out["fs"] = self.fs
        if self.fs_write:
            out["fs_write"] = self.fs_write
        if self.net:
            out["net"] = self.net
        if self.time:
            out["time"] = self.time
        if self.random:
            out["random"] = self.random
        if self.kv:
            out["kv"] = self.kv
        if self.kv_write:
            out["kv_write"] = self.kv_write
        if self.secret:
            out["secret"] = self.secret
        return out


class TaskSpec(BaseModel):
    id: str = Field(min_length=1)
    source_path: str = Field(min_length=1)
    difficulty: Difficulty
    description: str = Field(min_length=1)
    signature: str = Field(min_length=1)
    required_attrs: list[str] = Field(default_factory=list)
    required_effects: list[str] = Field(default_factory=list)
    required_grants: Grants = Field(default_factory=Grants)
    fuel_budget: int = Field(default=100_000, ge=1)
    inputs: list[TaskInput] = Field(min_length=1)
    expected_output_strategy: Literal["capture_from_reference", "literal"] = (
        "capture_from_reference"
    )
    # Used only when expected_output_strategy == "literal":
    expected_outputs: dict[str, str] | None = None
    # Phase 5a-4: stdlib modules this task expects the agent to import.
    # Each entry must be a bare module name (e.g. `"fs"`) — the runner
    # composes the corresponding `stdlib/sigil/<m>.sigil` into the LLM
    # source, AND the parse-aware verifier asserts the LLM's source has
    # `use sigil::<m>;` for each declared entry. Per I25 each name is
    # validated against `^[a-z_][a-z0-9_]*$` at load time.
    stdlib_imports: list[str] = Field(default_factory=list)
    # MODULE-SHAPED TASKS. When set, the model authors a LIBRARY module and this fixed driver
    # (repo-relative path to a `module tool;` source) is appended before compile. The model never
    # writes `tool_main`, so it cannot collapse the task into one function — which is what made the
    # tool-shaped corpus unable to exercise records/enums/Option/taint-across-a-boundary at all
    # (see the 2026-08-04 corpus-design audit). Empty = classic whole-program task.
    driver_path: str = ""
    # SCORING MODE. "forge" (default) = byte-exact on hidden inputs, the honest bar.
    # "check_only" = compile+capability-check alone. Required for ACTOR tasks: the forge has no
    # actor runtime (`forge` returns S002 "tool module must export pub fn tool_main"), so an actor
    # can be typechecked but never executed. A check-pass is a MUCH weaker claim than byte-exact —
    # it says the capability/taint/handler discipline holds, not that the logic is right — so these
    # score into a separate `check_correct` class and MUST NOT be added to the forge-correct
    # headline. See the 2026-08-04 corpus-design audit.
    scoring: str = Field(default="forge", pattern="^(forge|check_only)$")

    @model_validator(mode="after")
    def _expected_outputs_consistency(self) -> "TaskSpec":
        if self.expected_output_strategy == "literal":
            if not self.expected_outputs:
                raise ValueError(
                    f"task {self.id}: expected_outputs is required when "
                    "expected_output_strategy is 'literal'"
                )
            input_names = {inp.name for inp in self.inputs}
            missing = input_names - set(self.expected_outputs.keys())
            if missing:
                raise ValueError(
                    f"task {self.id}: expected_outputs missing keys for inputs: {sorted(missing)}"
                )
        return self

    @model_validator(mode="after")
    def _stdlib_imports_well_formed(self) -> "TaskSpec":
        """Phase 5a-4 / I25: each stdlib_imports entry must be a bare,
        well-formed module name. Path-traversal characters (`..`, `/`,
        `\\`, `:`) and uppercase variants fail the regex and are
        rejected before any file I/O happens in `compose_with_stdlib`.
        """
        for entry in self.stdlib_imports:
            if not _MODULE_NAME_RE.fullmatch(entry):
                raise ValueError(
                    f"task {self.id}: invalid stdlib_imports entry "
                    f"`{entry}` — must match ^[a-z_][a-z0-9_]*$ (bare "
                    "module name; no `sigil::` prefix, no path separators)"
                )
        return self

    @model_validator(mode="after")
    def _capture_strategy_compatible_with_grants(self) -> "TaskSpec":
        """Phase 5a-4 / I27: tasks with `time` or `random` grants
        cannot use `capture_from_reference` because the captured output
        won't match on the next run (clock advances, RNG returns
        different bytes). Force `literal` strategy for those tasks.
        """
        non_det_grants: list[str] = []
        if self.required_grants.time:
            non_det_grants.append("time")
        if self.required_grants.random:
            non_det_grants.append("random")
        if non_det_grants and self.expected_output_strategy == "capture_from_reference":
            raise ValueError(
                f"task {self.id}: required_grants includes "
                f"{non_det_grants} (non-deterministic) but "
                "expected_output_strategy is `capture_from_reference`. "
                "Use `literal` with hard-coded expected_outputs instead "
                "(per I27 — captured outputs won't match across runs)."
            )
        return self

    def resolve_source(self, repo_root: Path) -> Path:
        return (repo_root / self.source_path).resolve()


def load_tasks(tasks_dir: Path, *, only: list[str] | None = None) -> list[TaskSpec]:
    """Load every task*.yaml in tasks_dir, sorted by id. If `only` is given,
    filter to those task ids (raises if any requested id is missing)."""
    if not tasks_dir.is_dir():
        raise FileNotFoundError(f"tasks dir not found: {tasks_dir}")
    specs: list[TaskSpec] = []
    for path in sorted(tasks_dir.glob("task*.yaml")):
        with path.open("r", encoding="utf-8") as f:
            data = yaml.safe_load(f)
        try:
            specs.append(TaskSpec.model_validate(data))
        except Exception as e:
            raise ValueError(f"failed to parse {path.name}: {e}") from e
    if only:
        wanted = set(only)
        present = {s.id for s in specs}
        missing = wanted - present
        if missing:
            raise ValueError(
                f"requested task ids not found: {sorted(missing)}. "
                f"Available: {sorted(present)}"
            )
        specs = [s for s in specs if s.id in wanted]
    return specs
