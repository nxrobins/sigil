"""Cross-language CONTROL condition: the same 24 agentic tasks, the same models,
the same convergence loop — but the target language is plain Python instead of
SIGIL.

Purpose (paper Section 6.7 control): the SIGIL agent-convergence spread is 6-86%
compile success across models with ZERO SIGIL in their training data. The
low-scoring cells (Sonnet 22%, GPT-4o 6%) invite an apparatus objection: maybe
the harness is simply broken for non-GPT models — tool-calling quirks, oracle
strictness, provider routing. This control answers it. Same loop, same tasks,
same oracle, same tool-calling machinery, retargeted to the language every model
knows cold. If the low-SIGIL models hit ceiling here, their SIGIL deficit is
provably language-specific, not apparatus. Ceiling performance IS the point.

This is a control, not a comparison. The metrics are deliberately NOT symmetric
with SIGIL: SIGIL "compile" clears the full verification pipeline (types,
effects, taint, ownership, Z3); Python "compile" is a syntax check. So the
load-bearing signal is behavioral CORRECTNESS (does the tool produce the right
output on every input), not compile-vs-compile.

Each SIGIL task has a language-independent functional core (input string ->
output string) wrapped in SIGIL-specific ceremony (packed-pointer ABI, @Secret
taint, FFI rings, effect rows). The control tests that core in Python's native
stdin->stdout idiom. The per-model delta (SIGIL correctness - Python
correctness) is the measured cost of de novo language acquisition.

The oracle is shared: expected outputs are captured ONCE from the authoritative
SIGIL reference forge (`capture_ground_truth`), so both harnesses grade against
byte-identical input->output pairs.

Tools the model drives (mirroring sigil_check / sigil_forge):
  * python_check(source)      -> compile-only (syntax) check, structured result
  * python_run(source, input) -> execute in a sandboxed subprocess over stdin
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from sigil_bench.runner import resolve_input_value
from sigil_bench.tasks import TaskSpec

from .backends import ToolSpec

# ── Task derivation: SIGIL spec -> functional Python contract ─────────────────

# Faithful functional ports of each SIGIL task, preserving exact semantics
# (byte values, examples, edge cases) while dropping SIGIL-only ceremony
# (packed-pointer ABI, @Secret taint, FFI ring/effect rows, stdlib-import
# requirements). Each is checkable against the SIGIL task YAML's description.
# A mechanical strip cannot do this because function and ceremony are
# interleaved (e.g. the @Secret tasks state the transform AFTER the taint
# clause), so the ports are explicit and reviewable.
_FUNCTIONAL_BRIEFS: dict[str, str] = {
    "task001_echo": "Return the input bytes unchanged.",
    "task002_reverse": (
        "Return the input bytes in reverse order (last byte first). Empty input "
        "yields empty output."
    ),
    "task004_uppercase": (
        "ASCII-uppercase the input: each lowercase letter (a-z, byte values "
        "97-122) becomes the corresponding uppercase letter (A-Z, 65-90). All "
        "other bytes pass through unchanged."
    ),
    "task011_palindrome": (
        'Return the literal string "true" if the input is a palindrome (reads '
        'the same forwards and backwards, byte by byte), or "false" otherwise. '
        "Empty input is a palindrome."
    ),
    "task015_ascii_sum": (
        "Sum the byte values of all input bytes and return the total as an "
        'ASCII-decimal string. Empty input sums to 0. "A" (byte 65) returns '
        '"65"; "abc" returns "294".'
    ),
    "task020_rot13": (
        "Apply ROT13 to the input: ASCII uppercase (A-Z, 65-90) and lowercase "
        "(a-z, 97-122) letters each rotate 13 positions within their case; every "
        "other byte passes through unchanged. Output length equals input length."
    ),
    "task021_fibonacci": (
        "Parse the input as a decimal integer n and return the n-th Fibonacci "
        'number as an ASCII-decimal string, with fib(0)=0, fib(1)=1. Input "10" '
        'returns "55".'
    ),
    "task023_dec_to_hex": (
        "Parse the input as a decimal integer and return that value as LOWERCASE "
        "hexadecimal with no 0x prefix and no leading zeros (0 renders as \"0\"). "
        '"255" returns "ff"; "4096" returns "1000".'
    ),
    "task026_read_file": (
        "Read the file whose path is supplied as input and return its raw bytes "
        "unchanged."
    ),
    "task028_count_lines": (
        "Read the file at the supplied path and return the number of lines as an "
        "ASCII-decimal string. Lines are delimited by \\n (byte 10). A trailing "
        "newline does NOT count as an extra line; a file ending without a "
        "trailing newline still counts its final line."
    ),
    "task029_count_lines_via_stdlib": (
        "Read the file at the supplied path and return the number of lines as an "
        "ASCII-decimal string. Lines are delimited by \\n (byte 10). A trailing "
        "newline does NOT count as an extra line; a file ending without a "
        "trailing newline still counts its final line."
    ),
    "task032_sha256_hex": (
        "Compute the SHA-256 of the input bytes and return it as lowercase hex "
        "(64 ASCII characters)."
    ),
    "task045_http_size_via_stdlib": (
        "Fetch the URL given as input via HTTP GET and return the byte count of "
        "the response body as an ASCII-decimal string."
    ),
    "task061_json_field": (
        'Extract the value of the top-level field named "name" from a JSON '
        "object passed as input. For a string value, return the string body "
        "without quotes; for a number/bool/null, the literal characters. Assume "
        "a flat top-level object."
    ),
    "task085_eval_add_sub": (
        "Evaluate a simple arithmetic expression of decimal integers joined by + "
        "and - operators, strictly left-to-right (no precedence, no spaces, no "
        'parentheses). "3+4" returns "7", "10-3-2" returns "5", "100-50+25" '
        'returns "75". The result may be negative (render a leading -).'
    ),
    "task101_secret_length": (
        "Return the byte length of the input as an ASCII-decimal string."
    ),
    "task103_secret_mask": (
        "Return a run of asterisk bytes '*' (byte 42) of the SAME length as the "
        "input — a masked placeholder. Empty input yields empty output."
    ),
    "task105_secret_xor_hex": (
        "XOR-fold all input bytes together into a single checksum byte (running "
        "XOR starting from 0) and return that byte as exactly two LOWERCASE hex "
        'digits. Empty input yields "00".'
    ),
    "task121_secret_rot13": (
        "Apply ROT13 to the input: ASCII letters (A-Z, a-z) rotate 13 positions "
        "within their case; all other bytes pass through unchanged."
    ),
    "task127_fs_sort_lines": (
        "Read the file whose path is supplied as input and return its lines "
        "sorted in ascending byte order, one per line."
    ),
    "task129_fs_grep_error": (
        "Read the file whose path is supplied as input and return only the lines "
        "that contain the substring ERROR, in their original order, one per line."
    ),
    "task151_http_size": (
        "Fetch the URL given as input via HTTP GET and return the byte count of "
        "the response body as an ASCII-decimal string."
    ),
    "task152_http_lines": (
        "Fetch the URL given as input via HTTP GET and return the number of "
        "lines in the response body as an ASCII-decimal string. Lines are "
        "delimited by \\n (byte 10)."
    ),
    "task154_http_wc": (
        "Fetch the URL given as input via HTTP GET and return the number of "
        "whitespace-separated words in the response body as an ASCII-decimal "
        'string. A "word" is a maximal run of non-whitespace bytes; whitespace '
        "is space, tab, newline, and carriage return."
    ),
}


def functional_brief(task: TaskSpec) -> str:
    """The language-independent functional statement for a task. Explicit,
    faithful port (see `_FUNCTIONAL_BRIEFS`); raises if a task has no port so a
    new task can never silently fall back to a mangled auto-strip."""
    brief = _FUNCTIONAL_BRIEFS.get(task.id)
    if brief is None:
        raise KeyError(
            f"no functional brief for task {task.id!r} — add a faithful port to "
            "_FUNCTIONAL_BRIEFS (do not auto-derive; function and ceremony are "
            "interleaved in the SIGIL descriptions)."
        )
    return brief


def input_kind(task: TaskSpec) -> str:
    """How the task's input string should be interpreted by the Python tool."""
    if task.required_grants.net:
        return "url"
    if task.required_grants.fs or task.required_grants.fs_write:
        return "path"
    return "literal"


SYSTEM_PROMPT_TEMPLATE = """\
You write small, self-contained Python 3 command-line tools.

Contract for every task:
  * Read the ENTIRE input from standard input (sys.stdin.read()).
  * Write ONLY the result to standard output (sys.stdout), with no trailing
    newline unless the result itself ends in one. Do not print debug text.
  * The program is a complete script run as `python tool.py` with the input
    piped on stdin. Use only the Python standard library.

You have two tools:
  * python_check(source): syntax-checks the source. Call it to catch errors
    before running.
  * python_run(source, input): runs the source with `input` on stdin and
    returns its stdout/stderr. Use it to test against the task's examples.

Iterate: write source, check it, run it on the examples, fix, repeat. When the
output matches the task for every example, you are done — stop calling tools.
"""


def render_system_prompt(task: TaskSpec) -> str:
    brief = functional_brief(task)
    kind = input_kind(task)
    if kind == "url":
        input_line = (
            "The input on stdin is a URL. Fetch it with urllib.request over the "
            "network and process the response as described."
        )
    elif kind == "path":
        input_line = (
            "The input on stdin is a filesystem path (relative to the current "
            "working directory). Open and read that file, then process it."
        )
    else:
        input_line = "The input on stdin is the data to process directly."
    examples = ", ".join(f"{inp.name!r}={inp.value!r}" for inp in task.inputs)
    return (
        SYSTEM_PROMPT_TEMPLATE
        + f"\n\nTASK ({task.id}):\n{brief}\n\n{input_line}\n\n"
        + f"Example input names/values: {examples}\n"
    )


KICKOFF_USER_MESSAGE = (
    "Write the Python tool for this task. Check and run it against the examples, "
    "then stop when it is correct."
)


# ── Model-facing tool specs ──────────────────────────────────────────────────


def model_tool_specs() -> list[ToolSpec]:
    return [
        ToolSpec(
            name="python_check",
            description=(
                "Syntax-check a Python 3 source string WITHOUT running it. "
                'Returns {"status":"ok"} if it compiles, or {"status":"error", '
                '"error_type":..., "message":..., "line":...} on a SyntaxError.'
            ),
            input_schema={
                "type": "object",
                "properties": {"source": {"type": "string", "description": "Python 3 source."}},
                "required": ["source"],
            },
        ),
        ToolSpec(
            name="python_run",
            description=(
                "Run a Python 3 source string as a script with `input` piped to "
                'stdin. Returns {"status":"ok","stdout":...,"stderr":...} or '
                '{"status":"error",...} on a non-zero exit, timeout, or crash.'
            ),
            input_schema={
                "type": "object",
                "properties": {
                    "source": {"type": "string", "description": "Python 3 source."},
                    "input": {"type": "string", "description": "Bytes piped to stdin. Default empty."},
                },
                "required": ["source"],
            },
        ),
    ]


# ── Executor ─────────────────────────────────────────────────────────────────


@dataclass
class ToolCallRecord:
    index: int
    name: str
    ok: bool | None = None
    check_attempt: int | None = None
    codes: list[str] = field(default_factory=list)
    run_input: str | None = None
    run_status: str | None = None
    output_text: str | None = None
    error: str | None = None


@dataclass
class ExecControl:
    stop: bool = False
    reason: str | None = None


_RUN_TIMEOUT_S = 15


class PyToolExecutor:
    """Mirror of MCPToolExecutor's metric surface, for the Python target.
    One instance per (model x task x run) cell."""

    def __init__(
        self,
        task: TaskSpec,
        repo_root: Path,
        *,
        max_check_attempts: int,
        expected_outputs: dict[str, str] | None = None,
    ) -> None:
        self._task = task
        self._repo_root = repo_root
        self._max_check_attempts = max_check_attempts
        self._expected_outputs = expected_outputs

        self.check_attempts = 0
        self.first_check_ok: bool | None = None
        self.attempts_to_success: int | None = None
        self.any_check_passed = False
        self.hit_cap = False
        self.code_counts: Counter[str] = Counter()
        self.grants_requested: list[dict[str, Any]] = []  # always empty (parity field)
        self.forge_calls = 0
        self.forge_fuel_consumed = 0
        self.lookup_calls = 0
        self.tool_log: list[ToolCallRecord] = []
        self.last_passing_source: str | None = None
        self._call_index = 0

    # ── run a python source over an input, sandboxed subprocess ──
    def _run_source(self, source: str, stdin_text: str) -> dict[str, Any]:
        with tempfile.TemporaryDirectory() as td:
            tool = Path(td) / "tool.py"
            tool.write_text(source, encoding="utf-8")
            try:
                proc = subprocess.run(
                    [sys.executable, "-I", str(tool)],
                    input=stdin_text.encode("utf-8"),
                    capture_output=True,
                    timeout=_RUN_TIMEOUT_S,
                    cwd=str(self._repo_root),
                )
            except subprocess.TimeoutExpired:
                return {"status": "error", "reason": "timeout", "stdout": "", "stderr": "timed out"}
            stdout = proc.stdout.decode("utf-8", errors="replace")
            stderr = proc.stderr.decode("utf-8", errors="replace")
            if proc.returncode != 0:
                return {"status": "error", "reason": "nonzero_exit", "code": proc.returncode,
                        "stdout": stdout, "stderr": stderr}
            return {"status": "ok", "stdout": stdout, "stderr": stderr}

    def execute(self, name: str, args: dict[str, Any]) -> tuple[str, ExecControl]:
        self._call_index += 1
        try:
            if name == "python_check":
                return self._do_check(args)
            if name == "python_run":
                return self._do_run(args)
            self.tool_log.append(ToolCallRecord(self._call_index, name, ok=False, error="unknown tool"))
            return json.dumps({"status": "error", "message": f"unknown tool {name!r}"}), ExecControl()
        except Exception as e:  # noqa: BLE001
            self.tool_log.append(ToolCallRecord(self._call_index, name, ok=False, error=f"{type(e).__name__}: {e}"))
            return json.dumps({"status": "error", "message": f"harness error running {name}: {e}"}), ExecControl()

    def _do_check(self, args: dict[str, Any]) -> tuple[str, ExecControl]:
        source = args.get("source")
        if not isinstance(source, str) or not source.strip():
            self.tool_log.append(ToolCallRecord(self._call_index, "python_check", ok=False, error="missing source"))
            return json.dumps({"status": "error", "message": "python_check requires a non-empty `source`"}), ExecControl()
        self.check_attempts += 1
        try:
            compile(source, "<tool>", "exec")
            ok = True
            env: dict[str, Any] = {"status": "ok"}
            codes: list[str] = []
        except SyntaxError as e:
            ok = False
            code = type(e).__name__  # SyntaxError | IndentationError | TabError
            codes = [code]
            env = {"status": "error", "error_type": code, "message": str(e.msg), "line": e.lineno}
        self.code_counts.update(codes)
        if self.first_check_ok is None:
            self.first_check_ok = ok
        if ok:
            self.last_passing_source = source
            if not self.any_check_passed:
                self.any_check_passed = True
                self.attempts_to_success = self.check_attempts
        self.tool_log.append(
            ToolCallRecord(self._call_index, "python_check", ok=ok, check_attempt=self.check_attempts, codes=codes)
        )
        if not ok and not self.any_check_passed and self.check_attempts >= self._max_check_attempts:
            self.hit_cap = True
            return json.dumps(env), ExecControl(stop=True, reason="hit_cap")
        return json.dumps(env), ExecControl()

    def _do_run(self, args: dict[str, Any]) -> tuple[str, ExecControl]:
        source = args.get("source")
        if not isinstance(source, str) or not source.strip():
            self.tool_log.append(ToolCallRecord(self._call_index, "python_run", ok=False, error="missing source"))
            return json.dumps({"status": "error", "message": "python_run requires a non-empty `source`"}), ExecControl()
        self.forge_calls += 1
        run_input = args.get("input", "")
        if not isinstance(run_input, str):
            run_input = str(run_input)
        result = self._run_source(source, run_input)
        self.tool_log.append(
            ToolCallRecord(
                self._call_index, "python_run", ok=(result["status"] == "ok"),
                run_input=run_input, run_status=result["status"],
                output_text=result.get("stdout"),
            )
        )
        return json.dumps(result), ExecControl()

    # ── authoritative final-source verdict (harness-run) ──
    def verify_final_source(self, *, check_capability_use: bool = False) -> dict[str, Any]:
        """Grade the last check-passing source over every task input against the
        shared SIGIL ground truth.

        We record TWO verdicts per input. `all_passed` (the headline) uses a
        trailing-whitespace-tolerant comparison, because this is a CAPABILITY
        control: whether the model computed the right answer, not whether it
        matched SIGIL's exact-byte output contract. A trailing newline (idiomatic
        Python `print`) is an output-format difference orthogonal to capability.
        `all_passed_exact` keeps the byte-exact verdict for full transparency."""
        if self.last_passing_source is None:
            return {"ran": False, "reason": "no passing source"}
        expected = self._expected_outputs
        if not expected:
            return {"ran": False, "reason": "no expected outputs"}
        per_input: list[dict[str, Any]] = []
        all_passed = all_passed_exact = True
        for inp in self._task.inputs:
            value = resolve_input_value(inp.value, self._repo_root)
            res = self._run_source(self.last_passing_source, value)
            got = res.get("stdout") if res.get("status") == "ok" else None
            want = expected.get(inp.name)
            ok = res.get("status") == "ok"
            passed_exact = ok and got == want
            passed_norm = ok and got is not None and got.rstrip("\r\n") == (want or "").rstrip("\r\n")
            all_passed = all_passed and passed_norm
            all_passed_exact = all_passed_exact and passed_exact
            per_input.append({
                "input": inp.name, "passed": passed_norm, "passed_exact": passed_exact,
                "status": res.get("status"),
            })
        return {
            "ran": True, "all_passed": all_passed, "all_passed_exact": all_passed_exact,
            "per_input": per_input, "capability_unused": None,
        }
