"""The "SIGIL Tool Generation" system prompt + per-task description block.

`SYSTEM_PROMPT_TEMPLATE` is the experiment's system prompt VERBATIM, with a
single `{{TASK_DESCRIPTION}}` placeholder. `render_system_prompt(task)`
substitutes a task-specific description block built from the `TaskSpec`.

Deliberately we do NOT tell the model which `grants` to pass to `sigil_forge`
— inferring the right capabilities from the task description is part of what
the experiment measures (the "grants requested" metric). We DO surface the
required signature, effects and module attributes, since those are part of the
task contract, not something the model is being tested on guessing.
"""

from __future__ import annotations

from pathlib import Path

from sigil_bench.tasks import TaskSpec

# ── The verbatim system prompt (single {{TASK_DESCRIPTION}} placeholder) ────
# Stored as a literal so the experiment is reproducible and greppable. The
# embedded ```sigil fence is intentional and well-formed.
SYSTEM_PROMPT_TEMPLATE = """# SIGIL Tool Generation

You are writing a tool program in SIGIL, a capability-secure language targeting WebAssembly. Your goal is to produce a working tool that compiles, verifies, and executes correctly.

## Language basics

SIGIL is statically typed with explicit capabilities, effect rows, and taint labels. A tool exports:

```sigil
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { /* effects */ } {
    // input bytes at input_ptr/input_len
    // return packed (ptr << 32 | len) output
}
```

Key rules:

- No ambient authority. I/O requires capabilities passed as parameters or granted by the host.
- Effects must be declared in the function signature: `! { NetIO, Alloc, FFI, Unsafe }`
- Capabilities are linear (move semantics — use once, no copy).
- Taint labels (`@Public`, `@Internal`, `@Secret`) track information flow.
- Two rings: inner (actors, state, cap ownership) and outer (pure functions, FFI wrappers).
- All execution is bounded by fuel. No infinite loops.

## Available tools

- `sigil_check(source)` — Compile and verify. Returns structured diagnostics on failure (error code, message, hint, span).
- `sigil_forge(source, input, fuel?, grants?)` — Compile and execute. Returns output or diagnostics.
- `sigil_lookup_error(code)` — Look up an error code for explanation and fix guidance.

## Process

1. Write your best attempt at the SIGIL source for the task.
2. Call `sigil_check` with your source.
3. If it fails, read the diagnostics carefully. Use `sigil_lookup_error` if a code is unclear.
4. Fix the issues and retry from step 2.
5. Once it compiles clean, call `sigil_forge` with appropriate input to verify execution.

Do not invent syntax. If you are unsure whether something exists, try it and let the compiler tell you. Trust the diagnostics — they are precise and positional.

## Task

{{TASK_DESCRIPTION}}
"""

# The kickoff user turn. Short on purpose — the contract lives in the system
# prompt; this only tells the model to begin and to use the tools to verify.
KICKOFF_USER_MESSAGE = (
    "Write the SIGIL tool for the task in the system prompt. Use `sigil_check` "
    "to verify it compiles, read and fix any diagnostics, then use "
    "`sigil_forge` to confirm it executes. When you have a tool that passes "
    "`sigil_check`, reply with the final source in a ```sigil fenced block."
)


def build_task_description(task: TaskSpec) -> str:
    """The block substituted for `{{TASK_DESCRIPTION}}`.

    Description (verbatim) + the hard contract (signature / effects / module
    attributes). Grants are deliberately omitted — see module docstring.
    """
    lines: list[str] = [task.description.rstrip(), ""]
    lines.append(f"Required exported signature: `{task.signature}`")
    if task.required_effects:
        effects = ", ".join(task.required_effects)
        lines.append(f"Required effects on `tool_main`: `! {{ {effects} }}`")
    if task.required_attrs:
        attrs = ", ".join(f"`{a}`" for a in task.required_attrs)
        lines.append(f"Required module attributes: {attrs}")
    if task.driver_path:
        # Module/actor-shaped task: the model authors a LIBRARY (or actor); this fixed driver is
        # appended by the harness before compile. Including its source verbatim makes the required
        # interface unambiguous — every name, field and signature the driver touches is a
        # compiler-enforced obligation on the model's code.
        try:
            driver_src = (Path(__file__).resolve().parents[3].parent / task.driver_path).read_text(
                encoding="utf-8")
        except OSError:
            driver_src = "(driver source unavailable)"
        lines.append(
            "\nA fixed driver (below) is appended to your code before compilation. Write ONLY the "
            "module(s) it calls into — do NOT write `pub fn tool_main` and do NOT write "
            "`entry actor Main`; both already exist in the driver and duplicating them is a "
            "compile error.\n\n```sigil\n" + driver_src.strip() + "\n```")
    if task.stdlib_imports:
        mods = ", ".join(f"`sigil::{m}`" for m in task.stdlib_imports)
        lines.append(
            "You may import these stdlib modules with a top-level "
            f"`use sigil::<module>;`: {mods}. Their source is linked in "
            "automatically when you call `sigil_check` / `sigil_forge`."
        )
    return "\n".join(lines)


def render_system_prompt(task: TaskSpec) -> str:
    """The full system prompt for `task`, with `{{TASK_DESCRIPTION}}` filled."""
    return SYSTEM_PROMPT_TEMPLATE.replace(
        "{{TASK_DESCRIPTION}}", build_task_description(task)
    )
