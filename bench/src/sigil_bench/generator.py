"""Source generators for sigil-bench.

The agent loop calls `Generator.generate(task, transcript)` to get the next
candidate `.sigil` source. Two flavors:

* `OracleStub` / `BrokenStub` / `RecoverStub` — deterministic stubs for tests
  and `--dry-run`. Zero LLM cost.
* `AnthropicGenerator` — wraps the Anthropic Messages API with prompt-cached
  system prompts (system.md + recipes.md + lang-ref.md + ERROR-CODES.md).
  Three cache-controlled blocks; per-call user message carries task spec
  and the latest attempt's diagnostics.
"""

from __future__ import annotations

import hashlib
import os
import re
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Protocol

from .tasks import TaskSpec

if TYPE_CHECKING:
    from anthropic import Anthropic

# Phase 5a-4: stdlib bundle hash truncation length, mirrors compose.py
# (where it gates the per-task composed_source key). The cache-block
# variant uses the SAME truncation so test harnesses can correlate.
_STDLIB_BUNDLE_HASH_HEX_LEN: int = 24

# ── Source extraction ─────────────────────────────────────────────────────


_FENCE_RE = re.compile(r"```(?:[a-zA-Z_]+)?\s*\n(.*?)\n```", re.DOTALL)
# Must tolerate an ATTRIBUTED declaration — every FFI tool opens with
# `#[ring(outer)] #[trusted] module tool;`. Without the attribute prefix this misses the
# existing header, extract_source injects a second `module tool;`, and the compiler rejects
# the result with N001 (duplicate module).
_MODULE_RE = re.compile(r"(?m)^\s*(?:#\[[^\]]*\]\s*)*module\s+\w+\s*;")


def extract_source(response_text: str) -> str:
    """Pull the .sigil body out of a model response. Tolerant: accepts
    ```sigil, ```rust, ``` (no language), or no fence at all.

    Harness repair: if the body has no `module ...;` declaration, inject
    `module tool;`. Some models emit a correct tool body but drop the required
    module wrapper — the compiler then rejects every one with P002 before judging
    the logic. Supplying the omitted boilerplate is a no-op for models that
    already emit `module`."""
    match = _FENCE_RE.search(response_text)
    body = match.group(1).strip() if match else response_text.strip()
    if body and not _MODULE_RE.search(body):
        body = "module tool;\n\n" + body
    return body


# ── Generator protocol ────────────────────────────────────────────────────


class Generator(Protocol):
    """Anything that can produce a .sigil source for a given task."""

    name: str

    def generate(self, task: TaskSpec, transcript: list[dict[str, Any]]) -> str: ...


# ── Stubs (deterministic, no API calls) ───────────────────────────────────


class OracleStub:
    """Returns the contents of `source_path` verbatim. Used for `--dry-run`
    and as the recover source in tests."""

    name = "OracleStub"

    def __init__(self, source_path: Path) -> None:
        self._source = source_path.read_text(encoding="utf-8")

    def generate(self, task: TaskSpec, transcript: list[dict[str, Any]]) -> str:
        return self._source


# Source that fails `sigil_check` deterministically: references an
# undefined identifier `missing`. The check loop iterates on check
# failures, so this is what triggers exhaust-attempts behavior. (S002,
# the missing-tool_main code, only fires inside `sigil_forge`'s
# compile_tool gate — too late to drive the check loop.)
_BROKEN_SOURCE = (
    "module tool; "
    "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return missing; }"
)


class BrokenStub:
    """Always returns a source that fails `sigil_check` with T060
    (undefined local). Verifies the runner exhausts attempts cleanly."""

    name = "BrokenStub"

    def generate(self, task: TaskSpec, transcript: list[dict[str, Any]]) -> str:
        return _BROKEN_SOURCE


class RecoverStub:
    """Returns broken source on the first call, then `then_source` on every
    subsequent call. Verifies the runner converges after one bad attempt."""

    name = "RecoverStub"

    def __init__(self, then_source: str) -> None:
        self._then = then_source
        self._calls = 0

    def generate(self, task: TaskSpec, transcript: list[dict[str, Any]]) -> str:
        self._calls += 1
        if self._calls == 1:
            return _BROKEN_SOURCE
        return self._then


# ── Anthropic-backed generator (production driver) ────────────────────────


_PROMPTS_DIR = Path(__file__).resolve().parent / "prompts"


@dataclass
class _CacheBlocks:
    """The four cache-controlled system blocks. Built once per generator
    instance; reused across every `generate()` call so the cache stays
    warm. The fourth block (`stdlib_bundle`) is the entire `stdlib/sigil/`
    contents — added in Phase 5a-4 so the model can introspect available
    stdlib functions without each task carrying the source. The
    `stdlib_hash` is exposed on the dataclass for telemetry."""

    system_md: str
    recipes_and_langref: str
    error_codes: str
    stdlib_bundle: str
    stdlib_hash: str

    def to_messages_api(self) -> list[dict[str, Any]]:
        ephemeral: dict[str, Any] = {"type": "ephemeral"}
        return [
            {"type": "text", "text": self.system_md, "cache_control": ephemeral},
            {
                "type": "text",
                "text": self.recipes_and_langref,
                "cache_control": ephemeral,
            },
            {"type": "text", "text": self.error_codes, "cache_control": ephemeral},
            {"type": "text", "text": self.stdlib_bundle, "cache_control": ephemeral},
        ]


def _load_stdlib_bundle(repo_root: Path) -> tuple[str, str]:
    """Concatenate every `stdlib/sigil/*.sigil` (sorted, normalized to LF)
    into one block, then compute a 24-hex-char SHA-256 truncation. The
    bundle order is byte-deterministic so the cache key is stable across
    runs on the same stdlib content. Returns (text, hash)."""
    stdlib_dir = repo_root / "stdlib" / "sigil"
    sources: list[str] = []
    for path in sorted(stdlib_dir.glob("*.sigil")):
        raw = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
        # Per-line trailing whitespace strip + ensure trailing newline,
        # matching the discipline applied in `compose.py` so the bundle
        # hash here would match a hypothetical bundle composed with all
        # modules.
        lines = [ln.rstrip() for ln in raw.split("\n")]
        normalized = "\n".join(lines)
        if not normalized.endswith("\n"):
            normalized += "\n"
        sources.append(f"// === {path.name} ===\n{normalized}")
    bundle = "\n".join(sources)
    digest = hashlib.sha256(bundle.encode("utf-8")).hexdigest()[:_STDLIB_BUNDLE_HASH_HEX_LEN]
    return bundle, digest


def _load_cache_blocks(repo_root: Path) -> _CacheBlocks:
    system_md = (_PROMPTS_DIR / "system.md").read_text(encoding="utf-8")
    recipes_md = (_PROMPTS_DIR / "recipes.md").read_text(encoding="utf-8")
    lang_ref = (repo_root / "lang-ref.md").read_text(encoding="utf-8")
    error_codes = (repo_root / "docs" / "ERROR-CODES.md").read_text(encoding="utf-8")
    combined_lang = (
        "# Tool-writing recipes\n\n"
        f"{recipes_md}\n\n"
        "# Sigil ToolForge language reference (lang-ref.md)\n\n"
        f"{lang_ref}\n"
    )
    stdlib_bundle, stdlib_hash = _load_stdlib_bundle(repo_root)
    stdlib_block = (
        "# Sigil stdlib (composed at task time via `use sigil::<m>;`)\n"
        "\n"
        "Below is the verbatim source of every stdlib module currently shipped. "
        "When a task lists `stdlib_imports`, those modules are concatenated with "
        "your tool source before `sigil_check`/`sigil_forge` run, so any `pub fn` "
        "or `effect` declared here is callable from your tool via "
        "`<module>::<fn>(...)` after a top-level `use sigil::<module>;`.\n"
        "\n"
        f"_stdlib bundle hash: `{stdlib_hash}`_\n"
        "\n"
        f"{stdlib_bundle}\n"
    )
    return _CacheBlocks(
        system_md=system_md,
        recipes_and_langref=combined_lang,
        error_codes=error_codes,
        stdlib_bundle=stdlib_block,
        stdlib_hash=stdlib_hash,
    )


# ── Diagnostic rendering: the A/B variable (diagnostics-axes a9) ───────────
#
# `detail` selects how much of the errors-as-API envelope the model sees:
#   * "bare" — `[CODE]: message` only. The honest "no errors-as-API
#     investment" counterfactual (what a minimal compiler must emit).
#   * "full" — title + location + message + hint + a model-actionable
#     suggested_edits line. The complete structured envelope.
# Both modes render the SAME diagnostic set (same codes, count, order);
# only per-diagnostic verbosity differs — that single difference IS the
# measured variable. See docs/DIAGNOSTIC_EVIDENCE.md.
DIAGNOSTIC_DETAIL_MODES = ("full", "bare")


def _render_suggested_edits(diag: dict[str, Any]) -> list[str]:
    """Render each suggested edit by TYPE + replacement text — never by slicing
    the agent's source. The compiler's offsets are COMPOSED-space on stdlib
    tasks (stdlib is prepended), so slicing the agent source would garble the
    text (the iter-13 trap, for bytes). An empty-span edit is an insertion;
    otherwise a use/replacement. Replacement-only is robust either way (C3)."""
    out: list[str] = []
    for edit in diag.get("suggested_edits") or []:
        new = edit.get("replacement", "")
        start, end = edit.get("start"), edit.get("end")
        if isinstance(start, int) and isinstance(end, int) and start == end:
            out.append(f"  fix: insert `{new}`")
        else:
            out.append(f"  fix: use `{new}`")
    return out


def _format_diagnostic(
    diag: dict[str, Any],
    *,
    detail: str = "full",
    include_suggested_edits: bool = True,
    line_offset: int = 0,
) -> str:
    """Format one diagnostic for a retry prompt. `detail` is the envelope A/B
    variable (see DIAGNOSTIC_DETAIL_MODES). `include_suggested_edits` is the
    SECOND A/B variable (the +45%/redundancy experiment): when False the fix
    line is suppressed even in full mode. `line_offset` is the prepended-stdlib
    line count: diagnostic line numbers arrive in COMPOSED coordinates, so we
    subtract it to show the agent ITS OWN line (iter 13). 0 = no stdlib."""
    code = diag.get("code", "?")
    message = diag.get("message", "")
    if detail == "bare":
        return f"[{code}]: {message}"
    title = diag.get("title", "")
    hint = diag.get("hint")
    loc = diag.get("primary_label", {}).get("location") or diag.get("location")
    loc_str = ""
    if isinstance(loc, dict):
        line = loc.get("line")
        col = loc.get("column")
        if isinstance(line, int):
            src_line = line - line_offset
            if src_line >= 1:
                loc_str = f" @ line {src_line}" + (f", col {col}" if col is not None else "")
            # else: the error sits in the prepended stdlib region, not the
            # agent's source — omit a line number that would only mislead.
    parts = [f"[{code}] {title}{loc_str}: {message}"]
    if hint:
        parts.append(f"  hint: {hint}")
    if include_suggested_edits:
        parts.extend(_render_suggested_edits(diag))
    return "\n".join(parts)


def _build_user_message(
    task: TaskSpec,
    transcript: list[dict[str, Any]],
    *,
    detail: str = "full",
    include_suggested_edits: bool = True,
) -> str:
    """Compose the per-call user message.

    On attempt 1 (transcript empty): task description + signature/attrs/
    effects/grants only.
    On retries: same task block + last attempt's source + full diagnostics
    + (for attempt 3+) compact summary of older attempts' codes.
    """
    lines: list[str] = []
    lines.append(f"# Task: {task.id}")
    lines.append("")
    lines.append("## Description")
    lines.append(task.description.rstrip())
    lines.append("")
    lines.append("## Required signature")
    lines.append(f"`{task.signature}`")
    if task.required_attrs:
        lines.append("")
        lines.append("## Required module attributes")
        for attr in task.required_attrs:
            lines.append(f"- `{attr}`")
    if task.required_effects:
        lines.append("")
        lines.append("## Required effects on `tool_main`")
        lines.append(f"`! {{ {', '.join(task.required_effects)} }}`")
    grants = task.required_grants.to_mcp()
    if grants:
        lines.append("")
        lines.append("## Host-supplied grants (informational — do NOT mention in source)")
        for kind, items in grants.items():
            lines.append(f"- `{kind}`: {items}")

    if not transcript:
        lines.append("")
        lines.append(
            "Return one fenced ```sigil``` block with the complete tool "
            "source. No prose."
        )
        return "\n".join(lines)

    # Retry: surface the last attempt's full diagnostics. Older attempts'
    # diagnostics are compressed to a code-list summary so token growth is
    # bounded.
    last = transcript[-1]
    older = transcript[:-1]
    lines.append("")
    lines.append(f"## Previous attempt #{last.get('attempt_no', '?')} — failed `sigil_check`")
    lines.append("")
    lines.append("### Source you submitted")
    lines.append("```sigil")
    lines.append(last.get("source", "").rstrip())
    lines.append("```")

    diagnostics = (last.get("check_envelope") or {}).get("diagnostics") or []
    line_offset = last.get("source_line_offset", 0)
    lines.append("")
    lines.append("### Diagnostics")
    if not diagnostics:
        lines.append("(none — check_envelope was malformed)")
    else:
        for d in diagnostics:
            lines.append(
                _format_diagnostic(
                    d,
                    detail=detail,
                    include_suggested_edits=include_suggested_edits,
                    line_offset=line_offset,
                )
            )

    if older:
        lines.append("")
        lines.append("### Older attempts (summary)")
        for a in older:
            # Phase 6a-2 / I-OPS-17: failure_codes is `list[dict]`.
            # Tolerate the legacy `list[str]` shape too for older
            # transcripts being replayed under the new code.
            raw_codes = a.get("failure_codes") or []
            code_strs: list[str] = []
            for entry in raw_codes:
                if isinstance(entry, str):
                    code_strs.append(entry)
                elif isinstance(entry, dict) and "code" in entry:
                    code_strs.append(str(entry["code"]))
            n = a.get("attempt_no", "?")
            code_str = ", ".join(code_strs) if code_strs else "(no codes recorded)"
            lines.append(f"- attempt #{n}: {code_str}")

    lines.append("")
    lines.append(
        "Fix the diagnostics above. Return one fenced ```sigil``` block "
        "with the complete corrected source. No prose."
    )
    return "\n".join(lines)


class AnthropicGenerator:
    """Production generator. Wraps the Anthropic Messages API with three
    cache-controlled system blocks (system.md, recipes+lang-ref,
    ERROR-CODES.md). Each `generate()` call sends a fresh user message
    composed by `_build_user_message`."""

    name = "AnthropicGenerator"

    def __init__(
        self,
        client: Anthropic,
        model: str,
        repo_root: Path,
        *,
        max_tokens: int = 4096,
        detail: str = "full",
        include_suggested_edits: bool = True,
    ) -> None:
        if detail not in DIAGNOSTIC_DETAIL_MODES:
            raise ValueError(
                f"detail must be one of {DIAGNOSTIC_DETAIL_MODES}, got {detail!r}"
            )
        self._client = client
        self._model = model
        self._max_tokens = max_tokens
        self._detail = detail
        self._include_suggested_edits = include_suggested_edits
        self._blocks = _load_cache_blocks(repo_root)
        self._system_param = self._blocks.to_messages_api()

    @property
    def model(self) -> str:
        return self._model

    @property
    def stdlib_hash(self) -> str:
        """24-hex-char SHA-256 truncation of the cached stdlib bundle.
        Exposed for telemetry — when the stdlib changes between runs,
        this value changes and the prompt-cache invalidates cleanly."""
        return self._blocks.stdlib_hash

    @property
    def detail(self) -> str:
        return self._detail

    def generate(self, task: TaskSpec, transcript: list[dict[str, Any]]) -> str:
        user_text = _build_user_message(
            task,
            transcript,
            detail=self._detail,
            include_suggested_edits=self._include_suggested_edits,
        )
        response = self._client.messages.create(
            model=self._model,
            max_tokens=self._max_tokens,
            system=self._system_param,  # type: ignore[arg-type]
            messages=[{"role": "user", "content": user_text}],
        )
        # Concatenate text blocks (the API can return multiple); pick the
        # first .sigil fence inside the combined text via extract_source.
        text_chunks = [b.text for b in response.content if getattr(b, "type", "") == "text"]
        combined = "\n".join(text_chunks)
        return extract_source(combined)

    # ── Cost-estimation helpers ──────────────────────────────────────────

    def count_system_tokens(self) -> int:
        """Number of input tokens in the (cached) system blocks. Used by
        the pre-flight cost estimator. One round-trip; cheap."""
        # count_tokens accepts the same `system` shape as messages.create.
        # We send a one-token user message so the API has a well-formed
        # request; the system count we want is the dominant component.
        result = self._client.messages.count_tokens(
            model=self._model,
            system=self._system_param,  # type: ignore[arg-type]
            messages=[{"role": "user", "content": "x"}],
        )
        # The API returns total input tokens. The "x" user message is ~1
        # token, so subtract a small fudge factor — but we'd rather
        # over-estimate than under-estimate cost, so return the raw total.
        return int(result.input_tokens)

    def count_user_tokens_for(
        self, task: TaskSpec, transcript: list[dict[str, Any]] | None = None
    ) -> int:
        """Number of tokens for an attempt-N user message against `task`.
        Pass an empty transcript for attempt-1; pass a representative
        transcript to estimate retry-cost ceilings."""
        user_text = _build_user_message(
            task,
            transcript or [],
            detail=self._detail,
            include_suggested_edits=self._include_suggested_edits,
        )
        # We want JUST the user-message tokens, not system. Send WITHOUT
        # system blocks so the response is the user-only count.
        result = self._client.messages.count_tokens(
            model=self._model,
            messages=[{"role": "user", "content": user_text}],
        )
        return int(result.input_tokens)


# ── OpenAI-compatible generator (Azure / vLLM / OpenAI) ────────────────────
#
# One generator drives any OpenAI-chat-compatible endpoint: Azure OpenAI
# (gpt-5.5), a LOCAL vLLM-served model (any OpenAI-compatible base_url),
# or OpenAI proper. The four Anthropic cache blocks are concatenated into one
# system message (OpenAI has no cache-block API); the user message and source
# extraction are shared with AnthropicGenerator, so this is a fair baseline —
# same prompt, different endpoint. gpt-5 deployments require
# `max_completion_tokens` and reject a custom `temperature`. This generator is
# deliberately NOT an `AnthropicGenerator` and exposes no `count_system_tokens`,
# so the cost pre-flight (a capability check in cli.py) auto-skips it.


class OpenAICompatibleGenerator:
    """Generator over any OpenAI-chat-compatible endpoint (sync client)."""

    name = "OpenAICompatibleGenerator"

    def __init__(
        self,
        client: Any,
        model: str,
        repo_root: Path,
        *,
        max_completion_tokens: int = 4096,
        detail: str = "full",
        include_suggested_edits: bool = True,
    ) -> None:
        if detail not in DIAGNOSTIC_DETAIL_MODES:
            raise ValueError(f"detail must be one of {DIAGNOSTIC_DETAIL_MODES}, got {detail!r}")
        self._client = client
        self._model = model
        self._max_completion_tokens = max_completion_tokens
        self._detail = detail
        self._include_suggested_edits = include_suggested_edits
        blocks = _load_cache_blocks(repo_root)
        self._system_text = "\n\n".join(
            [blocks.system_md, blocks.recipes_and_langref, blocks.error_codes, blocks.stdlib_bundle]
        )
        self.stdlib_hash = blocks.stdlib_hash

    @property
    def model(self) -> str:
        return self._model

    def request_kwargs(self, user_text: str) -> dict[str, Any]:
        """Build the chat.completions kwargs. Split out so a unit test can
        assert the gpt-5 branch (max_completion_tokens, no temperature) without
        a live client — the MC-3 hardening guard."""
        kwargs: dict[str, Any] = {
            "model": self._model,
            "messages": [
                {"role": "system", "content": self._system_text},
                {"role": "user", "content": user_text},
            ],
        }
        # gpt-5 family: max_completion_tokens, no custom temperature.
        if self._model.startswith("gpt-5"):
            kwargs["max_completion_tokens"] = self._max_completion_tokens
        else:
            kwargs["max_tokens"] = self._max_completion_tokens
            kwargs["temperature"] = 0.2
        return kwargs

    def generate(self, task: TaskSpec, transcript: list[dict[str, Any]]) -> str:
        user_text = _build_user_message(
            task,
            transcript,
            detail=self._detail,
            include_suggested_edits=self._include_suggested_edits,
        )
        response = self._client.chat.completions.create(**self.request_kwargs(user_text))
        text = response.choices[0].message.content or ""
        return extract_source(text)


def _azure_client_from_env(env_path: Path | None, api_version_default: str) -> Any:
    """AzureOpenAI client from a dotenv (COVENANT_AZURE_* or AZURE_OPENAI_*),
    WITHOUT mutating os.environ or logging any secret."""
    from dotenv import dotenv_values
    from openai import AzureOpenAI

    env: dict[str, str | None] = {}
    if env_path is not None and Path(env_path).is_file():
        env = dict(dotenv_values(env_path))

    def first(*names: str) -> str | None:
        for n in names:
            v = env.get(n) or os.environ.get(n)
            if v:
                return v
        return None

    key = first("COVENANT_AZURE_KEY", "AZURE_OPENAI_API_KEY")
    endpoint = first("COVENANT_AZURE_ENDPOINT", "AZURE_OPENAI_ENDPOINT")
    api_version = first("COVENANT_AZURE_API_VERSION", "AZURE_OPENAI_API_VERSION") or api_version_default
    if not key or not endpoint:
        raise RuntimeError(
            f"Azure creds missing: need COVENANT_AZURE_KEY + COVENANT_AZURE_ENDPOINT "
            f"in {env_path} (or AZURE_OPENAI_* in the environment)."
        )
    return AzureOpenAI(api_key=key, azure_endpoint=endpoint, api_version=api_version)


def build_openai_compatible_generator(
    repo_root: Path,
    *,
    provider: str,
    model: str,
    base_url: str | None = None,
    env_path: Path | None = None,
    max_completion_tokens: int = 4096,
    api_version_default: str = "2025-04-01-preview",
    detail: str = "full",
    include_suggested_edits: bool = True,
) -> OpenAICompatibleGenerator:
    """Build a generator for provider ∈ {azure, openai, vllm}. azure → AzureOpenAI
    from env; openai → OpenAI(api_key); vllm → OpenAI(base_url) for a local
    server. Never logs a secret."""
    if provider == "azure":
        client = _azure_client_from_env(env_path, api_version_default)
    elif provider in ("openai", "vllm"):
        from openai import OpenAI

        if provider == "vllm":
            if not base_url:
                raise RuntimeError(
                    "provider=vllm requires --base-url (e.g. http://localhost:8000/v1)"
                )
            client = OpenAI(base_url=base_url, api_key=os.environ.get("OPENAI_API_KEY", "not-needed"))
        else:
            key = os.environ.get("OPENAI_API_KEY")
            if not key:
                raise RuntimeError("provider=openai requires OPENAI_API_KEY")
            client = OpenAI(api_key=key, base_url=base_url) if base_url else OpenAI(api_key=key)
    else:
        raise RuntimeError(f"unknown openai-compatible provider: {provider!r}")
    return OpenAICompatibleGenerator(
        client=client,
        model=model,
        repo_root=repo_root,
        max_completion_tokens=max_completion_tokens,
        detail=detail,
        include_suggested_edits=include_suggested_edits,
    )


def build_azure_generator(
    repo_root: Path,
    *,
    deployment: str = "gpt-5.5",
    env_path: Path | None = None,
    max_completion_tokens: int = 4096,
    api_version_default: str = "2025-04-01-preview",
    detail: str = "full",
    include_suggested_edits: bool = True,
) -> OpenAICompatibleGenerator:
    """Back-compat wrapper: Azure via the unified OpenAI-compatible builder."""
    return build_openai_compatible_generator(
        repo_root,
        provider="azure",
        model=deployment,
        env_path=env_path,
        max_completion_tokens=max_completion_tokens,
        api_version_default=api_version_default,
        detail=detail,
        include_suggested_edits=include_suggested_edits,
    )
