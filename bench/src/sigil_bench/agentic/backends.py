"""Provider-neutral tool-use backends.

The agentic loop is provider-agnostic: it maintains a NEUTRAL message history
and asks a `Backend` to produce the next assistant turn. Two concrete backends
render that neutral history into a provider's wire format and parse the reply
back into the neutral shape:

  * `AnthropicToolBackend` — Anthropic Messages API (`tool_use` / `tool_result`)
  * `OpenAIToolBackend`    — OpenAI-compatible chat completions (`tools` / `role:tool`)

Plus `ScriptedBackend`, a deterministic stub that emits a fixed sequence of
assistant turns (used by `--dry-run` and the unit tests — zero API cost).

Neutral message shapes (plain dicts so transcripts serialize to JSON):
  {"role": "user", "text": str}
  {"role": "assistant", "text": str, "tool_calls": [ToolCall-as-dict, ...]}
  {"role": "tool", "results": [{"id", "name", "output"}, ...]}
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Protocol

# Transient failures worth a bounded in-cell retry (Azure Foundry drops connections under sustained
# load — M3 evidence — and a lost cell would silently depress the frozen model's score). Auth/4xx/
# validation errors are NOT here: they re-raise immediately (run_cell → harness_error, fail-closed).
_TRANSIENT_EXC_SUBSTRINGS = (
    "Connection", "Timeout", "RateLimit", "InternalServer", "ServiceUnavailable", "APIError",
)


def _is_transient(exc: BaseException) -> bool:
    return any(s in type(exc).__name__ for s in _TRANSIENT_EXC_SUBSTRINGS)


def _create_with_retry(create_fn: Callable[[], Any], *, tries: int = 4) -> Any:
    """Call `create_fn()`, retrying ONLY transient errors with bounded exponential backoff
    (2/4/8/15s). Non-transient errors re-raise at once; the final transient re-raises after `tries`."""
    for i in range(tries):
        try:
            return create_fn()
        except Exception as e:  # noqa: BLE001 — classified below; non-transient re-raises
            if not _is_transient(e) or i == tries - 1:
                raise
            time.sleep(min(2.0 * (2 ** i), 15.0))
    raise RuntimeError("unreachable")  # pragma: no cover


@dataclass
class ToolSpec:
    name: str
    description: str
    input_schema: dict[str, Any]


@dataclass
class ToolCall:
    id: str
    name: str
    arguments: dict[str, Any]
    # Raw arguments string when the model emitted un-parseable JSON (rare but
    # real with weaker models); kept so the transcript shows what happened.
    raw_arguments: str | None = None

    def as_dict(self) -> dict[str, Any]:
        d = {"id": self.id, "name": self.name, "arguments": self.arguments}
        if self.raw_arguments is not None:
            d["raw_arguments"] = self.raw_arguments
        return d


@dataclass
class AssistantTurn:
    text: str = ""
    tool_calls: list[ToolCall] = field(default_factory=list)
    stop_reason: str = ""
    usage: dict[str, int] = field(default_factory=dict)
    # The model the provider reports actually served this turn (`response.model`).
    # Model-provenance audit: confirms the served model matches what was requested.
    served_model: str = ""
    # Provider-opaque raw assistant content for verbatim replay. Anthropic
    # extended thinking REQUIRES the prior turn's `thinking` blocks (with their
    # signatures) to be replayed before the tool_use blocks, or the next call
    # is rejected — so we round-trip the exact content blocks here.
    raw_content: Any = None


class Backend(Protocol):
    def converse(
        self, system: str, tools: list[ToolSpec], messages: list[dict[str, Any]]
    ) -> AssistantTurn: ...


def close_backend(backend: Any) -> None:
    """Best-effort release of a backend's underlying HTTP client."""
    client = getattr(backend, "_client", None)
    closer = getattr(client, "close", None)
    if callable(closer):
        try:
            closer()
        except Exception:  # noqa: BLE001 — cleanup must never raise
            pass


# ── Anthropic ────────────────────────────────────────────────────────────────


class AnthropicToolBackend:
    def __init__(
        self, client: Any, model_id: str, *, max_tokens: int = 4096,
        thinking: bool = False, effort: str = "high", temperature: float | None = None,
    ) -> None:
        self._client = client
        self._model = model_id
        self._effort = effort
        self._temperature = temperature  # pin (0.0) for a deterministic frozen model; None = SDK default
        # Fable/Mythos 5 have thinking ALWAYS ON (an explicit `{type:"disabled"}`
        # 400s, and thinking blocks must be replayed across tool-use turns) — so
        # treat them as thinking-on regardless of the flag, or a multi-turn run
        # 400s on turn 2 when the reconstructed assistant message lacks its
        # thinking block.
        always_think = model_id.startswith(("claude-fable", "claude-mythos"))
        self._thinking = thinking or always_think
        # Adaptive thinking emits reasoning + the answer in one response; give it
        # room. 16000 is the safe non-streaming ceiling (the SDK refuses larger
        # non-streaming requests). Modern Claude (Opus 4.6+/Sonnet 4.6/Fable 5)
        # uses adaptive thinking — NOT the removed `{type:"enabled",budget_tokens}`
        # form, which 400s on Opus 4.7/4.8/Fable 5.
        self._max_tokens = max(max_tokens, 16000) if self._thinking else max_tokens

    @staticmethod
    def _render(messages: list[dict[str, Any]]) -> list[dict[str, Any]]:
        out: list[dict[str, Any]] = []
        for m in messages:
            role = m["role"]
            if role == "user":
                out.append({"role": "user", "content": [{"type": "text", "text": m["text"]}]})
            elif role == "assistant":
                # Replay the exact prior content blocks when present (preserves
                # thinking blocks + signatures required by extended thinking).
                if m.get("_raw"):
                    out.append({"role": "assistant", "content": m["_raw"]})
                    continue
                content: list[dict[str, Any]] = []
                if m.get("text"):
                    content.append({"type": "text", "text": m["text"]})
                for tc in m.get("tool_calls", []):
                    content.append({
                        "type": "tool_use",
                        "id": tc["id"],
                        "name": tc["name"],
                        "input": tc["arguments"],
                    })
                if not content:  # API rejects empty assistant content
                    content.append({"type": "text", "text": "(no output)"})
                out.append({"role": "assistant", "content": content})
            elif role == "tool":
                content = [
                    {"type": "tool_result", "tool_use_id": r["id"], "content": r["output"]}
                    for r in m["results"]
                ]
                out.append({"role": "user", "content": content})
        return out

    def converse(
        self, system: str, tools: list[ToolSpec], messages: list[dict[str, Any]]
    ) -> AssistantTurn:
        anth_tools = [
            {"name": t.name, "description": t.description, "input_schema": t.input_schema}
            for t in tools
        ]
        kwargs: dict[str, Any] = {
            "model": self._model,
            "max_tokens": self._max_tokens,
            "system": system,
            "tools": anth_tools,
            "messages": self._render(messages),
        }
        if self._thinking:
            # Adaptive thinking + effort is the modern Claude reasoning surface
            # (Opus 4.6+/Sonnet 4.6); interleaved thinking with tools is enabled
            # automatically, no beta header needed.
            kwargs["thinking"] = {"type": "adaptive"}
            kwargs["output_config"] = {"effort": self._effort}
        elif self._temperature is not None:
            # Pin temperature only when NOT using adaptive thinking (they conflict).
            kwargs["temperature"] = self._temperature
        resp = self._client.messages.create(**kwargs)
        text_parts: list[str] = []
        tool_calls: list[ToolCall] = []
        for block in resp.content:
            btype = getattr(block, "type", None)
            if btype == "text":
                text_parts.append(block.text)
            elif btype == "tool_use":
                tool_calls.append(
                    ToolCall(id=block.id, name=block.name, arguments=dict(block.input or {}))
                )
        usage = {
            "input_tokens": int(getattr(resp.usage, "input_tokens", 0) or 0),
            "output_tokens": int(getattr(resp.usage, "output_tokens", 0) or 0),
        }
        # Round-trip the exact content blocks (thinking + text + tool_use) so
        # the next turn can replay them — mandatory for thinking + tool use.
        raw_content = [b.model_dump() for b in resp.content] if self._thinking else None
        return AssistantTurn(
            text="\n".join(text_parts).strip(),
            tool_calls=tool_calls,
            stop_reason=getattr(resp, "stop_reason", "") or "",
            usage=usage,
            served_model=getattr(resp, "model", "") or "",
            raw_content=raw_content,
        )


# ── OpenAI-compatible ────────────────────────────────────────────────────────


class OpenAIToolBackend:
    def __init__(
        self, client: Any, model_id: str, *, max_tokens: int = 4096,
        temperature: float | None = None, seed: int | None = None,
    ) -> None:
        self._client = client
        self._model = model_id
        self._max_tokens = max_tokens
        self._temperature = temperature  # pin for determinism; skipped for gpt-5* (rejects temperature)
        self._seed = seed  # best-effort reproducibility for gpt-5* (which can't take temperature)

    @staticmethod
    def _render(system: str, messages: list[dict[str, Any]]) -> list[dict[str, Any]]:
        out: list[dict[str, Any]] = [{"role": "system", "content": system}]
        for m in messages:
            role = m["role"]
            if role == "user":
                out.append({"role": "user", "content": m["text"]})
            elif role == "assistant":
                # Use "" not None for empty content: OpenAI permits null
                # alongside tool_calls, but several OpenAI-compatible providers
                # (Mistral, Moonshot, some Nebius models) reject a null content
                # field. An empty string is universally accepted.
                msg: dict[str, Any] = {"role": "assistant", "content": m.get("text") or ""}
                tcs = m.get("tool_calls", [])
                if tcs:
                    msg["tool_calls"] = [
                        {
                            "id": tc["id"],
                            "type": "function",
                            "function": {
                                "name": tc["name"],
                                "arguments": json.dumps(tc["arguments"]),
                            },
                        }
                        for tc in tcs
                    ]
                out.append(msg)
            elif role == "tool":
                for r in m["results"]:
                    # `content` MUST be a string per the API; coerce defensively.
                    out.append({
                        "role": "tool",
                        "tool_call_id": r.get("id"),
                        "content": str(r.get("output", "")),
                    })
        return out

    def converse(
        self, system: str, tools: list[ToolSpec], messages: list[dict[str, Any]]
    ) -> AssistantTurn:
        oa_tools = [
            {
                "type": "function",
                "function": {
                    "name": t.name,
                    "description": t.description,
                    "parameters": t.input_schema,
                },
            }
            for t in tools
        ]
        kwargs: dict[str, Any] = {
            "model": self._model,
            "messages": self._render(system, messages),
            "tools": oa_tools,
            "tool_choice": "auto",
        }
        # gpt-5* deployments use max_completion_tokens; everything else max_tokens.
        if str(self._model).startswith("gpt-5"):
            kwargs["max_completion_tokens"] = self._max_tokens
        else:
            kwargs["max_tokens"] = self._max_tokens
            # gpt-5* rejects a custom temperature; only pin it for non-gpt-5 models.
            if self._temperature is not None:
                kwargs["temperature"] = self._temperature
        if self._seed is not None:
            kwargs["seed"] = self._seed  # best-effort determinism (esp. gpt-5*, which can't take temperature)

        resp = _create_with_retry(lambda: self._client.chat.completions.create(**kwargs))
        choice = resp.choices[0]
        msg = choice.message
        tool_calls: list[ToolCall] = []
        for tc in (getattr(msg, "tool_calls", None) or []):
            raw = tc.function.arguments or "{}"
            try:
                args = json.loads(raw)
                if not isinstance(args, dict):
                    args, raw_kept = {}, raw
                else:
                    raw_kept = None
            except (json.JSONDecodeError, ValueError):
                args, raw_kept = {}, raw
            tool_calls.append(
                ToolCall(id=tc.id, name=tc.function.name, arguments=args, raw_arguments=raw_kept)
            )
        usage_obj = getattr(resp, "usage", None)
        usage = {
            "input_tokens": int(getattr(usage_obj, "prompt_tokens", 0) or 0),
            "output_tokens": int(getattr(usage_obj, "completion_tokens", 0) or 0),
        }
        return AssistantTurn(
            text=(msg.content or "").strip(),
            tool_calls=tool_calls,
            stop_reason=getattr(choice, "finish_reason", "") or "",
            usage=usage,
            served_model=getattr(resp, "model", "") or "",
        )


# ── Scripted stub (no API; tests + --dry-run) ────────────────────────────────


class ScriptedBackend:
    """Plays a fixed list of `AssistantTurn`s in order. When the script is
    exhausted, returns an empty end-of-turn (the loop then terminates)."""

    def __init__(self, turns: list[AssistantTurn], *, name: str = "scripted") -> None:
        self._turns = list(turns)
        self._i = 0
        self.name = name

    def converse(
        self, system: str, tools: list[ToolSpec], messages: list[dict[str, Any]]
    ) -> AssistantTurn:
        if self._i >= len(self._turns):
            return AssistantTurn(text="(done)", stop_reason="end_turn")
        turn = self._turns[self._i]
        self._i += 1
        return turn


_STUB_CALL_SEQ = [0]


def _stub_call_id() -> str:
    _STUB_CALL_SEQ[0] += 1
    return f"stub_call_{_STUB_CALL_SEQ[0]}"


def make_dryrun_turns(reference_source: str, *, grants: dict[str, Any] | None = None) -> list[AssistantTurn]:
    """A deterministic 4-step script exercising the full loop offline:
    a broken `sigil_check` → a passing `sigil_check` (reference source) →
    a `sigil_forge` → an end-of-turn. Yields metrics: first_pass=False,
    attempts_to_success=2, outcome=success, forge_ran=True."""
    broken = "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return missing; }"
    forge_args: dict[str, Any] = {"source": reference_source, "input": ""}
    if grants:
        forge_args["grants"] = grants
    return [
        AssistantTurn(
            text="First attempt.",
            tool_calls=[ToolCall(_stub_call_id(), "sigil_check", {"source": broken})],
            stop_reason="tool_use",
        ),
        AssistantTurn(
            text="Fixing the undefined identifier.",
            tool_calls=[ToolCall(_stub_call_id(), "sigil_check", {"source": reference_source})],
            stop_reason="tool_use",
        ),
        AssistantTurn(
            text="Compiles. Executing.",
            tool_calls=[ToolCall(_stub_call_id(), "sigil_forge", forge_args)],
            stop_reason="tool_use",
        ),
        AssistantTurn(text="Done — the tool works.", stop_reason="end_turn"),
    ]
