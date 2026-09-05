"""Tests for the agentic convergence harness.

Unit tests (no API, no binary): prompt rendering, registry resolution, backend
message conversion, tool-call JSON-parse fallback, and summary aggregation.

Integration tests: drive `run_cell` with a deterministic ScriptedBackend
against the REAL sigil-mcp binary (skipped if it isn't built).
"""

from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

# Run without an editable install.
_SRC = Path(__file__).resolve().parents[1] / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from sigil_bench.agentic import registry  # noqa: E402
from sigil_bench.agentic.backends import (  # noqa: E402
    AnthropicToolBackend,
    AssistantTurn,
    OpenAIToolBackend,
    ScriptedBackend,
    ToolCall,
    make_dryrun_turns,
)
from sigil_bench.agentic.experiment import _dump_transcript, summarize  # noqa: E402
from sigil_bench.agentic.loop import CellResult, run_cell  # noqa: E402
from sigil_bench.agentic.prompt import render_system_prompt  # noqa: E402
from sigil_bench.agentic.redteam import (  # noqa: E402
    constant_output_cheat,
    grant_necessity_probe,
    run_cheat_probe,
)
from sigil_bench.agentic.tooling import MCPToolExecutor, model_tool_specs  # noqa: E402
from sigil_bench.config import default_mcp_binary, find_repo_root  # noqa: E402
from sigil_bench.mcp_client import SigilMCP  # noqa: E402
from sigil_bench.runner import capture_ground_truth  # noqa: E402
from sigil_bench.tasks import load_tasks  # noqa: E402

REPO = find_repo_root()
BROKEN = "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return missing; }"


def _echo_task():
    return load_tasks(REPO / "bench" / "tasks", only=["task001_echo"])[0]


def _echo_source() -> str:
    return _echo_task().resolve_source(REPO).read_text(encoding="utf-8")


# ── prompt ───────────────────────────────────────────────────────────────────


def test_prompt_substitutes_task_and_has_no_placeholder():
    rendered = render_system_prompt(_echo_task())
    assert "{{TASK_DESCRIPTION}}" not in rendered
    assert "SIGIL Tool Generation" in rendered
    assert "tool_main" in rendered
    # The task's description text must appear in the substituted block.
    assert "returns its input bytes unchanged" in rendered


def test_tool_specs_are_the_three_advertised_tools():
    names = {t.name for t in model_tool_specs()}
    assert names == {"sigil_check", "sigil_forge", "sigil_lookup_error"}


# ── red-team instrument (unit) ───────────────────────────────────────────────


def test_constant_output_cheat_emits_fixed_bytes():
    src = constant_output_cheat("AB")  # 'A'=65, 'B'=66
    assert "alloc(2)" in src
    assert "store8(out + 0, 65)" in src
    assert "store8(out + 1, 66)" in src
    assert "* 4294967296 + 2;" in src
    assert "! { Alloc }" in src  # no NetIO/FFI — does no real I/O


# ── registry ─────────────────────────────────────────────────────────────────


def test_resolve_registry_key_and_passthrough():
    assert registry.resolve_model("claude-sonnet").provider == "anthropic"
    pt = registry.resolve_model("or:deepseek/deepseek-chat")
    assert pt.provider == "openrouter"
    assert pt.api_model_id == "deepseek/deepseek-chat"
    with pytest.raises(KeyError):
        registry.resolve_model("totally-unknown-model")


# ── backend message conversion (fake clients) ────────────────────────────────


class _FakeAnthropic:
    def __init__(self):
        self.captured = None
        self.messages = SimpleNamespace(create=self._create)

    def _create(self, **kwargs):
        self.captured = kwargs
        return SimpleNamespace(
            content=[
                SimpleNamespace(type="text", text="ok"),
                SimpleNamespace(type="tool_use", id="tu_1", name="sigil_check", input={"source": "x"}),
            ],
            usage=SimpleNamespace(input_tokens=11, output_tokens=7),
            stop_reason="tool_use",
        )


def test_anthropic_backend_renders_tool_roundtrip():
    be = AnthropicToolBackend(_FakeAnthropic(), "claude-x")
    messages = [
        {"role": "user", "text": "hi"},
        {"role": "assistant", "text": "", "tool_calls": [{"id": "a", "name": "sigil_check", "arguments": {"source": "s"}}]},
        {"role": "tool", "results": [{"id": "a", "name": "sigil_check", "output": "{\"status\":\"error\"}"}]},
    ]
    turn = be.converse("SYS", model_tool_specs(), messages)
    assert turn.tool_calls[0].name == "sigil_check"
    assert turn.usage == {"input_tokens": 11, "output_tokens": 7}
    sent = be._client.captured["messages"]
    # assistant tool_use then a user tool_result with matching id.
    assert sent[1]["content"][0]["type"] == "tool_use"
    assert sent[2]["content"][0]["type"] == "tool_result"
    assert sent[2]["content"][0]["tool_use_id"] == "a"


class _FakeOpenAI:
    def __init__(self, arguments: str):
        self._args = arguments
        self.captured = None
        self.chat = SimpleNamespace(completions=SimpleNamespace(create=self._create))

    def _create(self, **kwargs):
        self.captured = kwargs
        tc = SimpleNamespace(
            id="call_1",
            function=SimpleNamespace(name="sigil_check", arguments=self._args),
        )
        msg = SimpleNamespace(content="thinking", tool_calls=[tc])
        return SimpleNamespace(
            choices=[SimpleNamespace(message=msg, finish_reason="tool_calls")],
            usage=SimpleNamespace(prompt_tokens=20, completion_tokens=5),
        )


def test_openai_backend_parses_tool_args():
    be = OpenAIToolBackend(_FakeOpenAI('{"source": "abc"}'), "gpt-x")
    turn = be.converse("SYS", model_tool_specs(), [{"role": "user", "text": "hi"}])
    assert turn.tool_calls[0].arguments == {"source": "abc"}
    assert turn.usage == {"input_tokens": 20, "output_tokens": 5}
    # system prompt rendered as first message.
    assert be._client.captured["messages"][0]["role"] == "system"


def test_openai_backend_tolerates_bad_tool_json():
    be = OpenAIToolBackend(_FakeOpenAI("{not valid json"), "gpt-x")
    turn = be.converse("SYS", model_tool_specs(), [{"role": "user", "text": "hi"}])
    tc = turn.tool_calls[0]
    assert tc.arguments == {}
    assert tc.raw_arguments == "{not valid json"


def test_openai_renders_empty_assistant_content_as_string_not_null():
    # A tool-calling assistant turn with no text must render content as ""
    # (some OpenAI-compatible providers reject null content), and tool results
    # must be strings.
    be = OpenAIToolBackend(_FakeOpenAI('{"source": "x"}'), "gpt-x")
    messages = [
        {"role": "user", "text": "hi"},
        {"role": "assistant", "text": "", "tool_calls": [{"id": "a", "name": "sigil_check", "arguments": {"source": "s"}}]},
        {"role": "tool", "results": [{"id": "a", "name": "sigil_check", "output": "{}"}]},
    ]
    be.converse("SYS", model_tool_specs(), messages)
    sent = be._client.captured["messages"]
    asst = next(m for m in sent if m["role"] == "assistant")
    assert asst["content"] == ""  # not None
    assert asst["tool_calls"][0]["id"] == "a"
    toolmsg = next(m for m in sent if m["role"] == "tool")
    assert isinstance(toolmsg["content"], str)


# ── aggregation ──────────────────────────────────────────────────────────────


def _cell(**kw) -> CellResult:
    base = dict(
        model_key="m", display_name="M", provider="anthropic", task_id="t", run_index=0,
        first_pass_success=False, attempts_to_success=None, check_attempts=0,
        final_outcome="gave_up", diagnostic_codes={}, distinct_codes=[],
        grants_requested=[], final_source_correct=None,
    )
    base.update(kw)
    return CellResult(**base)


def test_dump_transcript_sanitizes_passthrough_model_key(tmp_path):
    # Passthrough keys ("or:openai/gpt-4o") contain ':' and '/' — illegal in
    # filesystem paths. _dump_transcript must sanitize the dir name and not crash.
    r = _cell(model_key="or:openai/gpt-4o", task_id="task001_echo")
    _dump_transcript(tmp_path, r)
    written = list(tmp_path.rglob("*.json"))
    assert len(written) == 1
    assert ":" not in str(written[0].parent.name) and "/" not in written[0].parent.name


def test_summarize_rates_and_codes():
    cells = [
        _cell(first_pass_success=True, attempts_to_success=1, check_attempts=1,
              final_outcome="success", final_source_correct=True,
              diagnostic_codes={}),
        _cell(attempts_to_success=3, check_attempts=3, final_outcome="success",
              final_source_correct=False, diagnostic_codes={"T060": 2, "R001": 1},
              grants_requested=[{"net": ["api.github.com"]}]),
        _cell(final_outcome="hit_cap", check_attempts=6, diagnostic_codes={"T060": 6}),
    ]
    s = summarize(cells)
    blk = s["by_model"]["m"]
    assert blk["cells"] == 3
    assert blk["first_pass_success_rate"] == pytest.approx(1 / 3, abs=1e-3)
    assert blk["success_rate"] == pytest.approx(2 / 3, abs=1e-3)
    assert blk["final_correct_rate"] == pytest.approx(1 / 2, abs=1e-3)  # 2 verified, 1 correct
    assert blk["mean_attempts_to_success"] == pytest.approx(2.0)
    assert blk["outcome_counts"]["hit_cap"] == 1
    assert blk["grant_kinds_requested"] == {"net": 1}
    assert s["overall_diagnostic_code_frequency"]["T060"] == 8


def test_summarize_de_errors_and_tracks_served_models():
    cells = [
        _cell(final_outcome="success", first_pass_success=True, served_models=["claude-fable-5"]),
        _cell(final_outcome="success", served_models=["claude-fable-5"]),
        _cell(final_outcome="hit_cap", served_models=["claude-fable-5"]),
        _cell(final_outcome="harness_error", served_models=[], error="credit too low"),
    ]
    blk = summarize(cells)["by_model"]["m"]
    assert blk["cells"] == 4
    assert blk["harness_error_cells"] == 1
    # de-errored denominator excludes the outage cell: 2 success / 3 clean
    assert blk["success_rate"] == pytest.approx(2 / 3, abs=1e-3)
    # raw rate counts the outage as a failure: 2 / 4
    assert blk["success_rate_incl_errors"] == pytest.approx(0.5, abs=1e-3)
    # model provenance aggregated across cells
    assert blk["served_models"] == {"claude-fable-5": 3}


# ── compose-failure counts as a failed check (no binary needed) ──────────────


def test_compose_failure_counts_as_failed_check(monkeypatch):
    ex = MCPToolExecutor(object(), _echo_task(), REPO, max_check_attempts=2, fuel=1000, compose_stdlib=False)

    def boom(_src):
        raise RuntimeError("stdlib link boom")

    monkeypatch.setattr(ex, "_compose", boom)
    _out, ctrl = ex.execute("sigil_check", {"source": "module x; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }"})
    assert ex.check_attempts == 1
    assert ex.first_check_ok is False
    assert ctrl.stop is False
    _out2, ctrl2 = ex.execute("sigil_check", {"source": "module x; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }"})
    assert ex.check_attempts == 2
    assert ctrl2.stop is True and ctrl2.reason == "hit_cap"
    assert ex.hit_cap is True


# ── integration: real sigil-mcp binary ───────────────────────────────────────


@pytest.fixture(scope="module")
def mcp_factory():
    binary = default_mcp_binary(REPO)
    if not binary.is_file():
        pytest.skip(f"sigil-mcp not built at {binary} (cargo build -p sigil-mcp)")

    def factory():
        mcp = SigilMCP.spawn(binary)
        mcp.initialize()
        return mcp
    return factory


_LIVE: dict = {}


def _live_factory():
    if "f" not in _LIVE:
        binary = default_mcp_binary(REPO)

        def factory():
            mcp = SigilMCP.spawn(binary)
            mcp.initialize()
            return mcp

        _LIVE["f"] = factory
    return _LIVE["f"]


def _run(backend, *, max_attempts=6):
    return run_cell(
        model_key="stub", display_name="Stub", provider="stub",
        backend=backend, task=_echo_task(), mcp_factory=_live_factory(),
        repo_root=REPO, max_check_attempts=max_attempts, verify_final=True,
    )


@pytest.mark.usefixtures("mcp_factory")
def test_integration_broken_then_good_converges():
    src = _echo_source()
    backend = ScriptedBackend([
        AssistantTurn("try1", [ToolCall("c1", "sigil_check", {"source": BROKEN})], "tool_use"),
        AssistantTurn("fix", [ToolCall("c2", "sigil_check", {"source": src})], "tool_use"),
        AssistantTurn("run", [ToolCall("c3", "sigil_forge", {"source": src, "input": "hello"})], "tool_use"),
        AssistantTurn("done", [], "end_turn"),
    ])
    r = _run(backend)
    assert r.first_pass_success is False
    assert r.attempts_to_success == 2
    assert r.check_attempts == 2
    assert r.final_outcome == "success"
    assert r.final_source_correct is True
    assert r.forge_calls == 1
    assert "T060" in r.diagnostic_codes  # undefined `missing`


@pytest.mark.usefixtures("mcp_factory")
def test_integration_first_pass_success():
    backend = ScriptedBackend([
        AssistantTurn("here", [ToolCall("c1", "sigil_check", {"source": _echo_source()})], "tool_use"),
    ])
    r = _run(backend)
    assert r.first_pass_success is True
    assert r.attempts_to_success == 1
    assert r.final_outcome == "success"


@pytest.mark.usefixtures("mcp_factory")
def test_integration_hit_cap():
    turns = [AssistantTurn(f"t{i}", [ToolCall(f"c{i}", "sigil_check", {"source": BROKEN})], "tool_use") for i in range(5)]
    backend = ScriptedBackend(turns)
    r = _run(backend, max_attempts=3)
    assert r.final_outcome == "hit_cap"
    assert r.check_attempts == 3
    assert r.attempts_to_success is None
    assert r.first_pass_success is False


@pytest.mark.usefixtures("mcp_factory")
def test_integration_dryrun_script():
    backend = ScriptedBackend(make_dryrun_turns(_echo_source()))
    r = _run(backend)
    assert r.final_outcome == "success"
    assert r.final_source_correct is True


@pytest.mark.usefixtures("mcp_factory")
def test_redteam_constant_cheat_resisted_by_multi_output_task():
    # A constant cheat (built from one input's expected output) compiles but
    # CANNOT pass a task whose inputs map to several distinct outputs (rot13).
    task = load_tasks(REPO / "bench" / "tasks", only=["task020_rot13"])[0]
    with _live_factory()() as mcp:
        gt = capture_ground_truth(task, REPO, mcp)
        nonempty = next(v for v in gt.values() if v)
        cheat = constant_output_cheat(nonempty)
        probe = run_cheat_probe(task, cheat, mcp, REPO, expected_outputs=gt)
        g = grant_necessity_probe(task, cheat, mcp, REPO)
    assert probe["compiles"] is True
    assert probe["gamed"] is False  # 5 distinct outputs defeat a constant
    assert g["applicable"] is False  # rot13 needs no grants


@pytest.mark.usefixtures("mcp_factory")
def test_integration_stop_mid_batch_skips_later_calls():
    # One turn with TWO tool calls: a failing check that trips the cap, then a
    # forge. With cap=1, the forge must NOT run (we break the moment the cap
    # trips), so forge_calls stays 0.
    src = _echo_source()
    backend = ScriptedBackend([
        AssistantTurn("both", [
            ToolCall("c1", "sigil_check", {"source": BROKEN}),
            ToolCall("c2", "sigil_forge", {"source": src, "input": "hello"}),
        ], "tool_use"),
    ])
    r = _run(backend, max_attempts=1)
    assert r.final_outcome == "hit_cap"
    assert r.check_attempts == 1
    assert r.forge_calls == 0  # second call in the batch was skipped
