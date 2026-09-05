"""Tests for the SigilMCP Python client.

Spawns the real sigil-mcp binary and exercises every method end-to-end.
Catches subprocess / line-framing / shutdown bugs before they ever reach
the LLM-driven part of the harness.

Skipped if the binary doesn't exist (build with `cargo build --release -p sigil-mcp`).
"""

from __future__ import annotations

import pytest

from sigil_bench.config import load_settings
from sigil_bench.mcp_client import MCPError, SigilMCP


@pytest.fixture(scope="module")
def binary_path():
    settings = load_settings()
    if not settings.mcp_binary.is_file():
        pytest.skip(
            f"sigil-mcp binary not found at {settings.mcp_binary}. "
            "Run `cargo build --release -p sigil-mcp` first."
        )
    return settings.mcp_binary


def test_initialize_returns_server_info(binary_path):
    with SigilMCP.spawn(binary_path) as mcp:
        info = mcp.initialize()
    assert info["serverInfo"]["name"] == "sigil-mcp"
    assert info["protocolVersion"] == "2024-11-05"
    assert "tools" in info["capabilities"]


def test_list_tools_returns_four_tools(binary_path):
    """Phase 5a-1.5 added `sigil_inspect_uses` for the parse-aware verifier."""
    with SigilMCP.spawn(binary_path) as mcp:
        tools = mcp.list_tools()
    names = [t["name"] for t in tools]
    assert names == [
        "sigil_check",
        "sigil_forge",
        "sigil_lookup_error",
        "sigil_inspect_uses",
    ]
    for tool in tools:
        assert tool["inputSchema"]["type"] == "object"


def test_check_success_envelope(binary_path):
    src = "module sigil; fn boot() -> i64 { return 42; }"
    with SigilMCP.spawn(binary_path) as mcp:
        env = mcp.check(src)
    assert env["status"] == "ok"
    assert env["command"] == "check"
    assert env["data"]["primary_module"] == "sigil"


def test_check_error_envelope_carries_diagnostics(binary_path):
    src = "module sigil; fn boot() -> bool { return ready; }"
    with SigilMCP.spawn(binary_path) as mcp:
        env = mcp.check(src)
    assert env["status"] == "error"
    diags = env["diagnostics"]
    assert diags, "expected at least one diagnostic"
    first = diags[0]
    assert first["code"] == "T060"
    assert first["title"] == "Undefined local"
    assert isinstance(first["hint"], str) and first["hint"]


def test_lookup_error_returns_registry_entry(binary_path):
    with SigilMCP.spawn(binary_path) as mcp:
        env = mcp.lookup_error("R001")
    assert env["status"] == "ok"
    assert env["data"]["code"] == "R001"
    assert env["data"]["category"] == "Ring"
    assert "default_hint" in env["data"]


def test_lookup_error_unknown_code(binary_path):
    with SigilMCP.spawn(binary_path) as mcp:
        env = mcp.lookup_error("X999")
    assert env["status"] == "error"
    assert "X999" in env["diagnostics"][0]["message"]


def test_forge_runs_a_trivial_tool(binary_path):
    src = (
        "module tool; "
        "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }"
    )
    with SigilMCP.spawn(binary_path) as mcp:
        env = mcp.forge(src, input="")
    assert env["status"] == "ok"
    assert env["command"] == "forge"
    assert env["data"]["output_bytes"] == 0


def test_forge_byte_passthrough(binary_path):
    """Verifies a tool that loops alloc/load8/store8 round-trips through MCP."""
    src = """
        module tool;
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
            let out_ptr = alloc(input_len);
            let mut i: i64 = 0;
            while i < input_len {
                let b = load8(input_ptr + i);
                store8(out_ptr + i, b);
                i = i + 1;
            }
            return out_ptr * 4294967296 + input_len;
        }
    """
    with SigilMCP.spawn(binary_path) as mcp:
        env = mcp.forge(src, input="hello")
    assert env["status"] == "ok", f"envelope: {env}"
    assert env["data"]["output_text"] == "hello"
    assert env["data"]["fuel_consumed"] > 0


def test_forge_compile_failure_returns_diagnostics(binary_path):
    """Tool source missing tool_main → S002."""
    src = "module tool; fn helper() -> i64 { return 0; }"
    with SigilMCP.spawn(binary_path) as mcp:
        env = mcp.forge(src)
    assert env["status"] == "error"
    assert any(d["code"] == "S002" for d in env["diagnostics"])


def test_unknown_method_raises_mcp_error(binary_path):
    with SigilMCP.spawn(binary_path) as mcp:
        with pytest.raises(MCPError) as exc_info:
            mcp._request("nope/nope")
    assert "nope/nope" in str(exc_info.value)


def test_id_round_trips(binary_path):
    """Two requests in a row both get matching ids."""
    with SigilMCP.spawn(binary_path) as mcp:
        info1 = mcp.initialize()
        info2 = mcp.initialize()
    # Same data, but the client matched ids correctly across calls.
    assert info1["serverInfo"]["name"] == info2["serverInfo"]["name"]
