"""Python client for the sigil-mcp server.

Mirrors `crates/sigil-mcp/tests/protocol.rs::Server` shape for shape-parity
with what real agent harnesses do. Spawns the binary, sends newline-delimited
JSON-RPC 2.0, reads responses.

Usage:
    with SigilMCP.spawn(binary_path) as mcp:
        mcp.initialize()
        envelope = mcp.check(source)
        ...
"""

from __future__ import annotations

import json
import os
import select
import subprocess
import threading
from collections import deque
from pathlib import Path
from typing import Any


class MCPError(RuntimeError):
    """Raised when the server returns a JSON-RPC error or the wire is broken."""

    def __init__(self, message: str, *, rpc: dict[str, Any] | None = None) -> None:
        super().__init__(message)
        self.rpc = rpc


class MCPTimeout(MCPError):
    """The server did not respond within the read deadline — almost always a model-authored
    program that hangs the oracle in an unbounded compile/verify loop (the WASM fuel limit only
    bounds *execution*). The offending child process is killed before this is raised, so a caller
    can catch it, respawn the client, score the task as failed, and continue."""


class SigilMCP:
    """Subprocess-backed MCP client. Use `spawn` (or the context manager) to
    create one; never call `__init__` directly."""

    def __init__(
        self,
        proc: subprocess.Popen[str],
        stderr_log: deque[str],
        reader_thread: threading.Thread,
        timeout: float | None = 90.0,
    ) -> None:
        self._proc = proc
        self._stderr_log = stderr_log
        self._reader = reader_thread
        self._next_id = 1
        self._closed = False
        # Per-request read deadline. A well-formed forge returns in well under a second (execution
        # is fuel-bounded); anything past this is a hang in compile/verify, so we give up on it.
        self._timeout = timeout

    # ── Lifecycle ─────────────────────────────────────────────────────────

    @classmethod
    def spawn(cls, binary_path: Path, timeout: float | None = 90.0) -> "SigilMCP":
        if not binary_path.is_file():
            raise FileNotFoundError(
                f"sigil-mcp binary not found at {binary_path}. "
                "Run `cargo build --release -p sigil-mcp` first."
            )
        proc = subprocess.Popen(
            [str(binary_path)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            bufsize=1,  # line-buffered
            # The bench runs a solver-off `sigil-mcp` build and legitimately
            # EXECUTES tools to measure model output — it is a benchmark, not a
            # security gate. `sigil_forge` now fails closed on a solver-off build
            # (R817) unless this override is set, so opt into it here (the same
            # override the Rust protocol tests use). This restores the pre-gate
            # behaviour for the harness without weakening the gate for real use.
            env={**os.environ, "SIGIL_ALLOW_UNVERIFIED_CERT": "1"},
        )
        # Cap stderr capture so a chatty server can't OOM the harness.
        stderr_log: deque[str] = deque(maxlen=200)

        def drain_stderr() -> None:
            assert proc.stderr is not None
            for line in proc.stderr:
                stderr_log.append(line.rstrip())

        reader = threading.Thread(target=drain_stderr, daemon=True)
        reader.start()
        return cls(proc, stderr_log, reader, timeout=timeout)

    def __enter__(self) -> "SigilMCP":
        return self

    def __exit__(self, *_exc: Any) -> None:
        self.close()

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        try:
            if self._proc.stdin and not self._proc.stdin.closed:
                self._proc.stdin.close()
        except (BrokenPipeError, OSError):
            pass
        try:
            self._proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self._proc.kill()
            self._proc.wait(timeout=2)

    @property
    def stderr_log(self) -> list[str]:
        return list(self._stderr_log)

    # ── Wire-level request ────────────────────────────────────────────────

    def _request(self, method: str, params: Any = None) -> dict[str, Any]:
        if self._closed:
            raise MCPError("client is closed")
        request_id = self._next_id
        self._next_id += 1
        payload = {
            "jsonrpc": "2.0",
            "id": request_id,
            "method": method,
            "params": params if params is not None else {},
        }
        line = json.dumps(payload, separators=(",", ":")) + "\n"
        assert self._proc.stdin is not None
        try:
            self._proc.stdin.write(line)
            self._proc.stdin.flush()
        except (BrokenPipeError, OSError) as e:
            raise MCPError(f"failed writing request: {e}") from e

        assert self._proc.stdout is not None
        if self._timeout is not None:
            # Each response is a single newline-terminated line the server writes atomically, so a
            # readable fd means the full line is available. No readiness within the deadline means
            # the oracle is wedged (spinning on a pathological program); kill it so it stops
            # burning CPU and raise a recoverable timeout.
            ready, _, _ = select.select([self._proc.stdout], [], [], self._timeout)
            if not ready:
                self._proc.kill()  # SIGKILL: stops the CPU-spinning oracle at once
                try:
                    self._proc.wait(timeout=5)  # reap it so no zombie lingers
                except subprocess.TimeoutExpired:
                    pass
                self._closed = True
                stderr_tail = "\n".join(self.stderr_log[-10:])
                raise MCPTimeout(
                    f"no response to {method} within {self._timeout}s; server killed. "
                    f"stderr tail:\n{stderr_tail}"
                )
        response_line = self._proc.stdout.readline()
        if not response_line:
            stderr_tail = "\n".join(self.stderr_log[-10:])
            raise MCPError(
                f"server closed stdout before responding to {method}; "
                f"stderr tail:\n{stderr_tail}"
            )
        try:
            response = json.loads(response_line)
        except json.JSONDecodeError as e:
            raise MCPError(
                f"non-JSON response: {e}\nline: {response_line!r}"
            ) from e
        if response.get("jsonrpc") != "2.0":
            raise MCPError(f"missing jsonrpc=2.0 marker: {response}", rpc=response)
        if response.get("id") != request_id:
            raise MCPError(
                f"id mismatch: expected {request_id}, got {response.get('id')}",
                rpc=response,
            )
        if "error" in response:
            err = response["error"]
            raise MCPError(
                f"server error {err.get('code')}: {err.get('message')}",
                rpc=response,
            )
        return response["result"]

    # ── Public protocol surface ───────────────────────────────────────────

    def initialize(self) -> dict[str, Any]:
        return self._request("initialize", {})

    def list_tools(self) -> list[dict[str, Any]]:
        return self._request("tools/list", {})["tools"]

    def _call_tool(self, name: str, arguments: dict[str, Any]) -> dict[str, Any]:
        result = self._request(
            "tools/call", {"name": name, "arguments": arguments}
        )
        try:
            text = result["content"][0]["text"]
        except (KeyError, IndexError, TypeError) as e:
            raise MCPError(
                f"tool {name} did not return a text content item: {result}"
            ) from e
        try:
            return json.loads(text)
        except json.JSONDecodeError as e:
            raise MCPError(
                f"tool {name} text was not JSON: {e}\ntext: {text!r}"
            ) from e

    def check(self, source: str) -> dict[str, Any]:
        return self._call_tool("sigil_check", {"source": source})

    def forge(
        self,
        source: str,
        *,
        input: str = "",
        fuel: int = 100_000,
        grants: dict[str, list[str]] | None = None,
    ) -> dict[str, Any]:
        args: dict[str, Any] = {"source": source, "input": input, "fuel": fuel}
        if grants is not None:
            args["grants"] = grants
        return self._call_tool("sigil_forge", args)

    def lookup_error(self, code: str) -> dict[str, Any]:
        return self._call_tool("sigil_lookup_error", {"code": code})

    def inspect_uses(self, source: str) -> dict[str, Any]:
        """Phase 5a-4: parse-aware introspection of `use` decls per
        module. Returns the `sigil_inspect_uses` envelope with
        `data.modules: { <module>: [<imported>] }`. Used by the
        stdlib-usage verifier (I10) to confirm an LLM-generated source
        actually imports the stdlib modules its task requires —
        comments and string literals containing `use sigil::...;` do
        NOT appear in the response (per AP18 anti-pattern)."""
        return self._call_tool("sigil_inspect_uses", {"source": source})
