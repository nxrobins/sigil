# Sigil MCP Server (`sigil-mcp`)

`sigil-mcp` exposes the Sigil compiler and runtime as Model Context Protocol
tools. An LLM agent harness (Claude Code, Claude Desktop, or any other MCP
client) can call these tools to drive a compile-feedback loop directly —
generate `.sigil` source, compile it, read structured diagnostics, regenerate
until clean, then execute under user-approved I/O grants.

## Architecture

The server runs an **agent-driven loop**. It exposes four primitive tools:

- `sigil_check(source)` — compile-only, returns a structured JSON envelope
  with diagnostics on failure.
- `sigil_forge(source, input?, fuel?, grants?)` — compile + execute in an
  ephemeral Wasmtime sandbox. Returns the same envelope shape plus output
  and fuel-consumed data on success.
- `sigil_lookup_error(code)` — return the registry entry (title, fix recipe,
  category, doc URL) for a stable diagnostic code like `T060` or `R001`.
- `sigil_inspect_uses(source)` — parse-aware introspection of `use`
  declarations per module. Used by callers (notably the bench harness)
  to verify that a generated source actually imports a required stdlib
  module — comments and string-literal `use sigil::...;` mentions do
  NOT appear in the output.

The server has **no LLM access of its own**. The calling agent is the loop:
it generates source, calls `sigil_check`, reads the diagnostics, regenerates,
and finally calls `sigil_forge` with the user-approved grants. This keeps
the server stateless, credential-free, and shippable as a single binary.

## Envelope schema v2

Every response from a compile-time tool (`sigil_check`, `sigil_forge`,
`sigil_inspect_uses`) carries `schema_version: 2`. v2 adds two
load-bearing fields over v1:

- **`data.timing`**: `{ check_ms: u64, modules_seen: u32, sigs_built: u32, partial: bool }` —
  wall-clock latency of the compile pass plus structural counters.
  Present on **success AND error envelopes**. `partial: true` indicates
  the compile didn't reach completion (e.g. parse failure stopped sig
  collection). Engineers and dashboards correlate compiler regressions
  on this without parsing free-text fields. Consumers that ignore
  unknown fields are unaffected by the addition.
- **Diagnostic structure**: `message` and `hint` are SEPARATE fields
  (never concatenated). Agents read `data.diagnostics[i].hint` directly
  for the fix recipe; humans read `message` for the failure description.
  The hint is required (never empty) for any code where a recipe makes
  sense — if you see an empty hint, that's a registry bug.

`tools/list` and `initialize` envelopes are EXEMPT from the timing field
(no compile happens) — documented as the only exception.

**v1 → v2 migration**: v2 only adds fields. Existing consumers that
ignored unknown JSON fields continue to work; those that asserted
`schema_version == 1` need to be widened. Old transcripts on disk
(`schema_version: 1`) are rejected by `--resume` flows that require
the integrity layer (Phase 5a-4 / I24); start a fresh run instead.

## Build

```bash
cargo build --release -p sigil-mcp
# Binary lands at target/release/sigil-mcp(.exe)
```

The MCP server only needs the `json` feature on `sigil-compiler` (default).
It does **not** need Z3 (the `solver` feature) — the structural checks the
compiler runs without Z3 are sufficient for agent-driven iteration.

## Wire into Claude Code

Add to `~/.claude.json` (or `.claude/mcp_servers.json`):

```json
{
  "mcpServers": {
    "sigil": {
      "command": "/abs/path/to/target/release/sigil-mcp",
      "args": []
    }
  }
}
```

Then `/mcp` in a Claude Code session lists the available tools.

## Wire into Claude Desktop

Add to `claude_desktop_config.json` (location varies by OS — see Anthropic's
MCP setup docs):

```json
{
  "mcpServers": {
    "sigil": {
      "command": "/abs/path/to/target/release/sigil-mcp"
    }
  }
}
```

Restart Claude Desktop. The Sigil tools appear in the tools panel.

## Tool reference

### `sigil_check`

Compile a Sigil source string and return a structured diagnostic envelope.

**Input:**
```json
{ "source": "module sigil; fn boot() -> i64 { return 42; }" }
```

**Success envelope:**
```json
{
  "schema_version": 2,
  "status": "ok",
  "command": "check",
  "data": {
    "source_name": "<mcp>",
    "primary_module": "sigil",
    "wasm_inner_bytes": 294,
    "wasm_outer_bytes": null,
    "air_function_count": 1,
    "fuel_budget": 128,
    "timing": {
      "check_ms": 1,
      "modules_seen": 1,
      "sigs_built": 1,
      "partial": false
    }
  }
}
```

**Error envelope:**
```json
{
  "schema_version": 2,
  "status": "error",
  "command": "check",
  "diagnostics": [
    {
      "severity": "error",
      "code": "T060",
      "title": "Undefined local",
      "message": "undefined local `ready`",
      "hint": "This name is not in scope. Declare it with `let`, ...",
      "doc_url": "sigil://errors/T060",
      "location": { "file": "<mcp>", "span": { ... }, "line": 1, "column": 42 }
    }
  ],
  "data": {
    "timing": {
      "check_ms": 0,
      "modules_seen": 1,
      "sigs_built": 0,
      "partial": true
    }
  }
}
```

### `sigil_forge`

Compile a Sigil tool module and execute it once in an ephemeral sandbox.
The source must export `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64`.

**Input:**
```json
{
  "source": "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }",
  "input": "hello",
  "fuel": 100000,
  "grants": {
    "fs": ["/tmp/work"],
    "net": ["api.github.com", "*.example.com"]
  }
}
```

`fuel` defaults to 100000. `grants` defaults to `{}` (fully sandboxed, every
FFI call returns 403). Filesystem grants are canonicalized; network host
patterns support a leading `*.` wildcard for subdomain matching.

**Success envelope:**
```json
{
  "schema_version": 2,
  "status": "ok",
  "command": "forge",
  "data": {
    "wasm_bytes": 294,
    "function_count": 1,
    "fuel_budget": 100000,
    "fuel_consumed": 4,
    "output_bytes": 5,
    "output_text": "hello",
    "timing": {
      "check_ms": 1,
      "forge_ms": 4,
      "modules_seen": 1,
      "sigs_built": 1,
      "partial": false
    }
  }
}
```

**Compile error**: same shape as `sigil_check` error.

**Runtime error** (fuel exhaustion, trap, missing entry point, invalid output)
returns a single `R8xx`-coded diagnostic:
```json
{
  "schema_version": 2,
  "status": "error",
  "command": "forge",
  "diagnostics": [
    {
      "severity": "error",
      "code": "R801",
      "title": "Fuel exhausted",
      "message": "tool exhausted fuel budget after 100000 units",
      "doc_url": "sigil://errors/R801",
      "location": null
    }
  ],
  "data": {
    "timing": {
      "check_ms": 1,
      "forge_ms": 12,
      "modules_seen": 1,
      "sigs_built": 1,
      "partial": true
    }
  }
}
```

### `sigil_lookup_error`

Look up a stable diagnostic code in the central registry.

**Input:**
```json
{ "code": "R001" }
```

**Output:**
```json
{
  "schema_version": 2,
  "status": "ok",
  "command": "lookup_error",
  "data": {
    "code": "R001",
    "title": "Outer-ring code cannot own capabilities",
    "default_hint": "Capabilities live in the inner ring. Pass a borrowed capability via `grant(&cap, ...)` ...",
    "category": "Ring",
    "doc_url": "sigil://errors/R001"
  }
}
```

Use this when a `sigil_check` / `sigil_forge` diagnostic returns a code you
want more context on.

### `sigil_inspect_uses`

Parse-aware introspection of `use` declarations per module. Returns a
`module_name → [imported module names]` map for every module in the
input source. Comments and string-literal `use sigil::...;` mentions
do NOT appear — only real `use` decls the parser saw.

The bench harness calls this from its parse-aware verifier (Phase 5a-4
/ I10 / AP18) to confirm an LLM-generated source actually imports the
stdlib modules its task requires. A regex-based check would happily
accept commented-out or string-literal mentions; this tool doesn't.

**Input:**
```json
{ "source": "module tool;\nuse sigil::fs;\nuse sigil::json;\npub fn tool_main(...) -> i64 { return 0; }" }
```

**Success envelope:**
```json
{
  "schema_version": 2,
  "status": "ok",
  "command": "inspect_uses",
  "data": {
    "modules": {
      "tool": ["fs", "json"]
    },
    "timing": {
      "check_ms": 0,
      "modules_seen": 1,
      "sigs_built": 0,
      "partial": false
    }
  }
}
```

**Parser failure**: same envelope shape with `status: "error"`,
diagnostics array populated, and `data.timing.partial: true`. Callers
that need to distinguish "module didn't import X" from "source didn't
parse at all" should check `status` first.

## Suggested agent loop

```
1. agent generates initial .sigil source from task description
2. agent calls sigil_check(source)
   if status == "error":
     for each diagnostic in diagnostics:
       agent reads code + title + hint
     agent generates corrected source, goto 2
3. agent presents source + intended grants to user for approval
4. agent calls sigil_forge(approved_source, input, grants)
5. agent reports the output to the user
```

Termination: cap the loop at N attempts (5 is reasonable). On exhaustion,
report the final diagnostics to the user.

## Protocol

Newline-delimited JSON-RPC 2.0 over stdin/stdout, per the MCP stdio transport.
Methods implemented: `initialize`, `tools/list`, `tools/call`, `shutdown`.
`notifications/initialized` and other notifications are accepted silently.

See `crates/sigil-mcp/tests/protocol.rs` for a worked client-side example
(spawn binary, send requests, parse responses).

## See also

- [`docs/ERROR-CODES.md`](ERROR-CODES.md) — the canonical catalog of every
  diagnostic code an agent will encounter.
- [`lang-ref.md`](../lang-ref.md) — the Sigil language reference, useful as
  a system-prompt addition for agents generating tools.
- [`ATTACK-MATRIX.md`](../ATTACK-MATRIX.md) — what the verifier protects
  against; helpful context for understanding why diagnostics matter.
