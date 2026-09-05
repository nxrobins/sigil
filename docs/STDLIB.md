# Sigil Standard Library — overview

The Sigil stdlib is a small set of capability-gated modules shipped
under `stdlib/sigil/`. Each module is plain `.sigil` source, composed
into a tool's compilation unit at build/forge time via
`use sigil::<name>;`. There is no AIR cache, no shared object — the
stdlib is just code that travels with the tool.

For per-function signatures, effect rows, grant requirements, and
determinism notes, see the canonical catalog at
[`stdlib/STDLIB.md`](../stdlib/STDLIB.md). This page is the high-
level orientation: what the stdlib is for, how it's structured, what
guarantees it makes, and how it's expected to evolve.

## What's in the stdlib today

Six modules in the first wave:

| Module | What it wraps | Ring | Determinism |
|---|---|---|---|
| `fs` | host `fs_read` / `fs_write` shims | outer + trusted | per-FS state |
| `crypto` | `sha256`, `sha512` shims + pure-Sigil hex helpers | outer (sha) / inner (hex) | yes (I3) |
| `time` | host `time_now` shim | outer + trusted | **no** (wall clock) |
| `random` | host `random_bytes` shim | outer + trusted | **no** (secure entropy) |
| `http` | host `http_get` / `http_post` shims | outer + trusted | per-server |
| `kv` | host `kv_get` / `kv_put` / `kv_delete` shims | outer + trusted | per-KV state |
| `json` | pure-Sigil codec (parse / extract / validate / escape) | inner | yes (I3) |

`kv` is the first storage primitive designed for STATE rather than
files: values put in one ephemeral run are readable in later runs,
which is what lets long-lived services be built out of one-shot tools
(state lives in storage between invocations; every process stays
ephemeral). Namespaces are opaque grant labels — the host maps them to
backing directories; keys are arbitrary bytes hashed host-side, so key
material never reaches path resolution. Read (`kv`) and write
(`kv_write`) grants are separate, both fail-closed. See
[`kv-runtime-capability.md`](kv-runtime-capability.md).

`json` is the flagship inner-ring stdlib module. v2 is a strict
RFC 8259 codec: full escape decoding (including `\uXXXX` surrogate
pairs → UTF-8), escape-aware key matching, nested objects/arrays
extracted as raw balanced slices (recurse by feeding them back in),
array indexing (`parse_index`) and counting (`array_len`),
whole-document `validate`, and an `escape_string` encode primitive.
Work stays bounded: 10,000-entry walk cap, 63-level nesting cap, and
an iterative (non-recursive) value skipper.

## Determinism guarantee (Invariant I3)

Every pure-compute stdlib function is deterministic: the same input
bytes always produce the same output bytes (or the same error code).
This is a hard guarantee, not best-effort:

- Bench tasks using deterministic stdlib can use
  `expected_output_strategy: capture_from_reference` — the captured
  golden bytes will match every subsequent run.
- The `random` and `time` modules are explicitly NON-deterministic and
  the bench validator (Phase 5a-4 / I27) refuses any task spec that
  combines `capture_from_reference` with a `time` or `random` grant —
  such tasks must use `expected_output_strategy: literal`.

`fs::read` / `fs::write` are deterministic relative to filesystem
state; `http::get` / `http::post` are non-deterministic at the network
level even though the wire protocol is. Bench fixtures that need
reproducible runs against these should pin against a static fixture
(local file, mocked endpoint).

## Capability gating

Every outer-ring stdlib function maps to a host-side grant category.
A tool that calls `fs::read` only succeeds at runtime if the host
passes a matching `IoGrants.fs` entry. Without the grant, the FFI
shim returns `-403` and the tool propagates that as an error.

Read and write grants are SEPARATE: granting read access to a path
does not enable write. `time` and `random` grants are coarse — either
the tool gets the capability or it doesn't.

The grant list per category is capped at 256 entries (Phase 5a-2 / I26
/ R501) to bound the worst case.

## Ring escalation

Calling any FFI-backed stdlib module (`fs`, `crypto::sha*`, `time`,
`random`, `http`, `kv`) requires the tool's own module to be declared
`#[ring(outer)] #[trusted]`. The compiler emits R004 with a hint
containing the literal escalation text if you forget. Inner-ring
stdlib (`json`, `crypto::hex_*`) callable from either ring without
escalation.

See [`lang-ref.md`](../lang-ref.md) for the full Modules and `use`
section, including the inner-ring effect-check exemption (a known
semantic — inner-ring tools' effect rows are NOT enforced against
callees today).

## How the stdlib is composed into a tool

The bench harness (`bench/src/sigil_bench/compose.py`) is the
reference implementation:

1. Validates each requested module name against `^[a-z_][a-z0-9_]*$`
   BEFORE any file I/O (Invariant I25 — path-traversal can't reach
   `Path` operations).
2. Reads each `stdlib/sigil/<module>.sigil` once per process
   (LRU-cached by path).
3. Normalizes line endings to LF, strips trailing whitespace per line.
4. Sorts and deduplicates the requested module list (compose is
   byte-deterministic across module-order variations).
5. Concatenates the LLM source onto the front of the bundled stdlib.
6. Computes a 24-hex-char SHA-256 truncation of the bundled stdlib
   bytes (`stdlib_hash`, Invariant I23) — used as the prompt-cache
   key suffix in the LLM generator so any stdlib edit invalidates
   the cache cleanly.

Other harnesses (a CI workflow, an editor plugin) should follow the
same shape. The hash truncation length and the validator regex are
both exposed as constants; don't redefine them.

## What's coming next

Phase 5b builds the evolution harness. Its originally-planned first
track — expanding `json::parse_field` to escapes, nested values, and
arrays — landed hand-written as json v2 (see the catalog); the
harness's adversarial corpus now targets what v2 still defers
(number decoding, builders, streaming input). Other natural targets:

- `time::monotonic_ms` — currently no monotonic clock; only wall.
- `random` insecure / seeded variant for reproducible tests.
- `crypto` — SHA-3, HMAC, AES.
- `fs` — append, streaming.
- `http` — PUT / DELETE / PATCH, header customization.

The point of evolution is to expand the stdlib WITHOUT breaking the
determinism / capability guarantees above. Any candidate that mutates
an `extern "C"` signature is dead-end-rejected at trial setup
(Invariant I22 / AP20).

## See also

- [`stdlib/STDLIB.md`](../stdlib/STDLIB.md) — canonical per-module catalog
- [`lang-ref.md`](../lang-ref.md) — Modules and `use`, ring escalation
- [`docs/MCP-SERVER.md`](MCP-SERVER.md) — `sigil_inspect_uses` for
  parse-aware verification of stdlib usage
- [`docs/ERROR-CODES.md`](ERROR-CODES.md) — every diagnostic code the
  stdlib calls can produce (R004, T155, N007/8/9, O0xx grant codes)
