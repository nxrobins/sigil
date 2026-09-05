# Cap<KV> — the durable key-value storage capability

**Status:** shipped. The first storage primitive designed for STATE
rather than files: a value put in one ephemeral run is readable in
later runs. This is the piece that lets long-lived *services* be built
out of one-shot *tools* — state lives in storage between invocations
while every process stays ephemeral (the FaaS shape; see
`memory-model.md` for why in-process long-lived state is a separate,
unscheduled epic, and `serve-runtime.md` for the host layer that
completes the shape: HTTP trigger + durable scheduler).

Built by mirroring the proven `fs`/`http`/`crypto` host-shim pattern,
the same recipe `z3-runtime-capability.md` documents.

## The boundary

| Layer | Artifact |
|---|---|
| SIGIL source | `stdlib/sigil/kv.sigil` — `effect KvIO;` + `extern "C" fn kv_get / kv_put / kv_delete` + `pub fn get / put / delete` wrappers, `#[ring(outer)] #[trusted]` |
| Compile-time authority | the `KvIO` effect (user-declared, tracked like `FsIO`); a caller omitting it is rejected with **E001** (tested in `stdlib_compiles.rs::tool_using_kv_without_effect_is_rejected`) |
| Runtime authority | `KvGrant` (read) / `KvWriteGrant` (write) entries in `IoGrants.kv` / `IoGrants.kv_write`; empty ⇒ fail closed (-403 before any I/O) |
| Host shims | `kv_get` / `kv_put` / `kv_delete` in `crates/sigil-runtime/src/ephemeral.rs` (`link_ffi_imports`) |

## Namespaces are grants, keys are opaque

A call names a **namespace** — an opaque label matched against grants
by exact string compare. The grant (not the guest) maps the namespace
to a host directory:

```
KvGrant      { namespace: "app", root: /srv/kv/app }   → kv_get allowed
KvWriteGrant { namespace: "app", root: /srv/kv/app }   → kv_put / kv_delete allowed
```

Read and write are SEPARATE grant categories (mirroring
`fs`/`fs_write`): a read grant does not confer write, and a write
grant does not confer read.

**Keys never touch paths.** A key is arbitrary bytes (≤ 1 KB); the
host stores the value at `<root>/<sha256hex(key)>.kv`. There is no
path-traversal surface: namespace strings are compared, never joined;
key bytes are hashed, never interpreted.

## Semantics

- `get(ns, key)` → packed value bytes; `-404` when absent. Empty
  values are legal and distinct from absent.
- `put(ns, key, value)` → `0`. Create-or-replace, last-put-wins.
  Atomic publish (sibling temp file + rename): a concurrent reader
  sees the old value or the new one, never a torn write. Durability
  matches `fs::write` — OS write-back, no fsync.
- `delete(ns, key)` → `0`; `-404` when the key was absent.

Error codes across all three: `-403` no grant for the namespace,
`-413` key > 1 KB / value > 5 MB / namespace > 256 bytes, `-400`
malformed arguments (bad pointers), `-500` host failure — including
a missing grant root: creating the root directory is the granter's
job, not the tool's.

**Determinism:** per I3-style classification, `kv::*` is deterministic
*relative to KV state* (same class as `fs`). Bench tasks should pin
fixture directories, or use `TimeGrant::Frozen`-style pinned setups.

## Caps (I7 / I26)

- Key ≤ 1 KB, value ≤ 5 MB (matching `fs`/`http` body caps),
  namespace label ≤ 256 bytes.
- Grant categories `kv` and `kv_write` are capped at 256 entries each
  (R808 / `MAX_GRANTS_PER_CATEGORY`), enforced by
  `IoGrants::validate()`.

## Wiring

- **CLI:** `sigil forge tool.sigil --kv NS=DIR --kv-write NS=DIR`
  (repeatable). Roots are canonicalized at grant construction.
- **MCP:** `sigil_forge` grant args gain `"kv": ["NS=DIR", ...]` and
  `"kv_write": ["NS=DIR", ...]`. Malformed descriptors are DROPPED
  (fail closed), not widened.
- **Cert gate:** `KvIO` is not yet in `CLI_GATED_EFFECTS`
  (`FsIO`/`NetIO` only), so `forge --cert` neither requires nor
  forbids kv grants. Tightening that is a follow-up.

## Out of scope (v1)

- `list` / `scan` (needs pagination + size-bounding design; hashing
  keys also means listing requires a key-manifest decision).
- Compare-and-swap / transactions — single-writer, last-put-wins only.
- TTL / expiry.
- Cross-namespace atomicity.

These are natural evolve-harness or follow-up targets once a consumer
needs them; adding any of them is a NEW extern (per I22/AP20, existing
shim signatures are frozen).

## Tests

`crates/sigil-runtime/tests/kv_shims.rs` — fail-closed boundary,
read/write separation, namespace isolation, binary keys/values, size
caps, grant-cap validation, stdlib-wrapper composition, and the
capability headline: `kv_durability_across_ephemeral_runs` (put in one
`execute_ephemeral`, get in a fresh one).
