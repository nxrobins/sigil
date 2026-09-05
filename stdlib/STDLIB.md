# Sigil Standard Library

The first wave of the curated stdlib. Six modules wrap the FFI shims
shipped in Phase 5a-2 (#21) and
provide pure-Sigil helpers for hex encoding and a JSON codec.

Modules are imported via `use sigil::<name>;` and called as
`<name>::<fn>(...)` (cross-module dispatch lands in
Phase 5a-1, #18).

## Ring requirements

| Module | Ring | Reason |
|---|---|---|
| `fs` | outer + trusted | `extern "C" fn fs_read`, `fs_write` |
| `crypto` | outer + trusted | `extern "C" fn crypto_sha256`, `crypto_sha512` |
| `time` | outer + trusted | `extern "C" fn time_now` |
| `random` | outer + trusted | `extern "C" fn random_bytes` |
| `http` | outer + trusted | `extern "C" fn http_get`, `http_post` |
| `kv` | outer + trusted | `extern "C" fn kv_get`, `kv_put`, `kv_delete` |
| `json` | inner | pure-Sigil; no FFI |
| `abi`  | inner | pure-Sigil; no FFI (packed-i64 helpers) |

A user tool calling any FFI-backed module above MUST itself declare
`#[ring(outer)] #[trusted]` on its module — `compile_tool` selects ONE
wasm by `tool_main`'s ring, and cross-ring calls don't exist at the
wasm level. Calling `json::*` from inner-ring tools works fine.

## Per-module reference

### `fs`

| Function | Signature | Effects | Grant required |
|---|---|---|---|
| `fs::read` | `(path_ptr: i32, path_len: i32) -> i64 @Internal` | `FsIO, Alloc, FFI, Unsafe` | `IoGrants.fs` covering `path` |
| `fs::write` | `(path_ptr: i32, path_len: i32, body_ptr: i32, body_len: i32) -> i64 @Internal` | `FsIO, FFI, Unsafe` | `IoGrants.fs_write` covering `path` |

`read` returns packed `(ptr * 4294967296 + len)` of file bytes, or
negative error. `write` returns 0 on success, negative on error.
Cap: 5 MB body. Read and write grants are SEPARATE — granting read
on a path does not enable write.

### `crypto`

| Function | Signature | Effects | Grant required | Deterministic |
|---|---|---|---|---|
| `crypto::sha256` | `(input_ptr: i32, input_len: i32) -> i64 @Internal` | `Alloc, FFI, Unsafe` | none | yes (I3) |
| `crypto::sha512` | `(input_ptr: i32, input_len: i32) -> i64 @Internal` | `Alloc, FFI, Unsafe` | none | yes (I3) |
| `crypto::hex_encode` | `(input_ptr: i64, input_len: i64) -> i64` | `Alloc` | none | yes (I3) |
| `crypto::hex_decode` | `(input_ptr: i64, input_len: i64) -> i64` | `Alloc` | none | yes (I3) |

`sha256` returns packed pointer to 32 bytes; `sha512` to 64 bytes.
`hex_encode` produces lowercase hex; `hex_decode` accepts both cases
and returns -400 on malformed input or odd length.

### `time`

| Function | Signature | Effects | Grant required | Deterministic |
|---|---|---|---|---|
| `time::now_ms` | `() -> i64 @Internal` | `FFI, Unsafe` | `TimeGrant::Wall` | **no** (I18) |

**WALL CLOCK ONLY** — value can DECREASE under NTP correction or manual
clock change. Stdlib must not assume monotonicity. A separate
`monotonic_ms` is reserved for future expansion.

Returns Unix epoch milliseconds as a raw integer (NOT a packed
pointer). Tools that want to format the timestamp as a string for
output need a render helper (e.g. a decimal-rendering loop similar to
`crypto::hex_encode`).

Tasks using `time` MUST use `expected_output_strategy: literal`
(per I27) — `capture_from_reference` is invalid because the captured
value won't match on the next run.

### `random`

| Function | Signature | Effects | Grant required | Deterministic |
|---|---|---|---|---|
| `random::bytes` | `(out_len: i32) -> i64 @Internal` | `Alloc, FFI, Unsafe` | `RandomGrant::Secure` | **no** |

Cap: `out_len` up to 64 KB (per I26). Returns -400 on overflow.

Tasks using `random` MUST use `expected_output_strategy: literal`
(per I27).

### `http`

| Function | Signature | Effects | Grant required |
|---|---|---|---|
| `http::get` | `(url_ptr: i32 @Internal, url_len: i32 @Internal) -> i64 @Internal` | `NetIO, Alloc, FFI, Unsafe` | `NetGrant` matching the URL host with `Get` method |
| `http::post` | `(url_ptr: i32 @Internal, url_len: i32 @Internal, body_ptr: i32 @Internal, body_len: i32 @Internal) -> i64 @Internal` | `NetIO, Alloc, FFI, Unsafe` | `NetGrant` matching the URL host with `Post` method |

Response body cap: 5 MB. Returns packed pointer to body on success,
negative HTTP-style error code on failure (-403 grant rejected,
-404 host not allowed, -413 body too large, -502 transport error).

### `kv` (durable key-value storage)

| Function | Signature | Effects | Grant required |
|---|---|---|---|
| `kv::get` | `(ns_ptr: i32 @Internal, ns_len: i32 @Internal, key_ptr: i32 @Internal, key_len: i32 @Internal) -> i64 @Internal` | `KvIO, Alloc, FFI, Unsafe` | `IoGrants.kv` entry for the namespace |
| `kv::put` | `(ns_ptr: i32 @Internal, ns_len: i32 @Internal, key_ptr: i32 @Internal, key_len: i32 @Internal, val_ptr: i32 @Internal, val_len: i32 @Internal) -> i64 @Internal` | `KvIO, FFI, Unsafe` | `IoGrants.kv_write` entry for the namespace |
| `kv::delete` | `(ns_ptr: i32 @Internal, ns_len: i32 @Internal, key_ptr: i32 @Internal, key_len: i32 @Internal) -> i64 @Internal` | `KvIO, FFI, Unsafe` | `IoGrants.kv_write` entry for the namespace |

The first storage primitive designed for STATE, not files: values put
in one ephemeral run are readable in later runs. The namespace is an
opaque label matched against grants by exact string compare
(fail-closed); the grant maps it to a host directory. Keys are
arbitrary bytes (up to 1 KB) hashed host-side to backing-file names —
key material never participates in path resolution.

- `get` returns the packed value bytes; `-404` when absent.
- `put` creates or replaces, returns 0. Atomic: a concurrent reader
  sees the old value or the new one, never a torn write. Durability
  matches `fs::write` (OS write-back).
- `delete` returns 0, or `-404` when the key was absent.

Shared error codes: `-403` no grant for the namespace (read and write
grants are SEPARATE, like `fs`/`fs_write`), `-413` key > 1 KB, value
> 5 MB, or namespace > 256 B, `-400` malformed arguments, `-500` host failure (including a
missing grant root — creating it is the granter's job, not the
tool's).

Deterministic relative to KV state (like `fs` relative to filesystem
state). Bench tasks against kv should pin fixture directories.

See [`docs/kv-runtime-capability.md`](../docs/kv-runtime-capability.md)
for the full boundary description.

### `json` (v2: strict RFC 8259 codec)

| Function | Signature | Effects | Grant required | Deterministic |
|---|---|---|---|---|
| `json::parse_field` | `(input_ptr: i64 @Flow, input_len: i64 @Flow, key_ptr: i64 @Flow, key_len: i64 @Flow) -> i64 @Flow` | `Alloc` | none | yes (I3) |
| `json::parse_index` | `(input_ptr: i64 @Flow, input_len: i64 @Flow, index: i64 @Flow) -> i64 @Flow` | `Alloc` | none | yes (I3) |
| `json::array_len` | `(input_ptr: i64 @Flow, input_len: i64 @Flow) -> i64 @Flow` | none | none | yes (I3) |
| `json::validate` | `(input_ptr: i64 @Flow, input_len: i64 @Flow) -> i64 @Flow` | none | none | yes (I3) |
| `json::escape_string` | `(input_ptr: i64 @Flow, input_len: i64 @Flow) -> i64 @Flow` | `Alloc` | none | yes (I3) |

**Taint-polymorphic (`@Flow`):** the label of what comes out is the
label of what went in. Parse a `@Public` document and the field is
`@Public`; parse an `@Internal` HTTP response and the field is
`@Internal`; parse `@Secret` bytes and the field is `@Secret`. Calling
these on classified data needs NO declassification — which is the point,
since parsing untrusted input is what a JSON codec is for — and no label
is ever lowered. The compiler checks each body once per admissible label,
so a leak would be caught at the `@Internal` instantiation. `@SecretCT`
is excluded (these scanners branch on their input by construction); such
an argument is rejected with T030 rather than given a false CT guarantee.
See `docs/SECURITY_MODEL.md`.

**v2 scope (strict RFC 8259 grammar):**

- `parse_field` extracts the named field's value from the top-level
  object; `parse_index` extracts element `index` (0-based) from the
  top-level array. Extraction rules:
  - string values come back with escapes DECODED (`\"` `\\` `\/`
    `\b` `\f` `\n` `\r` `\t` and `\uXXXX` including surrogate pairs,
    encoded as UTF-8), quotes stripped;
  - numbers (full grammar: fraction + exponent) and `true` / `false`
    / `null` come back as their literal ASCII, verified byte-exactly;
  - nested objects/arrays come back as the RAW balanced JSON slice —
    recurse by feeding the slice back into `parse_field` /
    `parse_index`.
- Object keys are matched AFTER escape decoding: `{"a\nb": 1}` is
  found by the 3-byte key `a`, `0x0A`, `b`.
- `array_len` counts (and validates) the top-level array's elements.
- `validate` is the whole-document check: exactly one JSON value of
  any kind plus optional surrounding whitespace; returns 0 on valid.
- `escape_string` is the encode primitive: quotes + escapes arbitrary
  bytes into a JSON string literal (`"` `\` and control bytes escaped,
  control bytes as `\b \t \n \f \r` or `\u00XX`; all other bytes pass
  through UTF-8-transparent). Exact-size, two-pass.

**Extraction is streaming:** `parse_field` / `parse_index` validate
only the bytes they traverse and return as soon as the target is
extracted — bytes after the target (even a missing closing bracket)
are never inspected. Use `validate` when whole-document strictness
matters. (`array_len` similarly does not inspect bytes after the
closing `]`.)

**Bounds (per I7):** field/element walks cap at 10,000 entries
(-429); container nesting caps at 63 levels (-430). The value skipper
is iterative with an explicit step budget — no recursion, so
adversarial nesting cannot grow the wasm call stack.

Returns:
- success: packed pointer per the extraction rules above
  (`array_len` and `validate` return plain non-negative integers,
  NOT packed pointers)
- `-400` malformed JSON (bad escape, lone surrogate, raw control byte
  in a string, bad number grammar — leading zeros, `1.`, `.5`, `1e` —
  unbalanced containers, truncated input, trailing garbage in
  `validate`)
- `-404` field / index not found
- `-429` more than 10,000 fields / elements in one container walk
- `-430` nesting deeper than 63 levels
- `-415` is retired as of v2 (nested values are supported); the code
  is reserved and will not be reused

### `abi`

| Function | Signature | Effects | Grant required | Deterministic |
|---|---|---|---|---|
| `abi::unpack_ptr` | `(packed: i64) -> i64` | none | none | yes |
| `abi::unpack_len` | `(packed: i64) -> i64` | none | none | yes |
| `abi::pack` | `(ptr: i64, len: i64) -> i64` | none | none | yes |

Every FFI host function returns a packed `(ptr << 32 | len)` i64. The
helpers wrap the shifts and masks (`packed >> 32`, `packed & 0xFFFFFFFF`,
`ptr << 32 | len`) so call sites read as data flow named at the function
boundary. Inlining the operators at the call site is fine too — these
exist as ergonomics, not abstraction.

Pure compute — inner-ring, no FFI, no grants, deterministic. Outer-ring
tools can `use sigil::abi;` freely.

## Determinism summary (per I3)

Deterministic (safe with `expected_output_strategy: capture_from_reference`):
- `crypto::*` (sha256, sha512, hex_encode, hex_decode)
- `json::*` (parse_field, parse_index, array_len, validate, escape_string)
- `fs::read` / `fs::write` (deterministic relative to filesystem state;
  bench fixtures with stable file contents are reproducible)
- `kv::*` (deterministic relative to KV state, same caveat as `fs`)

Non-deterministic (require `expected_output_strategy: literal`):
- `time::now_ms`
- `random::bytes`
- `http::get` / `http::post` (depends on remote server)

## Tracing

Every FFI shim called from these modules emits typed `FfiShimEntry` /
`FfiShimExit` events behind `--features trace` per AP17 / I21. Pure-
Sigil helpers (`hex_encode`, `hex_decode`, `json::*`) do not
emit trace events directly today; future expansion may add per-module
trace events for parser-state transitions in `json`.

## Known v1 limits and follow-ups

- `json` v2 covers strict single-document parse/extract/validate and
  string encoding. Not yet: number → machine-integer decoding beyond
  `str.parse_i64`, object/array BUILDERS (compose via `escape_string`
  + byte concatenation), streaming multi-document input.
- `time::now_ms` is wall-clock only; no monotonic clock today.
- `random::bytes` is secure entropy only; no insecure / seeded variant.
- `crypto` provides SHA-2 family only; no SHA-3, no HMAC, no AES.
- `fs::read` / `fs::write` are byte-oriented; no streaming, no append.
- `http` is GET/POST only; no PUT/DELETE/PATCH, no header customization.
- `kv` is get/put/delete only; no list/scan, no compare-and-swap, no
  TTL. Single-writer semantics per key (last put wins).

These are tracked as the natural first batch of evolve-harness targets
once the loop ships in Phase 5b.
