# Sigil ToolForge Reference

This is the practical reference for writing ephemeral Sigil tools with
`sigil forge`.

> **Compiler diagnostics**: every error the Sigil compiler emits carries a
> stable code (e.g. `T060`, `R001`, `O001`). See
> [`docs/ERROR-CODES.md`](docs/ERROR-CODES.md) for the full catalog of codes,
> titles, and fix recipes — useful both for humans debugging and for agent
> loops driving the compiler from a JSON feedback channel
> (`sigil check --json`).

## Entry Point

Every tool must export:

```sigil
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64
```

`tool_main` may also use `i32` parameters, but pure byte-processing tools
should prefer `i64` so pointer math works with the language's arithmetic
operators.

The return value is a packed `i64`:

```sigil
result_ptr * 4294967296 + result_len
```

Return a negative error code on failure.

## Pure Tool Intrinsics

Pure tools now have three built-in byte intrinsics:

```sigil
alloc(size)   // returns an output pointer as i64
load8(ptr)    // returns one byte as i64 in the range 0..255
store8(ptr, val) // writes the low 8 bits of val
```

Accepted argument types are machine integers: `i32`, `u32`, `i64`, or `u64`.
Pointers are wrapped to Wasm `i32` addresses internally.

`alloc(...)` requires the `Alloc` effect.

## Minimal Byte-Copy Tool

```sigil
module tool;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let out_ptr = alloc(input_len);
    let mut i = 0;

    while i < input_len {
        let b = load8(input_ptr + i);
        store8(out_ptr + i, b);
        i = i + 1;
    }

    return out_ptr * 4294967296 + input_len;
}
```

## FFI Tools

Trusted FFI tools keep the existing outer-ring ABI shape:

```sigil
#[ring(outer)] #[trusted] module tool;

extern "C" fn http_get(url: i32, url_len: i32) -> i64 ! { FFI, Unsafe };

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc, FFI, Unsafe } {
    return http_get(input_ptr, input_len);
}
```

Use the built-in byte intrinsics for pure computation and host FFI for
filesystem or network access.

## Modules and `use`

A Sigil compilation unit is a sequence of modules. Each module is
introduced by `module <name>;` and contains items (functions, externs,
effect declarations, `use` decls). Modules in the same compilation unit
can reference each other's `pub` items via cross-module dispatch.

### Importing a module

Module-level imports use the `use` keyword with a fully-qualified path:

```sigil
use sigil::fs;
use sigil::json;
```

Functions are then called as `<module>::<fn>(args)`:

```sigil
let raw: i64 @Internal = fs::read(input_ptr, input_len);
let value: i64 = json::parse_field(raw_ptr, raw_len, key_ptr, key_len);
```

**Module-only imports** are the only form supported in v1 — function-
level imports (`use sigil::fs::read;`) and wildcards (`use sigil::fs::*;`)
are reserved for future versions. The compiler emits N007 if the module
isn't found, with a top-3 Levenshtein-ranked hint listing the closest
available module names.

### Visibility

Items inside a module are private by default. Add `pub` to expose:

```sigil
module my_helpers;

pub fn render_decimal(n: i64) -> i64 ! { Alloc } { /* ... */ }
fn count_digits(n: i64) -> i64 { /* private */ }
```

Cross-module calls into a private item emit T155 ("private function
called from another module").

### Module dependency graph

The set of `use` decls across all modules in a compilation unit must
form a DAG. Cycles emit N009 with the full cycle path (summarized to
first 5 + last 2 modules if longer than 7).

Module names must match `^[a-z_][a-z0-9_]*$` (N011), and no two modules
in the same unit may collide on a case-insensitive comparison (N012).

### Effect rows across module boundaries

A function's declared effect row must be a superset of every effect
required by the functions it calls. The compiler enforces this on
**outer-ring** functions:

```sigil
#[ring(outer)] #[trusted] module tool;
use sigil::fs;

pub fn tool_main(...) -> i64 ! { FsIO, Alloc, FFI, Unsafe } {
    return fs::read(...);  // requires the same row — checked
}
```

If `tool_main`'s effect row omits any effect that `fs::read` requires,
the compiler emits T070 (effect-row mismatch).

**Inner-ring exemption.** Inner-ring functions today do NOT have their
effect rows enforced against callees. This is a known semantic — a
pure-Sigil tool that calls `json::parse_field` (which declares
`! { Alloc }`) doesn't have to list `Alloc` on `tool_main`. The
exemption is intentional for now; it's tracked as a follow-up because
silent "documentation-only" effect rows undercut the soundness story
the outer ring relies on. Inner-ring tools that want to be self-
documenting should still annotate the row explicitly.

### Cross-ring constraint (R004)

Outer-ring stdlib modules (any module declared `#[ring(outer)] #[trusted]`,
which includes `fs`, `crypto`, `time`, `random`, `http`, `kv`) can only be
called from a tool whose own module is also `#[ring(outer)] #[trusted]`.

```sigil
#[ring(outer)] #[trusted] module tool;   // ← required to call fs, http, etc.
use sigil::fs;
```

Without the ring annotation, cross-ring dispatch into an outer-ring fn
emits R004. The hint always includes the literal `#[ring(outer)] #[trusted]`
text so the fix is unambiguous.

Inner-ring modules (`json`, `hex_*`, anything with no `#[ring(outer)]`)
can be called from either ring without escalation.

### Catalog of stdlib modules

See [`stdlib/STDLIB.md`](stdlib/STDLIB.md) for per-module signatures,
effect rows, grant requirements, and per-fn determinism notes. The
short version:

| Module | Ring | Determinism | Notes |
|---|---|---|---|
| `fs` | outer | per-FS state | `read`, `write` |
| `crypto` | outer (sha) / inner (hex) | yes (I3) | `sha256`, `sha512`, `hex_encode`, `hex_decode` |
| `time` | outer | **no** | wall-clock `now_ms` only; may decrease |
| `random` | outer | **no** | secure entropy via `getrandom` |
| `http` | outer | per-server | `get`, `post` |
| `kv` | outer | per-KV state | durable `get`, `put`, `delete`; namespace grants |
| `json` | inner | yes (I3) | v2 codec: `parse_field`, `parse_index`, `array_len`, `validate`, `escape_string` |

## Constant-Time Discipline (`@SecretCT`)

For cryptographic code where wall-clock timing must not depend on secret
data, Sigil ships a fourth taint label `@SecretCT` above the usual
three-level lattice. Full specification in
[`docs/specs/secret-ct.md`](docs/specs/secret-ct.md); library demo in
[`tools/ct_demo.sigil`](tools/ct_demo.sigil).

### Lattice

```
@Public  <  @Internal  <  @Secret  <  @SecretCT
```

Higher labels are *more confidential* for flow purposes (`can_flow_to`)
and *operationally stricter* — a value at `@SecretCT` cannot participate
in any construct whose execution time, memory access pattern, or
instruction trace would depend on it.

### What `@SecretCT` rejects at compile time

The compiler emits the listed `Txxx` diagnostic codes (spec name
`CTnnn` ↔ code `Txxx`):

| Construct | Spec / Code |
|-----------|-------------|
| `if`/`while`/`for`/`match` on `@SecretCT`         | CT001–CT004 / T020–T023 |
| Array index by `@SecretCT`                        | CT005 / T024 |
| `load8`/`store8` at `@SecretCT` address           | CT006 / T025 |
| `/` (division) with `@SecretCT` operand           | CT007 / T026 |
| `extern "C"` call with `@SecretCT` argument       | CT010 / T027 |
| `actor.send`/`actor.ask` with `@SecretCT` payload | CT014 / T028 |
| `alloc(n)`/`region(n)` with `@SecretCT` size      | CT015 / T029 |
| `@Internal`/`@Secret` → `@SecretCT` upcast        | CT016 / T030 |
| `declassify(value, cap)` with `@SecretCT` input   | CT017 / T031 |

`@Public → @SecretCT` upcast IS permitted — public constants and masks
carry no confidentiality and are required for CT computation.

### Source-of-CT principle

A `@SecretCT` value can only come from a declared `@SecretCT` parameter,
a literal annotated `@SecretCT`, a CT intrinsic return, or an arithmetic
expression whose source taints lub to `@SecretCT`. Untrusted sources
(FFI returns, declassified data) cannot be "promoted" to `@SecretCT`
without going through a declared `@SecretCT` boundary.

### Declassification chain

The two-step ladder `@SecretCT → @Secret → @Public` uses two distinct
linear capabilities:

```sigil
module crypto;
cap type DeclassifyCT {}
cap type Declassify {}

fn reveal(s: i64 @SecretCT, ct_cap: DeclassifyCT, pub_cap: Declassify) -> i64 @Public {
    let mid: i64 @Secret = declassify_ct(s, ct_cap);
    return declassify(mid, pub_cap);
}
```

`declassify` rejects `@SecretCT` inputs directly (T031 / CT017), so a
single declassification cannot collapse the chain.

### CT intrinsics

Three branch-free constant-time primitives are exposed as built-ins,
identical in calling syntax to `alloc`/`load8`/`store8`:

```sigil
ct_eq(a: i64, b: i64) -> bool         // (a ^ b) == 0
ct_select(c: bool, t: i64, f: i64) -> i64  // f ^ ((t ^ f) & -c)
ct_lt(a: i64, b: i64) -> bool         // ((a - b) >> 63) & 1
```

Each lowers to a fixed sequence of bitwise Wasm instructions (`I64Xor`,
`I64Sub`, `I64And`, `I64Or`, `I64Eqz`, `I64ShrS` by constant 63). The
compiler never emits Wasm `select`, `br_if`, `if`, or `div` opcodes
inside CT-discipline scope; a regression-guard test
([`crates/sigil-compiler/tests/taint_ct_audit.rs`](crates/sigil-compiler/tests/taint_ct_audit.rs))
byte-scans the emitted bytecode and panics if any forbidden opcode
appears.

### Minimal CT example

```sigil
module crypto;

fn ct_compare(a: i64 @SecretCT, b: i64 @SecretCT) -> bool @SecretCT {
    return ct_eq(a, b);
}

fn ct_min(a: i64 @SecretCT, b: i64 @SecretCT) -> i64 @SecretCT {
    let a_is_less = ct_lt(a, b);
    return ct_select(a_is_less, a, b);
}
```

Both functions contain no conditional branches, indexing, division, or
allocation; every operation runs in time independent of `a` and `b`.

### What `@SecretCT` does NOT defend against

Per the explicit anti-goals in `docs/specs/secret-ct.md` §9:

- **Microarchitectural channels** (Spectre v1/v2/v4, cache eviction,
  SMT port contention, DVFS, EM/power, rowhammer) — below the language;
  require CPU/OS/hardware mitigation.
- **Trap-timing observability** — Wasm traps (fuel exhaustion, OOB)
  unwind to the embedder; callers MUST size fuel from public inputs only.
- **Transitive timing through non-CT helpers** — CT scope is the
  immediate function signature; non-CT helpers called from CT code are
  not analyzed.
- **Operational state leakage** — actor mailboxes, fuel ledgers, and
  audit logs may carry residual side effects of past CT computation;
  CT scope is the current invocation's lexical environment only.
