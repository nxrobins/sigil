# Owned Strings — Construction on the `str` Provenance Model

**Status:** Implemented — v1 complete (owned-strings "PR S2", #211–#214); UTF-8 validity now ENFORCED (UTF-8 Boundary Enforcement epic, #216); `from_bytes` validates untrusted bytes (PR S3, #218)
**Date:** 2026-06-06
**Authors:** Nigel Robinson

---

## 1. Design Summary

The borrowing-string surface (`substr`/`find`/`split_on`/`trim`/`parse_i64`, #157–#161)
is all zero-copy **views** — there is no way to *build* a string. Owned construction —
`concat` / `join` / `itoa`, the strings a diagnostic renderer or pretty-printer needs —
is this epic.

The load-bearing decision: **an owned string is the SAME `str` type.** A `str` is a
uniform 8-byte fat-pointer `[data_ptr: u32 @0, len: u32 @4]`. It may point at static
bytes (a literal), borrowed bytes (a `substr` view), or — new — freshly `alloc`'d heap
bytes (owned). The type system does **not** distinguish: provenance is a runtime fact,
not a type. So an owned `str` interoperates with every existing `str` method
(`byte_at`/`len`/`substr`/`find`/`split_on`/…) for free, and composes with itself.

```sigil
let a: str = "ab";
let r: str = a.concat("cd");      // owned "abcd" — a fresh heap str
let v: str = r.substr(1, 3);      // borrowing view "bc" into the owned bytes
let n: i64 = 42;
let s: str = n.itoa();            // owned "42"
```

Construction is **pure-SIGIL stdlib** over one private compiler primitive: a builder
`alloc`s a buffer, fills it byte-by-byte from its inputs (read via the bounds-checked
`byte_at`), and wraps the buffer as a `str` via `str_from_raw`. Everything else
(`string.sigil`) is ordinary SIGIL.

### Core Principles

1. **Provenance, not a new type.** Owned ≡ borrowed ≡ literal at the type level. The
   only difference is where the bytes live; safety in v1 does not depend on the
   difference (the global bump arena never frees mid-invocation — except inside a
   `region {}`, which is exactly why owned strings are region-tracked; §6 ET-2).
2. **One unsafe primitive, contained.** `str_from_raw(ptr, len)` forges a fat-pointer
   from raw memory — the single place memory-safety could be violated. It is
   stdlib-private, gated at compile time (T257) and grep-quarantined (§4).
3. **Allocate once, return fresh.** Each builder allocates exactly once from a
   provably-non-negative total and returns a fresh value — never an input — so it is
   trivially clean under default-frozen and the constant-time/taint axes (§6).
4. **Preserve bytes; don't interpret them.** Builders copy bytes — they neither create
   nor repair UTF-8 validity, and don't need to: every public producer preserves it and
   `substr` now *traps* on a mid-codepoint slice, so "every `str` is valid UTF-8" holds
   by induction (§5 AC-2). `str` stays byte-indexed.

---

## 2. The Model

`str` runtime layout (`air.rs`): an 8-byte fat-pointer header
`[data_ptr: u32 @ STR_DATA_PTR_OFFSET=0, len: u32 @ STR_LEN_OFFSET=4]`, identical to
`Type::Slice`. A string literal lowers to a BumpAlloc'd header whose `data_ptr` is a
static-data offset; a `substr` view to a header pointing into the receiver's bytes; an
owned string to a header pointing at a fresh `alloc`'d buffer.

Builders read inputs only through the public, bounds-checked `byte_at` / `len`
intrinsics — never by extracting a raw `data_ptr` — and write through `alloc` + `store8`
(the `crypto.sigil` `hex_encode` precedent: alloc → store8 loop → wrap).

---

## 3. The Surface

The owned-construction surface lives in **`stdlib/sigil/string.sigil`** (`module string;`,
effect `! { Alloc }`), a module SEPARATE from the borrowing `strings.sigil` (note the singular):

| Method | Signature | Semantics |
|---|---|---|
| `a.concat(b)` | `str_concat(a: str, b: str) -> str` | a fresh `str` of `a`'s bytes then `b`'s |
| `sep.join(pieces)` | `str_join(sep: str, pieces: Vec<str>) -> str` | the pieces joined with `sep` between |
| `n.itoa()` | `str_itoa(n: i64) -> str` | a fresh decimal `str` for `n` |
| `ptr.from_bytes(len)` | `str_from_bytes(ptr: i64, len: i64) -> Option<str>` | validate `[ptr, ptr+len)` as UTF-8 → an OWNED copy, else `None` (PR S3, #218) |
| `ptr.valid_up_to(len)` | `str_valid_up_to(ptr: i64, len: i64) -> i64` | leading-valid-byte count (`== len` iff valid, else the first-invalid offset) |

### Dispatch

`concat` and `join` are `str`-receiver methods; `itoa` is an **i64-receiver** method.
The str-method reroute is a small `(method → module)` table: `find`/`contains`/…/`parse_i64`
route to `strings`, `concat`/`join` to `string`. Each desugars to
`<module>::str_<method>(receiver, args…)`. `n.itoa()` reroutes the i64 receiver to
`string::str_itoa(n)`; the PR-S3 validators `ptr.from_bytes(len)` / `ptr.valid_up_to(len)`
reroute the same way (i64 receiver, one trailing arg) to `string::str_from_bytes` /
`str_valid_up_to`.

> **Why `n.itoa()`, not free `itoa(n)`** (recon-grounded refinement of the original
> plan): free-function cross-module resolution only searches `use`'d modules, and
> ambient injection adds module *source*, never a `use` decl — so a free `itoa(n)`
> would fail to resolve, or an unconditional reroute would hijack a user `fn itoa`. The
> i64-receiver form is collision-safe (i64 has no user impls) and reuses the proven
> `.hash()`/`.eq()` primitive-method path. Every owned-surface method is thus a method,
> uniform with the rest of the str surface (`from_bytes`/`valid_up_to` take the i64 *pointer*
> as the receiver and the length as the sole arg).

### Ambient injection

`string.sigil` is injected by its OWN trigger — a `.concat(` / `.join(` / `.itoa(`
token — SEPARATE from the `strings.sigil` trigger. A borrow-only program (`.find` etc.)
injects `strings.sigil` but **not** `string.sigil`. Because `str_join` consumes a
`Vec<str>`, injecting `string.sigil` pulls `vec.sigil` transitively (as `strings.sigil`
does for `split_on`). A user `module string;` suppresses injection (the standard
dup-module guard).

---

## 4. The Keystone: `str_from_raw(ptr, len) -> str` (PRIVATE)

The one compiler primitive. It wraps a raw `(data_ptr, len)` pair into a fresh `str`
header — BumpAlloc 8 bytes, store `data_ptr` (u32) and `len` (u32) — mirroring the
string-literal lowering, the only difference being that `data_ptr` is a runtime value
instead of a static offset. It is effect-free (the caller's `! { Alloc }` covers the
buffer) and its result taint is `lub` of its args.

`str_from_raw` is **unsafe**: a lying `len` forges a `str` that the `byte_at`/`substr`
bounds-checks then *trust* (they check against the header's `len`), so a forged header
reads out of bounds. Unlike `vec_load`/`vec_store` (which self-trap on any caller),
`str_from_raw` cannot self-check — so it is contained **twice**:

- **Compile-time module gate (T257):** any call from a module other than `string` is
  rejected, abort-before-AIR. Normal user code (in `module tool;` etc.) cannot reach it.
- **Repo-wide grep quarantine** (`tests/str_from_raw_quarantine.rs`): the token may
  appear only in `stdlib/sigil/string.sigil`.

`T256` was left reserved for the regions epic; this gate took `T257`, the next free code.

---

## 5. Constraints & Fallbacks (as shipped)

The epic's adversarial Constraint Matrix produced five existential threats (ET-1…ET-5)
and two academic edge-cases (AC-1, AC-2). Each, as it actually landed:

### ET-1 — `str_from_raw` is an unsafe fat-pointer forge
**Limit:** callable from the one-module allowlist (`string`); each builder derives
`alloc`'s size, the `str_from_raw` `len`, and the bytes written from **one** length
value (`alloc'd ≡ len ≡ written`). **Fail-fast:** T257 (compile-time, abort-before-AIR)
+ the grep quarantine + the PR-1 runtime round-trip (build `"ab"` by hand → read back via
`byte_at`/`len`).

### ET-2 — owned strings × regions (the measured-and-closed hole)
The bump arena DOES free at region exit (DEF-2a reclamation), so a `str` built inside a
`region {}` and escaped would dangle. The measurement confirmed the hole empirically: a
region `Vec` escape was T254, but a region str escaped *silently* — because `Type::Str`
was absent from `is_aliasable_type` (safe pre-owned-strings, since no `str` could be
region-allocated). **Fix:** `region_of_value` now scores a freshly-allocated `str` as
region-born (`Lexical(depth)`), with a precise exception for string **literals** (static
bytes → `Global`). **Fail-fast:** the existing **T254** region-escape gate now rejects an
escaping owned str — parity with `Vec`, and it covers the builder *call* (e.g.
`a.concat(b)` in a region), not just `str_from_raw`. Scoped to region tracking (the broad
`is_aliasable_type` is untouched), so every non-region str program is byte-identical.

### ET-3 — taint preservation (retracted: already satisfied)
The teardown feared owned construction would *launder* a secret to public. Grounding in
`taint_check.rs` showed the opposite: a call's result taint is `lub(callee_ret, ⊔ args)`,
so `s.concat("x")` / `n.itoa()` on a `@SecretCT` input return `@SecretCT` automatically —
the secrecy rides the call boundary, not the str header's internals. **Fail-fast:** a
downgrade to `@Public` is **T001**; pinned by tests (secret-in → secret-out clean;
secret-in → public-out rejected). The pointers are length-derived (public), so there is
no T025 timing leak. (`join`'s secrecy rides the `Vec<str>` handle taint — the pre-existing
Vec rule.)

### ET-4 — builder length arithmetic
**Limit:** each builder allocates **exactly once** from a provably-non-negative total.
`join`: `Σ len(pieces) + (n-1)*sep.len()`, the `(n-1)` GUARDED by `n > 0` so the empty
vector can't underflow — `n=0 → ""`, `n=1 →` a fresh copy of the piece. `itoa`: all digit
math runs in NEGATIVE space (the working magnitude is kept ≤ 0), so **`i64::MIN`** — whose
magnitude is not a positive i64 — is handled with no negation and no overflow.
**Fail-fast:** the `n ∈ {0,1,2,N}` / empty-sep and `0`/±/`i64::MIN`/`i64::MAX` test
matrices assert exact bytes; a wrong total would trap at the bump allocator.

### ET-5 — byte-identity
**Limit:** owned construction lives in 1 NEW file (`string.sigil`), behind a DEDICATED
trigger; a non-owned-string program injects 0 bytes of it. **Fail-fast:** the snapshot
suite runs by diff rather than accepting changed snapshots automatically.

### AC-1 (anti-goal) — strings longer than 2³²
`concat`/`join` totals are i64, truncated to the u32 `len`. A string that large cannot
exist in WASM32's ≤4 GB linear memory — `alloc` OOM-traps long before truncation — so v1
does not engineer overflow-checked length arithmetic.

### AC-2 — UTF-8 validity as an enforced invariant (deferred at S2; RESOLVED by #216)
At S2 ship this was an anti-goal: byte-indexed with no codepoint consumer, and `substr`
could slice through a multi-byte codepoint, so "output is valid UTF-8" was *preserved, not
enforced*. The follow-on **UTF-8 Boundary Enforcement** epic (#216) closed it. `substr` was
the ONLY public producer that could introduce an invalid `str`; every other already
preserves validity, so trapping `substr` on a non-boundary slice makes the invariant true
**by induction**:

| Producer | Why the result is valid UTF-8 |
|---|---|
| string literal | lexer-validated (`String::from_utf8(..).expect(..)`; no byte-injection escape) |
| `concat` / `join` / `itoa` | byte-copy from already-valid inputs / ASCII digits |
| `split_on` / `trim` | slice only at delimiter / ASCII-whitespace positions — codepoint boundaries by self-synchronization |
| `str_from_raw` | T257-private + grep-quarantined; callers copy already-valid bytes |
| **`substr`** | **now traps** if `start`/`end` is a continuation byte (`(b & 0xC0) == 0x80`) strictly inside the string |

So "every `str` is valid UTF-8" is now *enforced*, not hoped-for. `concat`/`join`/`itoa`
still merely **preserve** (a multi-byte `"é"` = `0xC3 0xA9` survives both unchanged) — they
never need to repair, because their inputs are already valid. The read-only rail
`s.is_char_boundary(i) -> bool` is the floor's RAIL: `s.substr(a, b)` traps iff
`!is_char_boundary(a) || !is_char_boundary(b)`, letting a tool check before slicing. The one
path that needs a real *validator* — `from_bytes` for untrusted external bytes — has since
SHIPPED (PR S3, #218): it validates the bytes (full RFC 3629 / Table 3-7) and returns an
OWNED `Option<str>` (a copy, never an aliasing view), extending the invariant to the outside
world. See §3.

---

## 6. Composition with the capability gates

- **default-frozen / T253.** Builders take bare (frozen) `str` params, only READ them,
  and return a FRESH `str_from_raw` result — never an input — so no `@Mut` is needed and
  the escape gate is silent. *Empirical note:* even returning an input `str` param is
  clean, and soundly so — `str` is not in `is_aliasable_type` because v1 `str` has **no
  mutators**, so there is no mutable handle to widen; T253's hazard is moot for `str`
  specifically (it still fires for a mutable record/`Vec`).
- **regions / T254.** §5 ET-2: an owned str built in a region is region-born; escaping it
  is rejected; in-region use is clean.
- **taint / T001, T025.** §5 ET-3: secrecy is preserved through builders; downgrade is
  T001; no timing leak.
- **borrowing surface.** Owned strings flow through `substr`/`find`/`split_on` and chain
  into further builders (`a.concat(b).concat(c)`, `itoa(x)` into a `Vec<str>` then `join`)
  — proven by runtime round-trips.

---

## 7. Anti-Goals (v1 does NOT build / guarantee)

- **A `Utf8Error` *reason* enum / `Result<str, Utf8Error>`** — `from_bytes` SHIPPED (PR S3,
  #218) as `ptr.from_bytes(len) -> Option<str>` (validate untrusted bytes → an owned copy)
  plus `ptr.valid_up_to(len) -> i64` (the first-invalid offset, à la Rust's `valid_up_to()`).
  SIGIL has no custom error types, so a richer reason enum (overlong / surrogate / range) is
  deferred until agents need more than the offset.
- **A mutable `String` / `push_str` incremental builder** — the provenance model has no
  owned record; `concat` reallocates (fine for rendering). Revisit only for a hot
  incremental-build path.
- **Region-allocated strings (`Str::in_region`)** — global-heap only; the lifetime story
  waits on per-region arenas (`memory-model.md`). In the meantime, a region-built owned
  str is region-tracked and may not escape (T254).
- **`.chars()` / codepoint iteration / grapheme clusters** — byte-indexed only.
- **Byte-wise `str` equality (`==` / `match` on a view or constructed string)** — **SHIPPED
  (PR #699), closing AG-S1-M**: `str ==` / `!=` and `match` on a `str` literal now compare
  BYTES — length first, then a fuel-metered byte scan (`AirStmt::StrBytesEq`) — retiring the
  old `data_ptr` comparison, which was not even identity (it ignored `len`, so a `substr`
  view compared EQUAL to its parent). Two byte-equal strings produced at different sites now
  compare equal, unblocking `Map<str, V>` with view/constructed keys. `str.bytes_eq` remains
  and is behaviorally identical; the certified source still uses it throughout (a shadow
  fence in `pipeline_differential.rs` pins the certified source to zero `str ==`, so the
  emitted bytes never moved). Two consequences of the semantics: `==` is O(len) and burns
  fuel per compared byte, and `==`/`!=` on a `@SecretCT` operand is REJECTED (T033/CT018) —
  the early-exit scan is a timing channel. *(The old semantics were the load-bearing
  constraint behind the SIGIL lexer's `bytes_eq` keyword recognition — see
  `docs/specs/lexer-in-sigil.md` §5, now historical.)*
- **Exposing raw `data_ptr` extraction to user code** — builders read via `byte_at`;
  `str_from_raw` stays quarantined.
- **>2³²-byte strings** (AC-1) — see §5 AC-1. (Enforced UTF-8 validity, the former AC-2,
  is now GUARANTEED by the boundary epic #216 — `substr` traps on a non-boundary slice; §5 AC-2.)

---

## 8. The Arc Beyond

The LOCKED "operations may assume valid encoding" invariant now **holds** (the boundary
epic #216 — `substr` traps + the inductive producer set, §5 AC-2), and `from_bytes` (PR S3,
#218) has **extended** it to *untrusted external* bytes — they are validated (full RFC 3629 /
Table 3-7) and copied into an owned `str` at the door. **The string-validity story is now
complete end to end**: literals + builders + `substr` (enforced by induction) and untrusted
bytes (validated on construction). Beyond that: a `Utf8Error` reason enum if the offset proves
insufficient; a mutable `String` builder if a hot path demands it; codepoint-indexed
`char_substr` only if byte-indexing proves a persistent agent footgun; and the
region-allocated-string lifetime story, which slots in when the per-region-arena seam lands —
the same seam the rest of the capability arc waits on.

---

## Cross-references

- `docs/specs/readonly.md` — default-frozen / T251 / T253 (the escape gate builders satisfy).
- `docs/specs/regions.md` — T254 region-escape (ET-2).
- `docs/specs/exclusivity.md` — T255 (orthogonal; builders take frozen params).
- `docs/specs/secret-ct.md` — the taint lattice + T001/T025 (ET-3).
