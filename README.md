# SIGIL

A capability-oriented, agent-native language that compiles to WebAssembly, checks its declared capability and refinement obligations with Z3, and runs forge tools in fresh, discardable sandboxes.

**Shipped:** a Rust production toolchain plus self-hosted differential shadows written in SIGIL, a two-ring capability and effect system, a four-level information-flow lattice with an algorithmic constant-time mode, lexical regions, generics (including enums), Alloc-free bounded collections, iterator pipelines, and an ephemeral execution path gated by a load-bearing verification certificate. Extensive compiler and runtime test suites (run per-crate with `cargo test`); 67 attack programs defended, 15/15 tournament vectors covered, 10-CVE retrofit corpus.

## What this is

SIGIL compiles a capability-oriented source language to WebAssembly and runs it in a sandboxed Wasmtime host. Its production pipeline applies type, ring, effect, information-flow, capability, ownership, memory, and fuel checks over documented subsets; host grants and certificate gates add runtime enforcement at selected boundaries. The toolchain ships a full ephemeral path (`sigil forge`) that compiles a one-shot tool, verifies it, runs it against input inside a fresh store, and discards the execution state. Capability and refinement obligations are checked by a Z3 prover confined to a guarded quantifier-free fragment. Independent SIGIL implementations differentially check curated lexer, parser, type-checker, and security-pass surfaces against the Rust oracle.

The exact guarantee boundary is defined in [`docs/SECURITY_MODEL.md`](docs/SECURITY_MODEL.md), with claim-level evidence in [`docs/SOUNDNESS_MATRIX.md`](docs/SOUNDNESS_MATRIX.md) and residual risks in [`docs/RESIDUAL_RISKS.md`](docs/RESIDUAL_RISKS.md). [`docs/CLAIMS.md`](docs/CLAIMS.md) remains the machine-checked authority for what is proven.

## Capability matrix

Features shipped beyond the core actor/capability language, each with its evidence in-tree.

| Capability | Status | Where |
|---|---|---|
| Self-hosted compiler projection | Shipped, bounded | `selfhost/`; `docs/specs/self-hosting-completion-ladder.md`; differential lexer, parser, type-check, verification-pass, AIR, Wasm, and composed-pipeline suites against the Rust oracle |
| Generics — free fns, records, methods, **enums** | Shipped | `docs/specs/type-checker-in-sigil.md` §11/§12; generics differential cases (T150/T233/T234/T236) folded into the 107-test typecheck differential suite; eager monomorphization folded into the typed tree; 14-test guard against cap-smuggling through generic aggregates |
| Tuples — structural anonymous products | Shipped | `docs/specs/tuples.md` (Implemented v1); `Type::Tuple` with exhaustive `apply_subst`/`classify_value_kind` arms. `(A,B,…)` types, literals, multi-return, `let (x,y) = …` destructuring. (`.0`/`.1` index access deferred.) |
| Owned strings | Shipped | `docs/specs/strings.md` (Implemented v1); `stdlib/sigil/string.sigil` (`str_concat`/`str_join`/`str_itoa`/`str_from_bytes`/`str_valid_up_to`); UTF-8 boundary + `from_bytes` validation. One `str` type for literal/borrowed/owned; owned construction is pure SIGIL over the `str_from_raw` primitive |
| Bounded collections — stack-backed, Alloc-free | Shipped | `docs/specs/bounded-collections.md` (Implemented v1); `bounded_vec_i64`, `bounded_map_i64_i64`, `bounded_map_str_*`, `bounded_set_i64`, `bounded_set_str` in `stdlib/sigil/`. Sealed construction (T258), no `Alloc` effect, trap on overflow |
| BoundedVec transforms — Alloc-free functional API | Shipped | `stdlib/sigil/bounded_vec_i64.sigil`: `map`/`filter`/`filter_map`/`fold`/`sum`/`any`/`all`/`find`/`take` returning fresh sealed instances; no `Alloc` effect; size transposition is a compile error, not a silent trap |
| BoundedVec `zip`/`enumerate` + tuple pairs | Shipped | `stdlib/sigil/bounded_vec_i64.sigil` `zip`/`enumerate` build the sealed, Alloc-free `BoundedPairVec_i64_i64_N` family (`stdlib/sigil/bounded_pair_vec_i64.sigil`); `get -> Option<(i64,i64)>`; the unused pair family is DCE-proven not to bloat existing users |
| Iteration protocol + Vec pipelines | Shipped | `docs/specs/iteration.md` (Implemented v1); `stdlib/sigil/vec.sigil` — `VecIter`/`MapIter`/`FilterIter`/`TakeIter`, `for`-in desugars to a `while` loop at typecheck (zero `air.rs` change), eager `map`/`filter`/`sum`/`fold`/`any`/`all`/`find` on `Vec<i64>`, fluent `.iter().filter().map().take().collect()` |
| Array/slice methods | Shipped | `.contains(x)` on Array+Slice and `.first()`/`.last()` → `Option<T>`, the `==`-bearing scalar element types + `str` content equality; `AirStmt::ArrayOrSliceContains` scan loop |
| Collection pattern matching | Shipped | `Pattern::Array` in AST/typed-AST; `[]`, `[a]`, `[a,b,..rest]`, `[..rest]`, `[..]`; trailing `..rest` binds a slice; precise exhaustiveness; T264/T265 |
| String parsing & formatting | Shipped | width-conversion intrinsics (`.as_i32`/`.as_u32`/`.as_i64`/`.as_u64`), `str_parse_*`, unsigned itoa, `eq_ignore_case`, `split_first`; range-checked narrowing, ASCII case-folding |
| Narrow-int literal resolution | Shipped | `resolve_int_literals_or_reject` wired at let/assign/return/call-arg; emits T041/T045/T049/T071 on mismatch, gated to `{i32,u32,i64,u64}`; invalid wasm never emitted; self-host mirror in `typecheck.sigil` |
| F-strings — `f"…"` interpolation | Shipped | `f"…{e}…"` for `str`/`i64`/`bool` holes; both compilers type holes and emit T262 for unsupported values; lowering uses `.concat()` |
| Ergonomics — optional-else, if-let, while-let, type aliases | Shipped | Parse-time desugaring; type aliases resolve recursively at use sites, with cyclic aliases rejected at T263 |
| Corpus extraction | Shipped | `crates/sigil-corpus`: compiler-validated corpus infrastructure with four extractors (source-idiom, test-fixture, error-corpus, PR-history) plus the `inline_program` extractor, all behind a compiler-validation gate |
| Foreign frontends — untrusted DSL → SIGIL translators | Shipped (FE0–FE2) | `docs/specs/foreign-frontends.md`; `crates/sigil-frontends` (23 tests); `sigil translate/check --from <lang>`. FE0 `@cap`→cap-type (inner ring, T199), FE1 `@effects`→effect rows (outer ring, E001), FE2 typed subset behind a sound type+scope checker; cap-mode XOR effect-mode per file |

## Security model

This table is a compact index of production mechanisms. Its rows are bounded by the explicit
security model and soundness matrix linked above; they are not standalone whole-language theorems.

| Property guaranteed | Enforcement mechanism | Codes |
|---|---|---|
| Two-ring isolation — outer ring cannot own caps; inner ring cannot call externs directly | `ring_check.rs` rejects cross-ring access at typecheck (R001/R002/R003); R004 (direct cross-ring call) fires in the type-checker; `wasm.rs` emits separate `app_inner.wasm` / `app_outer.wasm` with isolated linear memories and a reduced outer import set (no `cap_restrict`/`cap_split`/`spawn`/`send`/`ask`) | R001–R004 |
| No capability forgery / no escalation | Type membrane (caps constructible only from init params) + linear ownership checker (use-after-move) + Z3 bitvector authority tracking (≤ 32 authorities per cap, `QF_BV<32>`); `Slot<Cap>` linear cell with authority-meet on multi-branch puts | O001, T183–T186, C003 |
| Parametric caps — value-bound authority | `cap type Approval(deadline_ms: i64)` / `Limited(deadline_ms, max_uses)`; arity checked (T201), all-positions covariant subtyping (T195), `restrict_deadline` narrows single-param caps (T200), `--build-deadline` refuses stale literals (T199) | T195/T199/T200/T201 |
| No undeclared effects | `effect_check.rs` validates that callee effect rows are a subset of the caller's declared row; `handle E1, E2 { … }` scopes the available set; closures inherit enclosing effects | E001–E003 |
| No unchecked downgrade on the declared information-flow surface | `taint_check.rs` four-level lattice `@Public < @Internal < @Secret < @SecretCT`; value and structured pc-taint propagation; control-flow joins and early-exit continuations; binding/return/state/actor sinks; capability-gated declassification; FFI results enter as `@Internal`. Termination observation and environmental channels are excluded by the security model | T001 |
| No algorithmic timing leak (constant-time) | `@SecretCT` is a strict refinement of `@Secret`: rejects secret-dependent branches/loops/match, indices, byte loads/stores, `div`/`%`, extern args, send/ask payloads, and size-of-alloc; closures and generics propagate CT taint; a wasm byte-scan audit (`tests/taint_ct_audit.rs`) locks codegen against regression. Algorithmic only — microarchitectural channels are an explicit anti-goal | T020–T032 |
| No region-value escape | `region NAME(LIMIT) { … }` lexical scope; birth-depth check in `type_check/statements.rs` rejects point-down escapes; reclamation is free (BUMP_PTR save/restore); post-hoc `(BUMP_PTR − save) > LIMIT` trap; region-polymorphism via `@in r` / `where region` | T254 |
| No OOB memory access | `wasm.rs` emits unsigned `I32LtU`/`I32GeU` bounds comparisons and `TrapIf` at index time | — |
| No unbounded execution | Fuel is a *capability* (spawn must move a `Fuel` cap in); every back-edge and recursion frame decrements it; `TrapIf` on exhaustion | — |
| No IoGrant bypass | Host validates the grant at FFI call time (last-line defense even if a cert is bypassed) | — |
| No cross-invocation state | Fresh Wasmtime store per `execute_ephemeral` | — |

## Verification & trust

**Z3 refinement & capability prover.** Capability authority, refinement clauses, and fuel/split balance are discharged by Z3. `air_capability_v2` is the sole AIR capability prover: pure collection is separated from discharge, and exactly four production `solver.check()` sites are permitted. Refinement obligations are collected without Z3 and discharged only by `type_check_v2/mod.rs` through `z3_capability.rs`. Per-query `rlimit = 1,000,000` and per-program cumulative `rlimit = 50,000,000` make solver budgets deterministic rather than wall-clock dependent.

**Quantifier-free fragment guard.** Decidability is not assumed — it is mechanically enforced. `z3_fragment_guard.rs` walks every solver assertion and rejects quantifiers, uninterpreted functions, non-`Bool`/`Int`/`BV` sorts, BV widths ≠ 32, and mixed-theory assertions, keeping all queries inside `QF_BV<32>` / `QF_LIA` / propositional. A `clippy.toml` disallowed-methods fence blocks the Z3 quantifier constructors and the cache-unsafe model/proof getters by name; the runtime fragment guard is the catch-all for anything outside the fragment. `C004` (Unknown) is a hard error with a reason string; there is no silent degradation. The `z3` crate is not linked into the default `sigil-runtime` build (TCB isolation).

**Load-bearing certificate.** Every successful compile emits schema-v9 evidence binding `source_fingerprint`, `wasm_inner_fingerprint`, `wasm_outer_fingerprint`, `module_names`, `compiler_version`, capability/ownership reports, the freshly linked Lean CSIR joint-verifier report, and `effects_required` (SHA-256, canonical multi-file framing). `sigil check --cert` emits it; `sigil verify-cert` checks source + WASM + policy match; `sigil run --cert` and `sigil forge --cert` refuse to execute on mismatch (deterministic `R810`–`R819`, no silent fallback). The certificate binds source to artifact; it is **unsigned** and does not assert provenance — an in-the-middle attacker can rewrite both source and cert consistently, so certificate binding ≠ certificate authenticity.

**Differential testing as bounded independent pressure.** The lexer, parser, and type-checker each have a second implementation *written in SIGIL* (`selfhost/*.sigil`) checked against the Rust oracle on declared corpora and projections: token streams, flat parse nodes, and selected resolved-type/diagnostic surfaces. Additional shadows cover selected ring, effect, taint, ownership, capability, AIR, monomorphization, and emit behavior. These tests prove agreement on their corpora, not whole-language equivalence or correctness of either implementation. Z3 results are also checked for corpus order independence, and a 10-CVE retrofit corpus is mechanically verified by `cve_corpus.rs`.

## Language tour

These blocks are compiled by `readme_compiles.rs` on every CI run, so everything
below is real SIGIL, not pseudocode. Note that SIGIL requires explicit
`return`, braces on every `match` arm, and writes negative values as `0 - n`.

```sigil
module tour;

// Types: records, enums, tuples, generics.
record Point { x: i64, y: i64 }
enum Shape<T> { Circle(T), Rect(T, T) }

// Type aliases.
type Id = i64;

// Tuple multi-return and destructuring.
fn divmod(a: i64, b: i64) -> (i64, i64) {
    let q = a / b;
    return (q, a - q * b);
}

fn remainder(a: i64, b: i64) -> i64 {
    let (q, r) = divmod(a, b);
    return r;
}

// Generics, monomorphized at the call site.
fn identity<T>(x: T) -> T {
    return x;
}

// Exhaustive match with inclusive range patterns and guards.
fn classify(b: i64) -> i64 {
    match b {
        0x30..=0x39 => { return 1; },      // inclusive range pattern
        c if c == 0x20 => { return 2; },   // guard
        _ => { return 0; },
    }
}

// Enum destructuring; variants are qualified.
fn area(s: Shape<i64>) -> i64 {
    match s {
        Shape::Circle(r) => { return 3 * r * r; },
        Shape::Rect(w, h) => { return w * h; },
    }
}

// Closures are `fn(..) -> T { .. }` values with an `Fn(..)` type.
fn apply_twice(f: Fn(i64) -> i64, x: i64) -> i64 {
    return f(f(x));
}

fn quadruple(x: i64) -> i64 {
    let double = fn(v: i64) -> i64 { return v * 2; };
    return apply_twice(double, x);
}

// while, compound assignment, and an `else`-less `if` (else is optional).
fn count_digits(limit: i64) -> i64 {
    let mut digits = 0;
    let mut i = 0;
    while i < limit {
        if classify(i) == 1 {
            digits += 1;
        }
        i += 1;
    }
    return digits;
}

// Capabilities: linear, value-parameterized.
// Limited(2031, 6) <: Limited(2030, 5)
cap type Limited(deadline_ms: i64, max_uses: i64) {}
```

Information flow lives in its own module below rather than in the block above.
The formal gate currently checks every closure call against the return contract
of every function in the module (a conservative dynamic-target summary, not a
type-directed one), so a module that mixes closure calls with functions returning
`@Secret` or `@SecretCT` values is refused today; the gap is tracked in
`docs/formal/public-occurrence-implementation.md`.

```sigil
module tour_flow;

// Information flow: four-level lattice, constant-time discipline.
fn ct_check(secret: i64 @SecretCT, guess: i64 @SecretCT) -> bool @SecretCT {
    return secret == guess;
}
```

## ToolForge — ephemeral execution

A SIGIL tool is a single outer-ring module exporting `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64`, returning a packed pointer/length pair into guest memory.

```bash
# Execute a tool directly against input data
sigil forge tools/task002_reverse.sigil --input "hello"

# With filesystem and network grants
sigil forge tools/task051_fetch_url.sigil \
    --fuel 1000000 \
    --fs /tmp/work \
    --net "api.github.com"

# Register a verified tool in the template store
sigil registry add tools/task036_csv_header.sigil \
    --task "Extract CSV header row" \
    --tags "csv,parse"

# Run from a registered template with string substitution
sigil forge --template 3 \
    --patch "TARGET_URL=https://api.github.com/zen" \
    --net "api.github.com"
```

### IoGrants

Capability-based runtime permissions; grants gate real I/O at call time (403 rather than trap). A per-category hard cap keeps the per-call scan bounded.

- `NetGrant { host_pattern, methods }` — `*.example.com` wildcards enforce dot-separated subdomain matching
- `FsGrant { root }` — canonicalized read-root prefix check; `..` and symlinks resolved before the check
- `FsWriteGrant` — write scope separate from read; `TimeGrant` — `Wall` or `Frozen(ms)`; `RandomGrant` — `Secure` or `Seeded(u64)`; `Z3Grant` — solver gate
- `IoGrants::none()` — fully sandboxed, every FFI call returns 403

### FFI host functions

- `ffi::http_get(url_ptr, url_len) -> i64` — real `ureq` HTTP GET, 5 MB body cap
- `ffi::http_post(url_ptr, url_len, body_ptr, body_len) -> i64` — real HTTP POST, 5 MB cap
- `ffi::fs_read(path_ptr, path_len) -> i64` — canonicalized read, 5 MB size cap
- All return packed `(ptr << 32 | len)` into guest memory via BUMP_PTR

### Tool corpus

`tools/` contains 200+ SIGIL files (numbered `task*.sigil` plus demo/probe files), compiled and executed end-to-end through the forge pipeline and swept by a CI drift detector. Coverage spans pure byte processing (reverse, base64, rot13), file I/O (read, grep, csv/json extract, diff), HTTP fetch (GET, hexdump, checksum), and composition (transpose csv, merge sorted, caesar/vigenère, levenshtein).

## Attack coverage & CVE retrofit

**67 attack programs across 9 phases. 15/15 tournament vectors defended.** Full inventory with tournament-vector mapping in [`ATTACK-MATRIX.md`](ATTACK-MATRIX.md).

| Phase | Attacks | Key defenses |
|---|---|---|
| Phase 1 | 14 | Ownership, type membrane, fuel, Wasm traps |
| Phase 2B — Ring | 8 | R001–R004, grant-scope enforcement |
| Phase 2C — Effects | 6 | E001–E003, closure effect propagation |
| Phase 2D — Taint | 5 | T001, implicit flow, declassify linearity |
| Phase 2E — FFI & Regions | 5 | F001, R003, E002, FFI `@Internal` taint |
| Phase 2F — Two-Module | 2 | Import segregation, memory isolation |
| Phase 2G — Cross-Cutting | 6 | Generic/effect-row cap smuggle, audit evasion |
| Phase 2H — Constant-Time | 13 | `@SecretCT` lattice, T020–T032 (CT001–CT017), byte-scan audit |
| Phase 3D — Forge Pipeline | 8 | IoGrant forgery, URL bypass, path traversal, fuel exhaustion |

**CVE retrofit corpus** — 10 famous bugs from JS, Solidity, Java, C, Linux, and Kubernetes (Log4Shell, The DAO reentrancy, Spring4Shell, Citrix path traversal, Shellshock, Drupalgeddon, WhatsApp double-free, Jenkins deserialization, Kubernetes API escalation, Struts2/Equifax), each classified honestly by scope (3 STRUCTURAL, 2 CLASS, 5 BY-CONSTRUCTION) and mechanically verified by `crates/sigil-compiler/tests/cve_corpus.rs`. Skim [`CVE-MATRIX.md`](CVE-MATRIX.md) or read the [per-CVE writeups](crates/sigil-compiler/tests/cve_corpus/).

## Build & test

```bash
# Install the `sigil` binary
cargo install --path crates/sigil-cli --force

# Compiler-only (no Z3 dependency)
cargo build -p sigil-compiler --no-default-features

# Full workspace (requires Z3 + LLVM/clang for bindgen)
cargo build --workspace

# Run each crate's suite (counts print in the `cargo test` summary)
cargo test -p sigil-compiler                         # compiler suite (default features: solver + json)
cargo test -p sigil-compiler --no-default-features   # compiler suite without the solver/json-gated tests
cargo test -p sigil-runtime                          # runtime suite
cargo test -p sigil-frontends                        # 23 foreign-frontend tests
cargo test -p sigil-corpus                           # corpus tests (integration + unit)
cargo test -p sigil-registry                         # registry tests
cargo test -p sigil --no-default-features            # CLI harness tests
cargo test -p sigil-mcp                              # MCP protocol tests

# Self-hosted differential gates (run inside sigil-runtime)
cargo test -p sigil-runtime lexer_differential       # 12 tests vs Rust oracle
cargo test -p sigil-runtime parser_differential      # 9 tests
cargo test -p sigil-runtime typecheck_differential   # 107 tests
```

### Z3 environment (Windows)

```bash
export Z3_SYS_Z3_HEADER="/path/to/z3/include/z3.h"
export LIBCLANG_PATH="C:/Program Files/LLVM/bin"
export BINDGEN_EXTRA_CLANG_ARGS="-I/path/to/z3/include"
export RUSTFLAGS="-L native=/path/to/z3/bin"
```

## Project status & maturity

The core language, two-ring capability/effect system, taint and constant-time lattice, regions, generics, collections, iterators, strings, and forge pipeline are shipped and regression-locked. The self-hosted projection covers the declared front-end, verification-pass, AIR, Wasm, and composed-pipeline surfaces; the certified source is byte-identical to the Rust oracle on the bounded corpus recorded in [`docs/specs/self-hosting-completion-ladder.md`](docs/specs/self-hosting-completion-ladder.md). The Rust compiler remains the oracle and trusted implementation. Refinement v2 is the sole production discharge path. Training-corpus session logging and synthetic mutation remain deferred.

**Where SIGIL is weak or costly** (from [`COMPARISON.md`](COMPARISON.md), which places SIGIL against Pony, Rust, Joe-E, Erlang, Caja, F\*, and Koka across 13 rows): SIGIL is **young and unproven in production** — no large deployments, a small ecosystem, and a single primary implementation of the back-end. It has no dependent types (F\* is far more expressive in its refinement logic), no first-class effect handlers (Koka), no hot-code reload (Erlang), and no mature library ecosystem (Rust). Verification has a real cost: with the solver on, refinement-heavy fixtures compile in milliseconds rather than microseconds, and SIGIL→Wasm output is **larger** than Rust→Wasm on paired programs (capability import stubs, fuel-decrement instructions, ring-isolation scaffolding, no tree-shaking) — see [`PERFORMANCE.md`](PERFORMANCE.md). The constant-time guarantee is **algorithmic only**; microarchitectural side channels (Spectre, cache, power/EM) are an explicit anti-goal requiring hardware/OS mitigation. Certificates bind but do not authenticate.

## Repo map

| Path | Contents |
|---|---|
| `crates/sigil-compiler` | Full compilation pipeline (lexer → parser → typecheck → ring/effect/taint/cap checks → AIR → Wasm) |
| `crates/sigil-runtime` | Wasmtime host engine — actors, messages, capabilities, fuel, supervision, ephemeral forge, IoGrants |
| `crates/sigil-abi` | Shared ABI boundary — runtime import names, actor/handler metadata |
| `crates/sigil-registry` | SQLite-backed template store for verified tool sources |
| `crates/sigil-cli` | The `sigil` binary — `check`, `run`, `forge`, `verify-cert`, `translate`, `registry`, `--cert` gates |
| `crates/sigil-mcp` | Model Context Protocol server exposing `sigil_check`/`sigil_forge`/`sigil_lookup_error` to agents — see [`docs/MCP-SERVER.md`](docs/MCP-SERVER.md) |
| `crates/sigil-corpus` | Compiler-validated SIGIL corpus extraction |
| `crates/sigil-frontends` | Untrusted external-DSL → SIGIL translators (`--from`) |
| `selfhost/` | The bounded compiler projection written in SIGIL, through composed AIR/Wasm emission |
| `stdlib/sigil/` | Strings, Vec + iterators, bounded collections, Result/Option, FFI shims |
| `tools/` | End-to-end forge tools |
| `docs/specs/` | Feature specifications |

Package-format work (the manifest and lockfile, `sigil check --package`, `sigil verify-cert`) is
specified in [`docs/specs/package-format-v1.md`](docs/specs/package-format-v1.md).

Contributing: start from the relevant spec under `docs/specs/`, the error-code catalogue in [`docs/ERROR-CODES.md`](docs/ERROR-CODES.md), and the attack/CVE matrices. Every behavioral change must land with a differential or corpus fixture; output-affecting compiler changes must preserve deterministic byte-equality gates.

## License

Dual-licensed under the MIT License ([`LICENSE-MIT`](LICENSE-MIT)) and the Apache License 2.0
([`LICENSE-APACHE`](LICENSE-APACHE)), at your option. Contributions are accepted under the same
terms with a Developer Certificate of Origin sign-off; see [`CONTRIBUTING.md`](CONTRIBUTING.md).
