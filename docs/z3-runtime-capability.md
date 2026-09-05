# Cap<Z3> — the runtime Z3 solver capability

**Status:** shipped (spike). The uniquely-SIGIL self-hosting dependency: a
compiled SIGIL WASM program can drive the Z3 SMT solver across the WASM
boundary, gated by a capability that fails closed.

## Why this exists

SIGIL is a *verifying* compiler — it discharges refinement and capability
obligations with Z3. For SIGIL to ever be written in SIGIL (self-hosting),
the SIGIL-written compiler must be able to call Z3 at its own runtime. Every
other self-hosting primitive (Vec, maps, arenas, file I/O) is "standard
systems-language completeness"; the Z3 oracle is the one dependency no other
language's playbook de-risks for us. This capability is that boundary, built
by mirroring the proven `fs`/`http`/`crypto` host-shim pattern.

This is a **spike**: a minimal, sound, shippable boundary. It is NOT the final
ergonomic surface (see "Out of scope").

## The boundary

| Layer | Artifact |
|---|---|
| SIGIL source | `stdlib/sigil/z3.sigil` — `effect Z3Solve;` + `extern "C" fn z3_check` + `pub fn check` wrapper, `#[ring(outer)] #[trusted]` |
| Compile-time authority | the `Z3Solve` effect (user-declared, tracked like `FsIO`); a caller omitting it is rejected with **E001** |
| Runtime authority | `Z3Grant::Solve` in `IoGrants.z3`; empty ⇒ fail closed |
| Host shim | `z3_check(query_ptr, query_len) -> i64` in `crates/sigil-runtime/src/ephemeral.rs` (`link_ffi_imports`), `#[cfg(feature = "solver")]` |

A SIGIL program places an SMT-LIB2 query string in guest memory and calls
`z3::check(ptr, len)`. The host shim reads it, runs it through a fresh,
rlimit-bounded Z3 solver, and returns the verdict as a packed `i64`.

### Return contract

| `i64` | Meaning |
|---:|---|
| `1` | **sat** — the asserted constraints are satisfiable |
| `0` | **unsat** — the asserted constraints are unsatisfiable |
| `-400` | malformed — non-UTF8, interior NUL byte, or **zero parsed assertions** |
| `-403` | grant denied (fail-closed; no solver constructed) |
| `-408` | unknown — rlimit exhausted / undecidable fragment |
| `-413` | query too large (> 1 MiB) |

**Soundness invariant (NC1):** a non-`{sat,unsat}` outcome is NEVER reported
as `0` or `1`. "Don't know" is never "proven". This is the property that makes
the boundary safe to build a verifier on. It is enforced two ways: the
`SatResult::Unknown` arm maps to `-408`, and a **parse-error gate** rejects any
query that `Solver::from_string` parsed into zero assertions (Z3 installs a
null error handler and silently swallows SMT-LIB2 parse errors, so an
unguarded `check()` on an empty solver would return a spurious `Sat`).

Through the public `execute_ephemeral` entry point, a negative return surfaces
as `Err(ToolError::Trapped { "tool returned error (N)" })`; `1` yields `Ok`
with a 1-byte output, `0` yields `Ok` with empty output.

## Security properties (the Adversarial-Compiler ritual)

| Constraint | Property | Enforced by |
|---|---|---|
| **NC1** | non-verdict outcomes never read as sat/unsat | `z3_shim_tests` (empty/garbage/rlimit) + `z3_shim_source_contract::cm1` |
| **NC2** | fail-closed; denied calls do zero work | grant check is the shim's first statement; `z3_capability_shim::fail_closed_without_grant` + `cm2` |
| **NC3** | panic-free & memory-safe for ALL guest input | NUL/UTF8/len/OOB guards; `z3_capability_shim` (nul/utf8/oversize/oob) + `cm3` |
| **NC4** | deterministic: rlimit only, fresh Context per call | pinned `Z3_RUNTIME_RLIMIT`, no wall-clock timeout; determinism tests + `cm4` |
| **NC5** | Z3 stays out of the default runtime TCB | optional dep behind `solver`; default build links no Z3 |

## Determinism

The verdict is bounded by `Z3_RUNTIME_RLIMIT` (solver fuel — conflicts/
decisions), **not** a wall-clock timeout, so the same query yields the same
verdict regardless of machine speed or call order (a fresh `Context` is built
per call; no shared solver state). Z3-using tools may therefore use
`expected_output_strategy: capture_from_reference`, unlike `time`/`random`.

Caveat (AG5): like the compiler's compile-time Z3 use, reproducibility is
guaranteed for a **pinned Z3 build** (`z3 = 0.12.1`); bit-identical resource
accounting across *different* Z3 builds is not attempted.

## Out of scope (Explicit Anti-Goals)

- **AG1** — no cumulative solver budget across many `z3_check` calls (per-call
  rlimit + guest fuel suffice).
- **AG2** — no SMT-LIB2 command-surface sandboxing. The eventual fix is a
  **typed assertion API** in SIGIL serialized to SMT-LIB2 at the boundary; this
  spike accepts raw SMT-LIB2 and only guarantees the must-prevent case
  (zero-assertion → false "sat") is closed by NC1.
- **AG3** — no cert-level effect⇆grant reconciliation for Z3 (runtime grant +
  compile-time effect only).
- **AG4** — targets the existing dev/CI build config (where the compiler
  already links Z3); no cross-target / static-vs-dynamic libz3 matrix.

## Build & test

```
# Default build: NO z3 in the TCB (NC5).
cargo build -p sigil-runtime

# Solver build: the shim + behavioral proofs.
cargo test -p sigil-runtime --features solver --test z3_capability_shim
cargo test -p sigil-runtime --features solver --lib z3_shim_tests

# Always-on source contract (CM1–CM4) + stdlib validity + effect-gating.
cargo test -p sigil-runtime --test z3_shim_source_contract
cargo test -p sigil-compiler --test stdlib_compiles z3
```
