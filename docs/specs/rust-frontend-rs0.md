# Rust Frontend — RS0 Spec

**Status:** SHIPPED. Hardened 2026-07-06 via the harden-spec ritual
(teardown handles `MC-*`/`MI-*`/`UP-*` → strict constraints `SC-*` below). The
third `sigil-frontends` translator, after TypeScript (FE0–FE2) and Solidity
(SOL0–ERC20). Crate: `crates/sigil-frontends`,
new module `src/rust/`. CLI: `sigil translate --from rust` and
`sigil check --from rust` (both already generic; only `frontend_for` needs a
new arm). This document records the shipped RS0 contract and its hardening basis.

## Thesis (the synergy)

Rust guarantees **memory safety** but has **zero authority discipline**: `std`
is ambient — any function may `std::fs::File::open`, `std::net::TcpStream::connect`,
`std::process::Command::spawn`, or read the environment, and `unsafe` governs
*memory*, not *authority*. A Rust → SIGIL frontend closes that gap: it translates
a Rust subset into SIGIL text that the trusted Rust `sigil-compiler` re-verifies,
so the emitted program is **memory-safe (Rust) ∧ capability-safe (SIGIL) by
construction**.

RS0 is the **base case** of that discipline and the pipeline-derisking rung
(mirroring FE0 for TypeScript and SOL0 for Solidity). Its guarantee is the atom
the whole capability story is built on:

> **S-AUTH — the RS0 synergy.** Every RS0-accepted Rust function is
> *authority-free by structural construction*: the emitter's output alphabet is a
> fixed finite set of arithmetic / comparison / control-flow / in-subset-call
> nodes over `i64`/`bool` — it contains **no** capability, intrinsic, `extern`,
> allocation, or host operation, so the emitted program has no way to *name*
> ambient authority. That structural closure is the guarantee's real basis, and
> it is the **frontend's** to enforce (see `SC-1`/`SC-2`), not the compiler's.

**What SIGIL does and does not contribute (grounded — UP-1 correction).** An
earlier draft claimed "SIGIL machine-checks this." That is **false** and is the
failure `UP-1` guards against: an RS0 module is **inner-ring** by default
([parser.rs](../../crates/sigil-compiler/src/parser.rs) — "default: secure by
construction"; `Ring::Inner` is `#[default]`), and
[`effect_check.rs`](../../crates/sigil-compiler/src/effect_check.rs) skips
inner-ring modules outright (`if module.ring == Ring::Inner { continue; }`). RS0
also threads no capabilities, so `capability::verify` has nothing to verify.
SIGIL therefore type- and structure-checks the emitted text (T-/N-/R-codes; an
inner-ring `extern` call is still R003) and is the trust anchor for RS1+ where
caps and effects *are* threaded and *are* checked — but it does **not** separately
certify authority-freedom for an RS0 fn. The proof is subset closure; the compiler
is a type/structure backstop only. RS0 must never overstate this.

RS0 does **not** yet thread capabilities (that is RS1, the FE0 analog: a
`#[sigil::cap(..)]`-derived cap parameter, moved into a terminal consumer,
enforced by `capability::verify` + T199) or effect rows (RS2, the FE1 analog).
RS0 establishes the trusted pipeline — hand-rolled lexer/parser, the sound
oracle-agreement checker, totality-owned bounds, the golden + differential
harness — that those rungs extend.

## Trust model (inherited, unchanged)

The frontend is an **untrusted** source-to-source translator; **SIGIL is the
trust anchor**. RS0 reuses the crate's existing contract verbatim
([`lib.rs`](../../crates/sigil-frontends/src/lib.rs)):

```rust
pub trait Frontend {
    fn name(&self) -> &'static str;                       // "rust"
    fn translate(&self, src: &str, source_name: &str)
        -> Result<EmittedSigil, Vec<FrontendDiag>>;
}
```

Translation either succeeds with **well-formed SIGIL** or fails with ≥1
`FrontendDiag` — it never panics, hangs, or emits partial output. The compiler
only ever sees the *emitted* text, so the translator itself must guarantee the
emitted meaning equals the authored meaning, and must **fail-closed** on anything
it does not fully recognize. The discipline is **reject (an FE6xx), never
best-effort** — the existential failure for a security translator is code that
*compiles* but *means something different*.

## RS0 subset (the closed allow-list)

Value-semantics only; every type explicitly annotated. Anything not in this table
is a fail-closed `FE6xx` reject.

| Category | RS0-accepted | Emitted SIGIL |
|---|---|---|
| **Items** | top-level `fn` / `pub fn` | `fn` / `pub fn` |
| **Types** | `i64`, `bool` — explicit on every param + return | `i64`, `bool` |
| **Literals** | exact in-range decimal `i64`; `true` / `false` | passthrough |
| **Arithmetic** | `+  -  *` on `i64` (wrapping — see S-SEM) | passthrough |
| **Comparison** | `== != < <= > >=` (i64 → bool; `==`/`!=` also bool↔bool) | passthrough (→ `bool`) |
| **Unary** | `!` on `bool` | passthrough |
| **Calls** | calls to other declared, in-subset `fn`s | passthrough |
| **Locals** | `let x: T = e;`, `let mut x: T = e;`, reassignment `x = e;` | `let` / `let mut` |
| **Control** | `if c { .. } else { .. }`, `while c { .. }`, blocks | passthrough (`else` always emitted) |
| **Return** | `return e;` **and** a Rust tail expression (trailing no-`;` expr) | `return e;` |

**Permanently / RS0-deferred out-of-subset → reject:** `struct`, `enum`, `impl`,
`trait`, `mod`, `use`, `const`/`static`, `extern`; references/borrows (`&`,
`&mut`); generics, lifetimes, `where`; closures; `match`; method calls and any
path with `::`; field/tuple/index access; macros (`ident!(..)` — an untrusted
macro is **never** expanded); `/` and `%`; `&&` and `||`; `if`/block used as an
*expression* (value position); `as` casts; string/char/float literals; `async`,
`unsafe`, `loop`, `for`, `break`, `continue`, `?`.

## The spines (load-bearing claims)

Each spine is a claim RS0 must *enforce*, not merely intend. They are the surfaces
harden-spec attacks.

- **S-AUTH — authority closure.** The synergy above. Enforcement: every call
  target must resolve to an in-subset `fn` declaration in the same file (an
  unresolved or external call → reject); no `::`, macro, method, or borrow can
  appear; `i64`/`bool` are register values (no heap, no `Alloc`). If the subset is
  truly closed, "provably authority-free" holds by construction. **This is the
  claim whose completeness is existential** — a single in-subset construct that
  reaches a host surface forfeits the whole guarantee.
- **S-ORACLE — oracle agreement (the H2 spine, from FE2).** The checker assigns
  every node the type the SIGIL compiler *would resolve*, and rejects any in-subset
  type error **before** emission — so emitted SIGIL never fails for a translator
  reason (no masquerading `T`-codes). Totality of typing is insufficient; a uniform
  "everything i64" checker is a defect. RS0's surface is small (`i64`/`bool`, fully
  annotated), which makes soundness tractable — but it must still be *proven* by the
  differential harness, not assumed.
- **S-TOTAL — totality is frontend-owned.** The hand-rolled parser checks
  `limits::MAX_DEPTH` **before every recursive descent**; adversarial nesting →
  `FE602`, never a native stack overflow (in the parser, the walkers, the recursive
  `Drop`, or the FE500 re-parse). *Bounding recursion depth ≠ bounding AST depth* —
  the bound is on structural depth, checked before descent. `syn` is a **dev-dep
  differential oracle only** (see Parser strategy); it is never on the shipped or
  liveness path.
- **S-SEM — value-semantics faithfulness.** The emitted SIGIL must *compute* what
  the Rust source computes:
  - **Integer overflow.** SIGIL `i64` `+ - *` lower to raw wasm `i64.add/sub/mul`
    ([wasm.rs:2124](../../crates/sigil-compiler/src/wasm.rs)) — **wrapping**,
    two's-complement, no trap. RS0 is therefore faithful to Rust's
    **`overflow-checks=off` (release)** semantics, and **NOT** to debug's
    overflow-*panic*. This is the one accepted, **documented** divergence (the
    NC-L1 analog): RS0 models `wrapping_{add,sub,mul}`. Debug-faithful *trapping*
    i64 is deferred to a future checked-arithmetic rung. Because a wrap is a
    *silent value* divergence (not a trap), this MUST be stated loudly to authors.
  - **`/` and `%` excluded** — sidesteps div-by-zero and `i64::MIN / -1` (Rust
    panics; wasm `i64.div_s` traps — different again) — deferred.
  - **Tail expression = return.** A block's trailing no-semicolon expression is its
    value → emit `return e;`. A trailing *statement* (`e;`) yields unit. Only a
    *simple* value expression is a legal RS0 tail (an `if`/block tail is value
    position → reject, `FE690`). Return-path analysis (the FE306 analog): a non-unit
    fn must reach a `return`/tail `e` on **every** path (`if`/`else` counts iff both
    branches do) → else `FE632`.
  - **No references.** RS0 has no `&`/`&mut`, so there is no aliasing and no
    mutate-through-alias to diverge — value semantics are exact. This deliberately
    sidesteps the Rust-borrow ↔ SIGIL-ownership mapping (deferred, and gated when
    introduced).
  - **`let mut` / reassignment.** Rust `let mut` → SIGIL `let mut`; reassigning a
    non-`mut` local or a parameter → `FE633` (the FE307 analog). **`let` shadowing
    of a live binding is rejected** (`FE635`), never alpha-renamed — flat scope
    merge would otherwise risk a silent redirect.
- **S-HYGIENE — identifier gating.** Every Rust identifier is validated with
  `is_legal_identifier` (ASCII `^[A-Za-z_][A-Za-z0-9_]{0,63}$`, `MAX_IDENT_BYTES`)
  and `is_sigil_keyword` (delegates to the real lexer, no drift). A **raw
  identifier** (`r#type`), a **non-ASCII** identifier (Rust permits Unicode XID),
  an over-64-byte identifier, or one colliding with a SIGIL keyword or the reserved
  `__fe_` prefix → `FE620`.
- **S-SELFCHECK — internal invariants.** The emitted text is re-parsed with the
  real SIGIL lexer/parser; a failure means the *translator* is buggy → `FE500`
  (shared internal code). A two-run byte-compare guards determinism → `FE502`.

## Strict Constraints (hardening)

Existential findings from the teardown, as hard MUST/MUST-NOTs. Each is a property
the implementation must make true by construction, not merely intend.

- **SC-1 — emitter output alphabet (MI-1/MC-1).** The emitter MUST be able to
  construct ONLY the node kinds in the RS0 subset table. It MUST NOT be able to
  emit any identifier naming a SIGIL intrinsic, builtin, `extern`, capability, or
  effect. Enforced by construction (no emit path builds such a node) **and** a test
  asserting the emitted-token alphabet ⊆ the allow-list.
- **SC-2 — call closure + ambient-name capture (MI-2/UP-3).** Every emitted call
  name MUST resolve, **pre-emission**, to an in-subset user `fn`; an unresolved
  target → `FE634`. A user identifier colliding with a SIGIL keyword, **an
  emittable builtin call-name** (e.g. `trap_if`), or the `__fe_` prefix MUST be
  rejected `FE620` — the denylist extends past keywords to the builtin namespace,
  because a bare `trap_if(..)` would otherwise bind the *builtin*, an authority leak.
- **SC-3 — signature/argument closure (UP-3).** A call is in-subset only if the
  callee's WHOLE signature is in-subset AND the arguments type-check against it;
  else `FE630`. "Declared" is never sufficient.
- **SC-4 — literal totality (MI-4).** Only an exact in-range **decimal** `i64`
  literal is accepted; any suffix (`5i32`), radix (`0x`/`0b`/`0o`), underscore, or
  out-of-range value → `FE612`; a literal in `bool` position → `FE630`. No silent
  truncation or radix reinterpretation.
- **SC-5 — tail-expr + return totality (MC-4/UP-2).** A tail expression is
  recognized ONLY at function-body top level; a trailing expression elsewhere is a
  statement or a reject. Return-path analysis MUST be total: a non-unit fn that does
  not reach a `return`/tail on every path → `FE632` **before emit** (never a `T044`
  masquerade).
- **SC-6 — positive conformance floor (MC-3).** The suite MUST contain ≥ 8
  `compile/` fixtures that translate AND compile clean through the real
  `sigil-compiler`. A green suite with an empty accept-set is a failing suite.
- **SC-7 — oracle non-vacuity (MC-2/MC-5).** The suite MUST include (a) a negative
  meta-test: a checker mutation typing all expressions `i64` MUST fail the suite;
  and (b) a `syn` differential that compares **normalized AST structure**, not
  accept/reject booleans.
- **SC-8 — whole-pipeline totality (MI-5).** `MAX_DEPTH` MUST bound EVERY recursive
  walk — parser, checker, emitter, the FE500 re-parse, and the AST's `Drop` — not
  just the parser. Adversarial nesting → `FE602` before any deep tree is built
  (*bounding recursion depth ≠ bounding AST depth*).
- **SC-9 — lexer/UTF-8 + determinism totality (UP-5/MI-3).** The lexer MUST consume
  arbitrary UTF-8 totally (a multi-byte char in a comment / rejected string /
  mid-identifier MUST NOT panic or desync byte-offset spans; a non-ASCII identifier
  → `FE620` at a defined point). No emit-path pass may depend on hash-container
  iteration order; fn/local emission MUST be source order (→ `FE502`).

## FE6xx code family (RS0)

`FE5xx` is unavailable (the shared `FE500` parse self-check and `FE502`
determinism marker live there); RS0 takes **`FE6xx`**. Every code is a fail-closed
reject that emits nothing.

| Code | Meaning |
|---|---|
| `FE601` | construct outside the RS0 subset (item/expr/stmt/type not in the allow-list) — fail-closed catch-all |
| `FE602` | input/complexity bound exceeded (bytes, nesting depth, function count) |
| `FE610` | a type annotation other than `i64`/`bool`, or a **missing** required annotation |
| `FE611` | `/` or `%`, or an operator outside the RS0 whitelist |
| `FE612` | numeric literal not an exact in-range decimal `i64` |
| `FE620` | identifier outside the SIGIL charset / raw / non-ASCII / over-length / keyword or `__fe_` collision |
| `FE630` | an in-subset expression/statement is ill-typed (operand/argument/condition/return type) |
| `FE632` | a non-unit function has a path that does not `return` (return-path analysis) |
| `FE633` | reassignment of a non-`mut` local or a parameter |
| `FE634` | a reference resolves to no in-scope binding (unresolved identifier / call target) |
| `FE635` | `let` shadowing of a live binding (rejected, not renamed) |
| `FE690` | `if`/block used in value/expression position (deferred desugar) |
| `FE500` | emitted SIGIL failed the parse self-check (internal — translator bug) — shared |
| `FE502` | two-run byte-compare found nondeterministic output (test-gate marker) — shared |

## Parser strategy — hand-rolled + `syn` dev-oracle

The shipped translator **hand-rolls** the lexer + parser for the RS0 subset, for
the two properties this subsystem prizes: **totality by construction** (S-TOTAL —
`MAX_DEPTH` before descent; `syn` owns its own recursion and can stack-overflow on
adversarial nesting, an abort, not a catchable panic) and a **minimal fail-open
surface** (hand-rolling only ever *constructs* supported nodes, versus gating
`syn`'s ~180-variant full-Rust AST behind a giant allow-list — the "walker forgot
an arm" bug class, maximized). RS0's subset is tiny and fully annotated, so the
main thing `syn` buys (correct Rust tokenization) mostly does not bite yet.

`syn` is pulled in as a **`[dev-dependencies]` differential oracle**, never on the
shipped or liveness path: a test asserts the hand-rolled parser agrees with `syn`
on every in-subset fixture, and that every construct `syn` accepts but the frontend
rejects is genuinely out-of-subset. This buys `syn`'s battle-tested correctness as
a *hardening signal* without putting it in the trusted-liveness build — in the
spirit of the project's differential-harness rituals. **Crossover:** when a future
rung reaches Rust's genuinely hard grammar (generic bounds, turbofish, full pattern
syntax, `where`-clauses), `syn`'s advantage flips and the pre-scan cost becomes
worth paying; RS0 is "hand-roll while the subset is small," not "hand-roll forever."

## Constraints & Fallbacks

Every threat gets a dumb physical bound (an exact number, a fixed whitelist, or a
structural impossibility) and a fail-fast that emits nothing. RS0 reuses the
crate's [`limits`](../../crates/sigil-frontends/src/lib.rs) module — the numbers
already align to compiler constants (S005 = 5 MiB input, S006 = 10 000 functions):

| Threat | Bound | Fallback |
|---|---|---|
| Oversized input | `MAX_INPUT_BYTES` = 5 MiB | `FE602` |
| Unbounded nesting (stack DoS) | `MAX_DEPTH` = 64, checked **before** each descent | `FE602` |
| Function explosion | `MAX_FUNCTIONS` = 10 000 | `FE602` |
| Identifier abuse | `MAX_IDENT_BYTES` = 64, ASCII charset | `FE620` |
| Synth-name collision | reserved `__fe_` prefix (disjoint by construction) | `FE620` |
| Out-of-subset construct | closed allow-list | `FE601` (or a precise `FE6xx`) |
| Emitted-SIGIL malformation | real-parser re-parse self-check | `FE500` |
| Nondeterminism | source-order emission; no hash-order dependence; two-run byte-compare | `FE502` |
| Ambient-authority node (SC-1) | fixed finite emitter alphabet | emitted-token-alphabet test red |
| Builtin-name capture (SC-2) | denylist = keywords ∪ emittable builtins ∪ `__fe_` | `FE620` |
| Unresolved / out-of-subset call (SC-2/SC-3) | resolve to in-subset user `fn` pre-emit | `FE634` / `FE630` |
| Non-decimal / out-of-range literal (SC-4) | exact in-range decimal i64 only | `FE612` / `FE610` |
| Non-exhaustive return (SC-5) | return/tail on every path; tail only at fn-top | `FE632` (before emit) |
| Empty accept-set (SC-6) | ≥ 8 compile-clean fixtures | suite red |
| Vacuous checker (SC-7) | uniform-i64 mutation must fail; `syn` diff over AST | meta-test red |
| Deep AST (any walk) (SC-8) | `MAX_DEPTH` on parser+checker+emitter+re-parse+`Drop` | `FE602` |

## Anti-goals (RS0)

- **References / borrows.** No `&`/`&mut`; the Rust-borrow ↔ SIGIL-ownership
  mapping is deferred and will be gated on provable agreement when introduced.
- **Type inference.** RS0 requires explicit annotations; no Hindley-Milner in an
  untrusted frontend — an undetermined type is a reject, not a guess.
- **Debug-mode overflow panic.** RS0 models `overflow-checks=off` (wrapping) i64;
  debug-faithful trapping arithmetic is a later checked-arithmetic rung.
- **`/` `%`, `&&` `||`, `if`/block-as-expression.** Deferred (semantics divergence
  / desugar not yet ported).
- **Structs, enums, `match`, generics, traits, closures.** Deferred; structs +
  enums + `match` are the natural next expansion (SIGIL has all three).
- **Macros, ambient `std`, any I/O.** Permanently out-of-subset — the S-AUTH
  guarantee depends on it.
- **Source-map fidelity.** An identity map is acceptable (inherits the FE0 T4
  anti-goal); diagnostics on emitted SIGIL need not map to exact `.rs` spans.
- **Corpus ingestion.** RS0 does not feed translator output into `sigil-corpus`.
- **Small accept-set from no-shadowing (UP-4, academic).** Rejecting all `let`
  shadowing (and much idiomatic Rust) shrinks the accept-set; RS0 optimizes
  *soundness over breadth*, and every such rejection fails loudly (`FE635`), never
  silently. Breadth is a later-rung concern — not a fallback RS0 owes.
- **In-subset non-termination (academic).** A pure recursive or `while` program
  that never halts is a runtime/fuel concern, not a translate-time one (mirrors the
  TS `while` anti-goal). Out of scope.
- **`syn`-oracle robustness (academic).** The differential feeds ONLY the bounded
  in-subset fixture corpus, never adversarial input, so `syn`'s own recursion is
  never on a liveness path. Hardening `syn` against adversarial nesting is out of
  scope by construction.

## Repo setup (concrete)

Mirrors the TypeScript / Solidity layout exactly:

- **New module** `crates/sigil-frontends/src/rust/{lexer,parser,check,emit,mod}.rs`.
  No `desugar.rs` in RS0 (added when `&&`/`||` / if-expr land). Pipeline:
  `lexer::lex → parser::parse → check::check → emit::emit`, each fail-fast + total.
- **`lib.rs`:** `pub mod rust;`; add the `FE6xx` constants to the `codes` module;
  register `"rust" | "rs" => Some(Box::new(rust::RustFrontend))` in `frontend_for`.
- **`Cargo.toml`:** add `syn` (with `features = ["full"]`) + `proc-macro2` under
  `[dev-dependencies]` only.
- **CLI:** no changes beyond the `frontend_for` arm — `translate` / `check --from`
  dispatch is fully generic ([main.rs](../../crates/sigil-cli/src/main.rs)).
  (Optionally refresh the cosmetic "(try `typescript`)" hint strings.)
- **Tests:** `crates/sigil-frontends/tests/rust_golden.rs` (conformance) with
  `tests/frontends/rust/compile/*.rs` + `*.sigil` and `tests/frontends/rust/reject/*.rs`;
  plus `crates/sigil-frontends/tests/rust_parser_differential.rs` (the `syn` oracle).
- **Docs:** this file; a Rust section appended to
  [`foreign-frontends.md`](foreign-frontends.md) once RS0 lands.

## The broader arc

- **RS0** (this doc) — authority-free value-semantics core; the pipeline, sound
  checker, totality, and golden + `syn`-differential harness.
- **RS1** — capability threading (the FE0 analog): `#[sigil::cap(Name, deadline=D)]`
  → a `cap type` + a synthetic cap parameter *moved* into a terminal consumer;
  enforcement demo = a stale cap → **T199**. (Watch the FE011 "decorative cap"
  trap: the compiler does not flag an *unused* cap param, so the translator must
  thread it.)
- **RS2** — effect rows (the FE1 analog): `#[sigil::effects(A, B)]` → a sorted
  `! { A, B }` row + co-emitted `effect` decls (the fail-open spine: an effect name
  with no decl is silently dropped). Enforcement demo = effect leakage → **E001**.
- **Later** — structs / enums / `match`; then references mapped to SIGIL
  ownership/exclusivity (gated on agreement); then refinements (`#[sigil::requires]`
  → Z3) and taint (`pub⊑int⊑sec`) as additional synergies on the RS0 spine.
