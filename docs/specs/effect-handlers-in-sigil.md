# Effect Handlers (Algebraic Effects with Operations) in SIGIL — Design

**Status:** EH0–EH3 IMPLEMENTED (the full front-end). Realized ladder: EH0 (parse + AST, #400) → EH1
(operation registry + `perform` shape-checking, #400) → EH2 (clause-handle checking — coverage / arity /
bare-on-op, #401) → EH3 (`Type::Never` + operation types; typed nodes `TypedExprKind::Perform/ClauseHandle/
Resume`; the C-VIS pass-coverage gate; effect **discharge** + orphan-`perform` E010; #402). Every form is
parsed, typed, and walked by every security pass, but **gated before AIR with E004**
(`effect_check::check_effect_handlers_gated`), so byte-identical AIR holds. **EH4 (this design's subject)
= the LOWERING** — the evidence-passing desugar that brings the gate down and makes handlers RUN; it
*unifies* the original EH3-abortive and EH5-scoped rungs (both need cross-function control transfer — the
"abortive = `br`, erases" framing was false: a `perform` lives in the scrutinee's callee, not lexically in
the handle). Then capability hardening (EH008). Codes are the Effect `E0xx` family (the spec's "EHxxx" are
logical role labels): E004 gate, E005–E007 perform shape, E008 coverage, E009 bare-on-op, E010 orphan.
**Scope:** the trusted (Rust) compiler plus its self-hosted verification shadows. Generators / async /
multi-shot continuations are explicitly **out of scope** (see §Explicit Anti-Goals) and must reject
*loud* (EH007), never silently miscompile.

This spec was produced through the project's adversarial-hardening ritual: Adversarial-Compiler teardown
→ Existential/Academic triage (code-grounded findings) → Constraint Matrix (§Constraints & Fallbacks,
Boring Limit + Fail-Fast). It adopts the normative format of [typestate-in-sigil.md](typestate-in-sigil.md)
and [hkt-in-sigil.md](hkt-in-sigil.md).

---

## Context

SIGIL has an effect **system** but effects are inert. Today `effect Name;` is a bare marker
(`EffectDecl { name, span }`, `crates/sigil-compiler/src/ast.rs:152`), and `handle E { body }` merely
**widens the available effect row** inside the body (`effect_check.rs:192`) and lowers **transparently
inline** (`air.rs:3664`). There are no operations and no caller-defined meaning.

This epic makes effects **first-class**: effects gain typed **operations**; a `handle` block's
**clauses** decide what those operations *mean*. That delivers — as library code, capability-tracked —
**exceptions**, **reader/state/config**, and **dependency-injection of authority**: the classic
algebraic-effects core *minus continuations*.

```sigil
effect Reader { fn get() -> i64; }
effect Fail   { fn raise(msg: str) -> never; }

fn parse(c: &Config) -> i64 ! { Fail, Reader } {
  let base = perform Reader.get();             // scoped: resumed once
  if base < 0 { perform Fail.raise("neg"); }   // abortive: never returns here
  return base * 2;
}

handle parse(cfg) {                            // the caller assigns meaning
  Reader.get()  => resume 42,                  // tail-resume a value to the perform site
  Fail.raise(m) => -1,                         // no resume => the value of the whole handle
}
```

### Why the backend forces the scope boundary (grounded)

- **No continuation machinery.** wasm = structured control flow only; bump allocator, no `free`/GC;
  monomorphic dispatch; the sacred *byte-identical-AIR* invariant. `ask` does **not** suspend (it is a
  synchronous nested call). True multi-shot continuations would break byte-identity structurally, **leak**
  under the bump allocator, and re-open the affine/cap **duplication** holes that the typestate (#397) and
  `mint` (#396) epics just closed. Out of scope for this backend.
- **The `Handle` node is destructured at 9 sites**, four of them security passes — `air.rs:1062`/`2086`,
  `effect_check.rs:192`, `ring_check.rs:266`, `taint_check.rs:721`, `type_check_v2/refinement.rs:1182`,
  `capability_tc.rs:816`, `type_check/mod.rs:1142`, `resolve.rs:1403`. Each reads a single `.body: Block`
  today; growing the node forces every one to walk the scrutinee + clause bodies (§C-VIS).
- **No `Type::Never`.** `Type` (`types.rs:38`) has ~20 variants and no bottom type; abortive ops (`-> never`)
  need one (prerequisite sub-rung EH1a; §C-NEVER).
- **`T069` already exists** for unknown-effect in `handle` (`capability_tc.rs:776`) → **extend** it (EH004).
- **C-MI2 — the load-bearing find.** `lower_handle_expr` lowers the body **inline** and *relies on* `T068`
  banning control flow so its dispatcher can `unreachable!()` (`air.rs:3659-3664`; ban at
  `capability_tc.rs:732`). Clause bodies (resume/abort) introduce branching the inline path cannot
  represent. The clause form is therefore a **distinct AST variant** with a dedicated check + lowering path;
  the bare path stays untouched (§C-PATHSEP).

---

## Surface syntax

- **Operations** grow `EffectDecl`: add `ops: Vec<EffectOp>`; `EffectOp` is a `fn`-signature-without-body,
  mirroring `ExternFnDecl` (`ast.rs:170`). The braced effect form **already parses** (`parser.rs:4212`) —
  fill it with op decls. **An operation's return type is the resumed-value type** (the forward-compat seam;
  for an abortive op it is `never`).
- **`perform Effect.op(args)`** — a **contextual keyword** firing only on the unambiguous
  `perform <Ident>.<Ident>(` shape (mirrors the `mint` trick, `parser.rs:4082`). `<ident> <ident>` is
  already a parse error in expression position, so the trigger never overlaps valid code. New
  `Expr::Perform(PerformExpr { effect, op, args, span })` — a **first-class typed node kept through
  type-check**, with **pluggable lowering** (abortive → `br`; scoped → evidence call; future → suspend).
- **`handle expr { Op(x) => body, ... }`** — a **new disjoint variant** `ClauseHandle { scrutinee, clauses }`,
  kept separate from the existing bare `Handle { effects, body }` (which stays byte-identical and is legal
  only for operation-less effects — §C-BARE). `resume <expr>` inside a scoped clause; a clause with no
  `resume` is abortive. The `resume`/`k` binder is reserved now even though general resume is gated to EH5.

---

## Type rules & diagnostic codes (new `EH` family)

Codes in `diagnostics/codes.rs` + `CORE_CODES` (`diagnostics/registry.rs`); rules in a new
`type_check/effect_handler_tc.rs`.

| Code  | Checks |
|-------|--------|
| EH001 | `perform` of an unknown operation, or op not in the named effect |
| EH002 | **orphan perform** — `perform E.op` requires `E` in the fn row OR an enclosing clause-handle of `E` |
| EH003 | a clause's parameters/return must match the operation's signature |
| EH004 | unknown effect in a clause-handle (**extends `T069`**) |
| EH005 | **coverage bijection** — clause-set ↔ the effect's operation-set exactly; no missing, extra, foreign, or wildcard clause |
| EH006 | scoped clause `resume` rules: **exactly one** in **tail** position; resume value type = op return type |
| EH007 | **deferral gate** — multi-shot / non-tail / cross-boundary / generator forms rejected with an explicit *"deferred to a future epic"* message |
| EH008 | **borrow-only cap injection** — a clause that moves/returns/stores a cap *value* (any aggregate/capture/actor channel) is rejected |
| EH009 | **intermediate-rung gate** — `perform`/clause forms rejected until their rung lands (no half-accept) |
| EH010 | bare `handle E {}` used on an **operation-bearing** effect (use the clause form) |
| EH011 | a `Never`-typed value used as an operand / in non-tail position |

- **Discharge:** a clause-handle **removes exactly the handled effect** from the ambient requirement
  (generalizing today's *widen* at `effect_check.rs:202`); every **other** effect of the scrutinee keeps
  leaking upward (§C-DISCHARGE).
- **`Type::Never`** (EH1a): the bottom type; **non-denotable** (no surface syntax), occurs only as an op
  return type / the type of a `perform` of an abortive op, **excluded from monomorph keys** (§C-NEVER).

### Capability / security integration

- **Two-ring:** clause-handle discharge is allowed **inside the inner ring**; bare `handle Unsafe` stays
  **trusted-only** (`E002`, unchanged at `effect_check.rs:194`).
- Clause bodies are checked **exactly like a function body in their lexical scope** — a cap referenced but
  not in scope is an ordinary name-resolution error, not a silent grant (AG-7).
- **Evidence-passing soundness (EH5):** the implicit handler record is a **standard closure**, so the
  existing linear-capture / borrow rules and EH008 govern it; the implicit param is threaded **only**
  through functions whose row contains the handled effect — pure fns stay byte-identical (§C-EVID).

---

## Rung ladder (smallest-first; each independently green: `cargo test --workspace`, `clippy -D`, `fmt`)

- **EH0 — parse + AST.** Grow `EffectDecl.ops`; add `PerformExpr` + the disjoint `ClauseHandle`. Parser: op
  decls in effect braces, contextual `perform`, clause-handle. EH009 gates the new forms. **Byte-identical
  AIR.** Mirror `selfhost/parser.sigil`. Tests: `parser_differential.rs` + parse fixtures (incl. a C-NOVAC
  fixture).
- **EH1 — type-check surface + `Never`.** EH1a adds `Type::Never`. Register `EffectOp` sigs
  (`universe.rs:430`). Type `PerformExpr` (EH001/EH002), clause sig match (EH003), coverage (EH005), extend
  `T069`→EH004, EH010, EH011. Mirror `typecheck.sigil`. Tests: `effect_handlers.rs` + `typecheck_differential.rs`.
- **EH2 — effect discharge + C-VIS.** Generalize the Handle arm (`effect_check.rs:192`) to clause-aware
  discharge; `perform` requires its effect. Route all 9 walk sites through one shared
  `walk_handle(scrutinee, clauses)` (§C-VIS). Mirror `selfhost/effect_check.sigil` + `effect_check_differential.rs`.
  **Still erases.**
- **EH3 — abortive lowering (resume-zero).** A clause without `resume` produces the `handle` value via
  discriminated-union early-return / structured `br` (the Solidity `require`→trap and `&&`/`||` ANF
  precedents). **Outward unwind only** — no continuation capture, **erases**. Dedicated clause check +
  lowering path (NOT `lower_scoped_body_inline`); relax `T068` for clause bodies only (§C-PATHSEP). Tests:
  `effect_handlers_runtime.rs` (the `Fail.raise` abort path via `execute_ephemeral`).
- **EH4 — capability hardening (EH008).** Borrow-only cap-injection gate via the TS4 aggregate-walk
  (`type_contains_typestate` sibling); a 4-channel sweep (record/enum/array/generic + closure-capture +
  actor-field) (§C-INJECT) + an adversarial sweep.
- **EH5 — scoped-resume via evidence-passing (capstone).** Thread an implicit handler record (a closure)
  through effect-carrying functions; lower `perform E.op(args)` to a `CallIndirect` through it; the handle
  site builds the record from the clauses; `resume` = the clause returning the resumed value to the perform
  site (§C-RESUME, §C-EVID). Re-blesses effectful-fn wasm snapshots; pure-fn snapshots stay byte-identical;
  **no new host import, no `IMPORT_COUNT` bump.** Tests: runtime exec of `Reader.get() => resume 42`.

**Forward-compat hooks** (so the deferred continuation epic is purely additive): op return type =
resumed-value type; `PerformExpr` is a stable typed node with pluggable lowering; the EH5 handler record is
where a future resumption pointer lives; reserved `resume`/`k` binder; handler power as a checked attribute
(EH007 gates the unimplemented levels).

### What erases vs. what is new runtime
- **EH0–EH4:** erase before AIR — **byte-identical**, no host import.
- **EH5:** effect-carrying fns gain an implicit handler param + `CallIndirect` at `perform` — not
  byte-identical (re-bless effectful-fn snapshots), but reuses verified closures, adds **no host import**,
  leaves pure fns untouched.

---

## Strict Constraints (existential — enforced by construction)

- **C-PATHSEP.** Bare `Handle` and `ClauseHandle` are distinct AST variants; the inline path
  (`lower_scoped_body_inline`) accepts only the bare variant. *Fail-fast:* `unreachable!()` if fed a clause.
- **C-VIS.** All 9 `Handle` destructure sites route through one shared `walk_handle(scrutinee, clauses)`
  (or visit both fields explicitly); **no `..`/`_`** on the new fields. *Fail-fast:* adding a field without
  updating a pass is a non-exhaustive-match **build error** — a security pass cannot silently skip clauses.
- **C-COV.** Clauses are an exact bijection with the discharged effect's operation set — 0 missing, 0 extra,
  0 foreign-op, 0 wildcard. *Fail-fast:* EH005 names the offending op.
- **C-LOWER.** Every `Perform` / `ClauseHandle` lowers to exactly one Call/CallIndirect/Branch; none reaches
  `air::lower` un-lowered (no "erase by deletion"). *Fail-fast:* ICE `unreachable!("perform reached AIR")`.
- **C-RESUME.** A scoped clause body = exactly one `resume <e>` in tail position, none elsewhere.
  *Fail-fast:* EH006; ≥2 or non-tail → EH007.
- **C-ORPHAN.** `perform E.op` requires `E` in the fn row or an enclosing clause-handle of `E`. *Fail-fast:* EH002.
- **C-NEVER.** `Never` is non-denotable, occurs only as op-return / perform-of-abortive type, excluded from
  monomorph keys. *Fail-fast:* EH011 on Never-as-operand; assert `Never ∉ mangle`.
- **C-BARE.** Bare `handle E {}` is legal only when `E` has 0 operations. *Fail-fast:* EH010.
- **C-INJECT.** A clause may name `&Cap`, but a cap *value* may not appear in its return type nor any
  record/enum/array/closure-capture/actor-field within it (reuse the TS4 walk). *Fail-fast:* EH008 at the channel.
- **C-DISCHARGE.** `handle` removes exactly the handled effect; all others stay in the row. *Fail-fast:*
  an unhandled effect still fires EH002/`E001` upward.
- **C-NOVAC.** Each differential rung ships ≥1 fixture containing op-decl + `perform` + clause-handle,
  asserted byte-identical both sides. *Fail-fast:* the differential test names the divergent record.
- **C-EVID.** The EH5 handler record is a standard closure (linear-capture + EH008 apply); the implicit
  param is threaded only through effect-carrying fns. *Fail-fast:* a handler closure capturing a cap *value*
  → EH008; an effectful fn reached with no handler in scope → EH002.

## Explicit Anti-Goals (out of scope — each fails *loud*, never silent)

- **AG-1 Multi-shot resume** (≥2×) — unsound under affine values + leaks under the bump allocator. Rejected
  by C-RESUME → EH007.
- **AG-2 Non-tail / conditional resume** — needs a real continuation. Rejected by C-RESUME → EH007.
- **AG-3 Cross-boundary resume** (a `perform` reached through an indirect/closure/actor frame the handler
  record doesn't thread) — dynamic-handler-stack / stack-switching territory. Rejected by C-EVID/C-ORPHAN →
  EH002/EH007. Future epic.
- **AG-4 Recursive / re-entrant handlers** (a clause performs the effect it handles) — deferred; rejected loudly.
- **AG-5 Dynamic handler installation** (handler chosen at runtime) — only static `handle` blocks; out.
- **AG-6 `perform`/`resume` contextual-keyword collision** — safe by the proven `mint` precedent;
  `<ident> <ident>` is already a parse error, so the trigger never overlaps valid code. No fallback owed.
- **AG-7 Out-of-scope cap referenced in a clause** — ordinary name-resolution error (N-code); a clause is
  checked exactly like a function body in its lexical scope. Not a new effect-system hole.
- **AG-8 Single-function generators / `yield`** (the fibonacci example) — needs the deferred state-machine
  inversion epic. Rejected by C-RESUME → EH007 naming the future epic.

## Constraints & Fallbacks (Boring Limit · Fail-Fast)

| ID | Boring Limit | Fail-Fast |
|---|---|---|
| C-PATHSEP | bare vs clause = distinct AST variants; inline path takes only bare | `unreachable!()` if fed a clause |
| C-VIS | one `walk_handle`; no `..`/`_` on new fields | non-exhaustive-match **build error** |
| C-COV | `#clauses == #ops`, exact name bijection; 0 wildcard/foreign | EH005 names the op |
| C-LOWER | each `Perform`/`ClauseHandle` → exactly one Call/CallIndirect/Branch | ICE "perform reached AIR" + op name |
| C-RESUME | scoped clause = 1 `resume` in tail position | EH006; else EH007 |
| C-ORPHAN | perform requires effect in row or enclosing handle | EH002 |
| C-NEVER | `Never` non-denotable; ∉ mono keys | EH011; assert on mangle |
| C-BARE | bare `handle E {}` only if `E` has 0 ops | EH010 |
| C-INJECT | no cap value in any return/aggregate/capture/actor channel of a clause | EH008 at the channel |
| C-DISCHARGE | discharge removes exactly the handled effect | unhandled effect → EH002/`E001` upward |
| C-NOVAC | ≥1 op+perform+clause fixture per differential rung | differential test names the divergence |
| C-EVID | handler record = closure; implicit param only on effectful fns | EH008 (cap capture) / EH002 (no handler) |

**Ambient backstop:** the parser nesting cap bounds handle/clause depth; the fuel meter bounds runtime; any
un-lowered or under-checked node **ICEs rather than miscompiles**.

---

# Appendix: EH4 Lowering Design — the evidence-passing desugar

EH0–EH3 are done: handlers are fully parsed, typed, effect-checked, and gated (E004). EH4 makes them
**run**. Per the user's decision (2026-06-25) it is a **single unified lowering** serving both abortive and
scoped clauses via **evidence-passing**: effect handlers desugar to the implicit closure-passing SIGIL
already verifies, so **AIR/wasm machinery is unchanged** — the new work is one pre-AIR typed-AST pass.

## Architecture: a pre-AIR typed-AST → typed-AST pass

`desugar_effect_handlers(typed: &mut TypedProgram)` runs in `compiler.rs` **after** the typed-program
checks and **before** `air::lower`, replacing the role of the E004 gate for the cases it handles. It
produces only **existing** typed-AST nodes (closures, indirect calls, calls, records), so `air::lower`
needs no new arms — the `TypedExprKind::Perform/ClauseHandle/Resume` arms that currently ICE are removed
once nothing un-desugared survives. **Incremental-safety invariant:** the desugar transforms only the
shapes it supports; everything else stays E004-gated (`check_effect_handlers_gated` runs as the backstop
until the desugar is complete), so **every intermediate rung is green**.

## The evidence-passing translation

An **effect's evidence** is a value carrying its operation clauses. Representation:
- **single-operation effect** → evidence is one **closure** `Fn(op_params) -> op_ret` (the op's clause).
- **multi-operation effect** → evidence is a **record of closures**, one field per operation.

A function whose effect row is `! { E1, .., En }` is rewritten to take **one implicit evidence parameter
per effect** (appended after the user params). Threading is dictated by the (already-checked) effect rows:
- `perform Ei.op(args)` → an **indirect call** through the evidence param `$ev_Ei` (its `op` clause):
  `CallIndirect($ev_Ei[.op], args)`. The call returns the operation's value — for a **scoped** clause the
  resumed value, so the perform site simply continues with it. No continuation capture.
- a call to an effectful callee `g(...)` where `g ! { Ei }` → pass the caller's own `$ev_Ei` down
  (propagation), since the effect system guarantees the caller either handles or declares `Ei`.
- `handle <call f(args)> { Ei.op(b) => body, .. }` → **build** the evidence for each discharged `Ei`
  (synthesize a closure per clause — `resume v` becomes the closure's `return v`; an **abortive** clause
  returns its value as an abort, see below), then rewrite the scrutinee call to `f(args, $built_ev..)`.
  The handle expression becomes that call (scoped) or the abort-join (abortive).

Synthesizing a closure **after** type-check mirrors `infer_closure_expr` (expressions.rs:6220): a new
`TypedFunction { kind: Closure, .. }` is appended to the module and a `TypedClosureConstructExpr` captures
the clause's free variables. Clause binders become the closure's parameters (typed from `op.params`).

## Abortive vs. scoped (the one genuinely-new control-flow bit)

- **Scoped** (`resume v`): the clause closure returns `v`; the perform site continues. Pure value flow.
- **Abortive** (no `resume`): the clause produces the **value of the whole `handle`**, abandoning the rest
  of the handled computation — i.e. control must cross back from the perform site (deep in a callee) to the
  handle. With no continuations, this is a **discriminated-union return + early-return propagation** (the
  Solidity `require`→trap / `?`-style precedent): a function that may perform an abortive op returns
  `{ value | aborted(payload) }`; `perform Ei.op(args)` for an abortive op becomes `return aborted(clause(args))`;
  every caller on the path propagates `aborted`; the handle site matches it and yields the clause value.

### EH4.2 — abortive, the direct-performer simplification (NO discriminated union)

The general abortive lowering above (discriminated-union return + early-return propagation) is only needed
when the `perform` sits in an **intermediate callee** (EH4.3). For the EH4.0/4.1 shape — the scrutinee is a
**direct call to the performer** that performs the operation **itself** — abortive collapses to a plain
**early return**, because of a type identity:

> An abortive operation's return type is `never`, so a `perform` of it never yields a value to its site;
> the clause instead produces the **value of the whole `handle`**. The handle's type **is** the
> scrutinee's type, i.e. the **performer's return type `T`**. So the abortive clause body has type `T`,
> the same type the performer returns.

Therefore the abortive clause becomes a closure `Fn(op_params) -> T` (returning the *performer's* `T`, not
the op's `never`), and an abortive `perform Ei.op(args)` is rewritten to **`return $ev_op(args);`** — the
performer calls the clause closure to compute the handle value and returns it, abandoning the rest of its
body. Normal `return v` paths are **untouched** (they already return `T`); no union, no per-caller
propagation, no match at the handle site (`handle f(args){..}` → `f(args, $clause_closure..)`, exactly as
scoped). This composes with EH4.1: an effect may mix scoped ops (`$ev$E$op : Fn(op_params)->op_ret`,
perform→`IndirectCall` *expression*) and abortive ops (`$ev$E$op : Fn(op_params)->T`, perform→`return`
*statement*); each `OpEvidence` carries an `abortive` flag (set when `op.ret == Type::Never`).

The genuinely-new machinery vs EH4.1 is the **statement-level** rewrite (an abortive `perform` must become
a `return`, not a discarded expression-statement — see **LC-ABORT2**). EH4.2 scope mirrors EH4.0/4.1: a
single effect; the performer performs every op directly at statement level; abortive `perform`s appear
**only** as a **bare statement** `perform E.op(args);` (typically inside an `if`), with the performer also
having a normal `return` elsewhere; abortive clause bodies are the same simple whitelist as scoped (and
must type as `T` — **LC-ABORT-TY**). Anything else is left for the E004 gate.

**Grounded type-check limits (pre-existing, not EH4.2's to fix).** Two `never`-perform forms never reach
the desugar because the type-checker already rejects them, so EH4.2 owes them no support:
`return perform E.op(m)` is **T049** (a `never` value is not assignable to the function's return type), and
a performer whose **only** statement is a tail `perform E.op(m);` with no normal `return` is **T044**
(missing return — the checker does not treat a trailing `never`-perform as divergent). The realistic
abortive shape (`if cond { perform E.op(m); } return ok;`) type-checks and reaches E004, and that is what
EH4.2 lowers. Teaching the checker that a `never`-typed tail diverges is a separate, later enhancement.

#### EH4.2 Strict Constraints (existential)

- **LC-ABORT2 (bare-statement only).** An abortive `perform` is `never`-typed **control flow**, not a
  value. It is rewritten **only** when it is the entire expression of a `TypedStmt::Expr` statement,
  becoming `return $ev_op(args);` in place. *Fail-fast:* an abortive `perform` in any other position (a
  `let` value, a sub-expression, a binary operand, a call argument) is **not** rewritten and is left to the
  E004 gate. Never rewrite an abortive `perform` to an expression (it would be evaluated and **discarded**,
  and execution would wrongly continue). (`return perform …` and a no-return tail `perform …;` are already
  rejected at type-check — T049 / T044 — so they never reach this rewrite.)
- **LC-ABORT-TY (abort-type-match).** The abortive clause body's type must be `type_compatible` with the
  performer's return type `T` (the synthesized closure declares return `T`). *Fail-fast:* a mismatch gates
  (E004) — never synthesize a closure whose body type differs from its declared return (the exact
  invalid-wasm class the EH4.1 sweep found via the unchecked perform-arg).
- **LC-ABORT-COVER (no half-rewrite).** An abortive `perform` left un-rewritten (not in an LC-ABORT2
  position) survives as a `Perform` node. *Fail-fast:* the post-desugar gate
  (`check_effect_handlers_gated`) rejects it with **E004** before `air::lower` — this is the LC-PARTITION
  backstop (the SAME enforcer the whole desugar relies on), not a `performer_plan` pre-check. So a partial
  rewrite is a loud E004, never a silent miscompile; were the gate ever removed, the `never`-typed node
  would instead ICE at `air::lower` (the C-NEVER backstop). The performer's signature may be mutated by
  Pass B even when a sibling `perform` survives, but the gate halts the compile before that matters.
- **LC-ABORT-NEVER (no Never escapes).** `Type::Never` appears only as an abortive op's declared return; it
  must **never** reach `mangle_type`/`lower_type`/a runtime value. The desugar replaces every abortive
  `perform` (the only `Never`-typed node reachable) with a `T`-typed `return`. *Fail-fast:* the existing
  `Type::Never` ICE arms in mangle/lower/runtime (the C-NEVER backstop) fire if one survives.

#### EH4.2 Explicit Anti-Goals (out of scope — gated loud)

- **AG-EH42-1** abortive `perform` in an intermediate callee (propagation) — needs the discriminated-union
  return; that is EH4.3. E004-gated.
- **AG-EH42-2** abortive `perform` in a value position (`let x = perform Fail.raise(m)`, `f(perform ...)`) —
  E004-gated (LC-ABORT2); the lowering would have to prove the continuation dead.
- **AG-EH42-3** an abortive clause body that is not the simple whitelist (a call, a capture, a nested
  handle) — E004-gated, exactly as scoped EH4.1.

#### Deferred hardening (EH4.2 sweep, contained — not a live miscompile)

- **D2 — effect-operation signature types bypass the T066 unknown-type validator.** `universe.rs` resolves
  op param/return types with plain `resolve_type_expr` (no `validate_lowered_type`/T066 pass that function,
  record, and enum signatures get), so `effect E { fn op(p: Bogus) -> Quux; }` records phantom
  `Type::Named("Bogus"/"Quux")`, and a bare `never` in op-PARAM position (vs the handled `-> never` return)
  becomes `Type::Named("never")`. **Contained today:** no phantom value can be constructed and `Type::Never`
  cannot escape — the perform-arg T071 check and the desugar TYPE-match reject any program that would
  exercise these, so it is a clean compile of an *uninstantiable* operation, not a miscompile. **Fix when
  touched:** run op param/return types through the same T066 path as function signatures and reject `never`
  in op-parameter position. Deferred (separable op-decl-validation concern, no live unsoundness).

#### EH4.2 Constraints & Fallbacks (Boring Limit · Fail-Fast)

| ID | Boring Limit | Fail-Fast |
|---|---|---|
| LC-ABORT2 | abortive perform rewritten only as a bare expr-statement → `return $ev(args)` | other positions: not rewritten → E004 gate; never left as an expr-stmt (would discard + continue) |
| LC-ABORT-TY | clause body type `type_compatible` with performer `T` | mismatch → E004 gate (no ill-typed closure) |
| LC-ABORT-COVER | every abortive perform in an LC-ABORT2 position, else whole performer gated | surviving `never` node ICEs at `air::lower` (C-NEVER) |
| LC-ABORT-NEVER | `Never` only as abortive op return; replaced by a `T` return | mangle/lower/runtime `Never` ICE arms |

### EH4.3 — propagation through the call graph (the general lowering)

EH4.0–4.2 require the scrutinee to perform DIRECTLY: every `perform` is a statement in the scrutinee
function itself. EH4.3 lifts this so a handler can wrap a function that performs **indirectly** — via
helper functions it calls. This is the architectural shift from a *per-handle local rewrite* to **evidence
threading through the call graph**, and it is the last EH4 rung (it also removes the multi-module gate and,
once total, the E004 gate + the `air::lower` ICE).

#### The model: evidence flows from each handle down the effectful call subgraph

Call a function an **E-function** if its effect row contains a (handled) user effect `E`. The desugar's
soundness rests on an invariant the effect checker (`effect_check.rs`) already enforces:

> **The leak invariant (E001/discharge).** A `Call` to a callee requires `callee.effects ⊆ caller.effects`
> UNLESS the call is the scrutinee of a `handle` discharging the missing effect (which expands the row for
> the scrutinee only). Therefore **every call to an E-function either sits in another E-function (which can
> forward its own evidence) or is a handle's scrutinee (where the handle builds the evidence).** Evidence
> for `E` is thus available at every call site of an E-function — never missing.

So the transform, per handled user effect `E` (with the per-op flat evidence of EH4.1):

1. **Params.** Every E-function `h` (NON-entry) gains evidence params `$ev$E$op` for **every** operation of
   `E` (in canonical effect-then-op-sorted order, appended after the user params). Uniform — every
   E-function has the identical E-evidence params, so callers always pass the same shape.
2. **Performs.** `perform E.op(args)` in any E-function → scoped `IndirectCall($ev$E$op, args)` / abortive
   `return …` (EH4.3c) exactly as EH4.1/4.2.
3. **Forwarding.** A `Call` to an E-function from inside another E-function → append the caller's own
   `$ev$E$op` params (the matching subset for the callee's effects) as the trailing args.
4. **Source.** A `handle g(args) { E.op => clause }` → build the clause closures for the discharged
   effect(s) and append them to `g(args, …)`. The handle is the evidence *source*; functions on the path
   *forward*. (Pure functions — no effect row — are never touched: **byte-identical AIR** holds for them.)

#### Sub-slices (smallest-first; each green via the gate backstop)

- **EH4.3a — scoped propagation, single effect, intra-module.** The core threading machinery: relax
  "performs directly" to "has `E` in its row"; add evidence params to all E-functions; forward at calls;
  the handle is the source. Scoped only; single effect; abortive-propagation, multi-effect, indirect/closure/
  actor calls all stay E004-gated. Requires plumbing `effect_ops` (operation signatures) into `TypedProgram`
  (it already carries `effect_registry`).
- **EH4.3b — multiple discharged effects.** Relax the single-effect limit; a handle may discharge a subset
  of the scrutinee's effects (the rest propagate to the handle's enclosing function). Evidence is built for
  discharged effects and forwarded for the rest, interleaved in the canonical order.
- **EH4.3c — abortive propagation (the discriminated-union return).** When an abortive `perform` sits in an
  intermediate callee, `return $ev(args)` would return from the *callee*, not unwind to the handle. The
  no-continuation solution is **Result-threading**: an E-function that may abort returns `EhResult<T> =
  Normal(T) | Aborted(payload)`; each call propagates `Aborted`; the handle matches and yields the clause
  value. This is the heaviest transform (every E-function return type + every E-call site changes); it lands
  last and only after a/b prove the threading.
- **EH4.3d — same-ring multi-module + the permanent gate.** Drops the `program.modules.len() != 1` gate and
  makes the scoped + direct-abortive threading **program-wide** (a handler in one module wrapping a performer
  in another, same-ring module — callee names are module-qualified, effect IDs + AIR `function_ids` are
  already program-wide). The original "remove the E004 gate" idea is **withdrawn** — see the EH4.3d subsection.

#### EH4.3d — same-ring multi-module + the permanent gate

Grounding the code corrected the original three-item sketch.

**The E004 gate is PERMANENT (the gate-removal idea is withdrawn).** The desugar is *intentionally
non-total*: it defers ~10 shape categories (multi-module abortive propagation, effectful closures/actors,
generics, nested calls, complex/nested clause bodies, partial coverage, non-tail abortive prop, wrong clause
shape, …), each via a `continue`/`return`. `effect_check::check_effect_handlers_gated` (E004) is LC-PARTITION's
load-bearing net — it turns every deferred shape into a clean **E004** instead of the `air::lower`
`unreachable!()` ICE. The gate (and the `air.rs` ICE arms) are therefore **never removed**; the gate naturally
narrows as the desugar grows, but it always remains while any shape is deferred (**LC-GATE-PERMANENT**).

**Same-ring multi-module (the implementation).** The scoped + direct-abortive analysis (`analyze`) runs ONCE
program-wide over all modules' functions, then the transforms run per-module using it. Synthesized clause
closures + `$EhResult$` enums place + resolve program-wide unchanged. Three gates:

- **LC-MM-RING.** An effect threads only if every E-function of it AND every function containing a handle of
  it share ONE ring. A synthesized clause closure lives in the handle's ring; an `IndirectCall` to it from a
  performer in a different ring would resolve through the wrong per-ring wasm function table (the old EH4-H6
  sweep root). *Fail-fast:* cross-ring → E004 gate (in practice the ring checker's **R004** rejects the
  cross-ring call first; LC-MM-RING is the desugar's own backstop, so its soundness is self-contained).
- **LC-MM-EXPORT-Q (post-sweep ROOT-A).** The abortive-propagation `$eh_unwrap_<H>` helper is a real exported
  `ModuleFunction`; its `export_name` MUST be module-qualified (mirror the function `name`'s `::`→`__`
  mangling), or two same-ring modules each lowering an abortive chain with the same payload `H` both export
  the bare `$eh_unwrap_<H>` → **duplicate wasm export → non-validating module from a clean compile**. *Fail-fast:*
  the qualified export name makes the collision structurally impossible (synthesized enum names dedupe via the
  program-wide `program.enums` map; clause closures are `Closure`-kind, never exported).
- **LC-MM-EHR-XCALL (post-sweep ROOT-B).** `lower_abortive_propagation` stays **per-module**, so it must NOT
  rewrite a chain function reached from another module — that foreign caller is left at the stale signature.
  `ehr_analyze` is given the **program-wide** call counts and gates any effect a chain function of which is
  called from outside its module (`program_all_calls > intra all_calls`). *Fail-fast:* cross-module reach →
  drop the plan → the handler/perform nodes survive to the E004 gate. (The earlier claim that such a chain
  "is undetected and *naturally* falls to E004" was **false**: the gate sees only surviving handler nodes, not
  a stale cross-module `Call` — the explicit count check is what makes the deferral real.)
- **LC-EHR-CHAIN-EXPORT (post-sweep ROOT-B sibling, finding #11).** When the desugar rewrites an abortive
  chain function's ABI (`(..) -> T` → `(.., $ev) -> $EhResult$<H>`), its original public symbol MUST NOT be
  exported with that mutated shape — a `pub fn deep(x: i64) -> i64 ! { Fail }` would otherwise export
  `<module>__deep` as `(i64, $ev) -> $EhResult` (a footgun if anything ever resolves imports by export name).
  The rewrite re-marks the EXPORT name `$`-internal (`$eh_chain$<orig>`) and `wasm.rs` drops every
  `$`-prefixed export. *Fail-fast:* `$` is outside the identifier grammar, so a user export name can never
  start with `$`; only synthesized internals are dropped, and internal call resolution (by `name` via AIR
  `function_ids`) is untouched. Non-effect programs are byte-identical.

**Deferred (gated loud):** **AG-MM-1** cross-ring multi-module (per-ring tables); **AG-MM-2** nested handlers
(re-open cap-injection soundness → EH008); **AG-MM-3** multi-module *abortive propagation* — gated by
LC-MM-EHR-XCALL (a cross-module abortive chain → E004). NOTE: two *independent* single-module abortive chains
in different modules are **supported** (LC-MM-EXPORT-Q lets them coexist); only a chain whose calls *span*
modules is deferred. The single-module path is the N=1 special case and is byte-identical.

#### EH4.3 Strict Constraints (existential — from the harden-spec teardown)

- **LC-THREAD-EXHAUSTIVE.** If the desugar adds evidence params to an E-function `h`, it MUST rewrite
  **every** `Call` to `h` in the program to forward evidence. *Fail-fast:* if any call to `h` cannot be
  rewritten (see LC-THREAD-DIRECT), the entire effect's transform is abandoned and **all** its handler nodes
  are left for the E004 gate — never a mix of rewritten and un-rewritten call sites (that is an arity
  mismatch → invalid wasm).
- **LC-THREAD-DIRECT.** Evidence is forwarded only across a **direct** `Call(name, args)` to a statically
  known E-function. An E-function reached through an `IndirectCall`, a closure value, an actor `send`/`ask`,
  a method/trait-dispatch, or whose address is otherwise taken CANNOT have evidence threaded (its signature
  is fixed by the indirect ABI). *Fail-fast:* such an E-function (and its effect's handlers) → E004 gate.
- **LC-THREAD-EXPORT.** An E-function that is an **entry** (`tool_main`, an actor init/handler, a module
  init, or otherwise exported) MUST NOT receive evidence params (its wasm ABI is fixed — LC-EXPORT).
  *Fail-fast:* an entry with a handled effect in its row → E004 gate (it has no handler anyway; the effect
  would leak).
- **LC-THREAD-PURE.** A function with NO handled effect in its row is **never** given evidence params and is
  **never** rewritten. *Fail-fast:* byte-identical AIR for pure functions is asserted by the unchanged wasm
  snapshots; a pure function gaining a param is a snapshot diff (CI red).
- **LC-THREAD-ORDER.** Every E-function's evidence params and every forwarding call site use the SAME
  canonical order (effects by registry order/name, ops by name). *Fail-fast:* a forwarded arg list whose
  (effect,op) sequence differs from the callee's param sequence is a desugar bug; guarded by a runtime
  differential (a propagated handler computes the same value as the inlined equivalent) and by wasm
  validation (a mis-ordered/mis-typed arg fails to validate).
- **LC-THREAD-GENERIC.** A generic E-function (unresolved type params) is not threaded in EH4.3a–c (the
  monomorphization interaction is out of scope). *Fail-fast:* E004 gate.

#### EH4.3 Explicit Anti-Goals (out of scope — gated loud)

- **AG-EH43-1** effectful **closures / actor handlers** that perform (evidence cannot thread an indirect
  ABI) — E004-gated (LC-THREAD-DIRECT). A future epic.
- **AG-EH43-2** an E-function whose **address is taken** / stored / passed as a value — E004-gated.
- **AG-EH43-3** generic/polymorphic effectful functions — E004-gated (LC-THREAD-GENERIC).
- **AG-EH43-4** mutual recursion or deep call graphs beyond the parser/analysis bounds — bounded by the
  ambient nesting cap; pathological graphs gate rather than loop.

#### EH4.3 Constraints & Fallbacks (Boring Limit · Fail-Fast)

| ID | Boring Limit | Fail-Fast |
|---|---|---|
| LC-THREAD-EXHAUSTIVE | all-or-nothing per effect: every call to a threaded E-function is rewritten, else none | partial rewrite → abandon effect → E004 gate (never arity-mismatched wasm) |
| LC-THREAD-DIRECT | evidence forwarded only across direct `Call` to a static E-function | indirect/closure/actor/method/address-taken E-function → E004 gate |
| LC-THREAD-EXPORT | entries never receive evidence params | entry with a handled effect → E004 gate |
| LC-THREAD-PURE | only E-functions are rewritten | pure-fn param = wasm snapshot diff (CI red) |
| LC-THREAD-ORDER | one canonical (effect,op)-sorted order everywhere | mis-order → wasm validation failure + runtime differential |
| LC-THREAD-GENERIC | no generic E-function threading | generic E-function → E004 gate |

### EH4.3c — abortive propagation via the `EhResult` discriminated-union return

EH4.2/4.3b lower an abortive `perform` to `return $ev(args)` returning the handle type `H` directly. That
works only when the performer IS the scrutinee, because the abortive evidence closure's return type is `H`
(per-handle), not uniform across the call graph — so it cannot thread. When the abortive `perform` sits in
an INTERMEDIATE callee, `return $ev(args)` returns from the callee, not the handle, and the caller's
continuation runs (the sweep miscompile). The no-continuation fix is **Result-threading**.

**Empirically validated** (a hand-written enum + `match` + tail-call chain compiles and runs in SIGIL):
`mid` returning `deep(b)` propagates an `Aborted` payload straight through. The desugar synthesizes the same
shape.

**The model (per PROPAGATING abortive effect — one whose E-functions tail-call each other).** A
non-propagating abortive effect keeps the EH4.2 simple lowering unchanged; this path is ADDITIVE and only
replaces what EH4.3a/b currently gate (abortive forwarding).

- Synthesize ONE concrete enum per handle-type `H`: `enum $EhResult$<H> { Normal(H), Aborted(H) }`,
  registered in `program.enums`. BOTH variants carry `H` — a tail-call chain's functions all share the
  scrutinee's return type (`return h(x)` forces `h`'s return == the caller's), and that type IS the handle
  type `H`. So every chain function's `EhResult` is `EhResult<H,H>`; no generics, no per-function variation.
- Synthesize ONE helper `fn $eh_unwrap_<H>(r: $EhResult$<H>) -> H { match r { Normal(v) => return v,
  Aborted(p) => return p } }`. Because `match` is a STATEMENT in SIGIL (not an expression), the unwrap lives
  in this helper — a plain `Call` that fits ANY expression position (`let r = …`, `return …`, an argument),
  sidestepping the match-is-a-statement blocker.
- Each abortive-effect function `f` (original return `T == H`):
  - return type → `$EhResult$<H>`; gains the abort evidence param `ev: Fn(op_args) -> H`;
  - abortive `perform E.op(args)` (bare statement) → `return $EhResult$::Aborted(ev(args))`;
  - a `return <expr>` whose `<expr>` is a TAIL CALL to an abortive-effect function → `return <call + ev>`
    (the callee's `$EhResult$<H>` propagates by direct return — `Normal` stays `Normal`, `Aborted` stays
    `Aborted` — with NO wrap and NO in-place `match`, which is why a dummy value is never needed);
  - any other `return <expr>` → `return $EhResult$::Normal(<expr>)`.
- The handle `<lhs> = handle g(args) { E.op(b) => clauseval }` → `<lhs> = $eh_unwrap_<H>(g(args, $ev_closure))`,
  where `$ev_closure : Fn(op_args) -> H` is the synthesized clause closure (`body = return clauseval`).

#### EH4.3c Strict Constraints (existential — from the harden-spec teardown)

- **LC-EHR-TAIL.** An abortive-effect function may be reached ONLY by a TAIL call (`return g2(args)`), never
  a `let`-bound, discarded, or nested call. *Fail-fast:* a non-tail call to an abortive-effect function in a
  propagating abortive effect → E004 gate. (A non-tail call would need an in-place `match` whose `Normal`
  arm binds the result — requiring an uninitialized/dummy `let` of an arbitrary type, or a continuation
  split; both are out of scope for this slice.)
- **LC-EHR-RET-UNIFORM.** Every function in the propagation chain has return type `== H` (the handle type).
  This is already forced by `return g2(args)` type-checking (the tail callee's return must equal the
  caller's), but the desugar re-checks it before synthesizing `EhResult<H,H>`. *Fail-fast:* a divergent
  return type → E004 gate (never synthesize an `EhResult` whose variants disagree).
- **LC-EHR-UNIFORM-H.** Every handle that reaches a given abortive-effect function must have the SAME `H`.
  *Fail-fast:* an abortive-effect function reachable from two handles with different scrutinee return types →
  E004 gate (its single `EhResult` return type cannot satisfy both).
- **LC-EHR-PAYLOAD.** `H` must be a representable, sized enum payload type (the same set user enums allow).
  *Fail-fast:* otherwise E004 gate, never a malformed `program.enums` entry.
- **LC-EHR-ADDITIVE.** A NON-propagating abortive effect (no E-function tail-calls another) keeps the EH4.2
  `return $ev` lowering byte-for-byte. *Fail-fast:* the EH4.2 runtime tests stay green (no re-bless); the
  `EhResult` path is entered only when propagation is detected.

#### EH4.3c Explicit Anti-Goals (out of scope — gated loud)

- **AG-EHR-1** a non-tail abortive-effect call (`let x = g2(); …`, `g2();` discarded, `g2() + 1`) — needs a
  dummy-init `let mut` or a continuation split. E004-gated.
- **AG-EHR-2** an abortive-effect function reached from handles with differing `H`. E004-gated.
- **AG-EHR-3** mixing a scoped op and an abortive op of the SAME effect in a PROPAGATION chain — the scoped
  `IndirectCall` interleaving with the `EhResult` return is deferred; the direct-scrutinee mixed case
  (EH4.2) is unaffected. E004-gated for the propagating shape.

#### EH4.3c Constraints & Fallbacks (Boring Limit · Fail-Fast)

| ID | Boring Limit | Fail-Fast |
|---|---|---|
| LC-EHR-TAIL | abortive-effect calls only in `return <call>` position | non-tail call → E004 gate (no dummy/CPS) |
| LC-EHR-RET-UNIFORM | chain functions all return `H` | divergent return → E004 gate |
| LC-EHR-UNIFORM-H | one `H` per abortive-effect function | multi-`H` reach → E004 gate |
| LC-EHR-PAYLOAD | `H` is a valid enum payload type | otherwise E004 gate |
| LC-EHR-ADDITIVE | non-propagating abortive keeps the EH4.2 path | EH4.2 tests green, no re-bless |

## Sub-slices (smallest-first; each green via the gate backstop)

- **EH4.0** — SCOPED, single-operation effect, scrutinee = a direct call to a function whose row is exactly
  that one effect, performing it directly (no propagation). Proves the whole mechanism (evidence param +
  perform→CallIndirect + handle builds the clause closure). A runtime test: `handle f() { Reader.get() =>
  resume 42 }` returns 42.
- **EH4.1** — multi-operation effects. As built, evidence is **one closure parameter per operation**
  (`$ev$E$op`, threaded in sorted-operation order so the performer's added parameters and the handle's
  appended closure arguments agree by construction) rather than a single record of closures — equivalent
  but without new record-type plumbing; the single-op case is the N=1 instance. Adds the **resume-value
  type-match** guard (each clause's resumed value must be `type_compatible` with its operation's return
  type, so `resume 42` for an `-> i64` op is accepted but `resume true` gates). Coverage requires the
  clause set to equal the performed-operation set; with E008 forcing clauses to equal the effect's full
  operation set, the performer must perform every operation of its effect, else it gates (E004).
- **EH4.2** — ABORTIVE clauses (the discriminated-union/early-return propagation).
- **EH4.3** — propagation through intermediate functions + multiple discharged effects + handlers nested in
  handlers; remove the E004 gate and the `air::lower` ICE once nothing un-desugared survives.

## Risks to pin (a focused harden-spec pass precedes implementation)

- **Closure capture of the handler scope** — a clause closure captures its definition-site environment;
  EH008 (borrow-only cap injection) must hold over the synthesized closure (reuse the TS4 walk).
- **Effectful closures / actors** — a user closure or actor handler that performs needs evidence too;
  bound EH4.0 to free functions and gate (E004) closures/actors that perform until a later slice.
- **Evidence threading correctness** — the param order / which evidence goes to which call must match the
  effect rows exactly; a mismatch is a miscompile. Pin with runtime differential tests, and keep the
  `air::lower` ICE as the backstop for any un-desugared node.
- **Monomorphization interaction** — generic effectful functions: defer (gate) until the threading is
  proven on monomorphic functions.

## EH4 Strict Constraints (existential — folded from the harden-spec pass)

These bind the desugar by construction. IDs are `LC-*` (lowering constraint), distinct from the
front-end `C-*` constraints.

- **LC-ABORT** (was MC-2/UP-1). A `perform` of an **abortive** operation has type `Type::Never` (EH3.1).
  It MUST lower as **control flow**, never as a value: the abortive evidence closure returns the abort
  *payload*, and the perform site **early-returns / diverges** (propagating the abort toward the handle).
  The "evidence closure returns the resumed value, perform continues" model is **scoped-only**. *Fail-fast:*
  a `Type::Never`-typed `perform` that reaches a value position ICEs.
- **LC-SCRUT** (was MC-3). The desugar transforms a handle **only** when its scrutinee is *exactly* a
  direct call to a free function; any other scrutinee shape (`f()+1`, a block, a method call, a closure
  call) is left **untouched** and rejected by the post-desugar E004 gate. The per-handle transform is
  **all-or-nothing** — a non-direct-call scrutinee is never partially rewritten. *Fail-fast:* shape
  mismatch → skip (gate fires).
- **LC-CAP** (was MC-4). A synthesized clause closure MUST NOT capture a capability **value** (a borrow is
  fine). Until EH008 lands, a clause body that captures *any* cap-typed value is **gated (E004), not
  desugared** — the compiler's own desugar must not become a cap-smuggle channel. *Fail-fast:* run the TS4
  `type_contains_typestate`-style cap walk over the recovered captures; any cap value → skip-and-gate.
- **LC-ORDER** (was MI-1). Evidence parameters are appended in **one canonical order — sorted by effect id**
  (the `EffectRegistry` u32) — used **identically** at the function definition and at *every* call site. A
  reordering is a silent miscompile (right types, wrong handler). *Fail-fast:* a `debug_assert!` at each
  rewritten call compares the evidence order to the callee's declared order; mismatch panics with the
  function name.
- **LC-EXPORT** (was MI-2). A function with a non-empty `export_name` (entry points / `tool_main`) MUST NOT
  receive an evidence parameter — its wasm ABI is fixed by the host. This holds iff its effects are all
  discharged internally (the effect checker's job). *Fail-fast:* the desugar ICEs if it would add a
  parameter to an exported function (the un-discharged effect should already be E001/E010).
- **LC-THREAD** (was MI-3). Each effectful call site threads **exactly** the callee's declared effect row —
  set-equal, no more, no less — sourced from the caller's own evidence params (propagation) or a handle.
  *Fail-fast:* the desugar ICEs if the provided-evidence set ≠ the callee's row.
- **LC-PHASE** (was UP-2/UP-3). The desugar is **two-phase**: (1) assign every effect-carrying function its
  evidence **signature** (params, in LC-ORDER) from its row; (2) rewrite bodies — `perform`→`CallIndirect`
  on the evidence param, effectful calls get the threaded evidence, handles synthesize clause closures and
  thread them. Closure synthesis runs *post-type-check*: append the new `TypedFunction { kind: Closure }`
  to `module.functions` (so `air::lower`'s `function_ids`, built from `module.functions`, pick it up),
  recover captures by walking the clause `TypedBlock` for free `Local`s (type = each `Local`'s `.ty`), and
  allocate closure ids from a fresh **monotone** counter. *Fail-fast:* phase 2 ICEs if an effectful callee
  lacks its phase-1 signature.
- **LC-PARTITION** (was UP-4). `check_effect_handlers_gated` runs on the **post-desugar** program, and the
  desugar MUST fully remove every node it claims to handle. *Fail-fast:* a `perform`/clause-`handle`/
  `resume` that survives **both** the desugar and the gate reaches `air::lower` and hits the existing
  `unreachable!` — the loud backstop. The gate is the safety net for everything the desugar leaves.

## EH4 Explicit Anti-Goals (out of scope for EH4.0 — each gated *loud*, never silent)

- **AG-EH4-1** — deep handler-in-handler nesting (a clause body that itself installs a `handle`). Beyond
  EH4.0; **E004-gated** until a later slice.
- **AG-EH4-2** — recursion / mutual recursion through an effectful function (propagation territory, EH4.3).
  **E004-gated** until then.
- **AG-EH4-3** — generic (un-monomorphized) effectful functions. The desugar is monomorphic-only;
  monomorphization runs *during* type-check, so concrete instances are fine — any residual generic
  effectful function is **E004-gated**.
- **AG-EH4-4** — effectful **closures** and **actor handlers** that perform. EH4.0 is free-functions-only; a
  `perform` inside a closure or actor body is **E004-gated** until a dedicated slice.

## EH4 Constraints & Fallbacks (Boring Limit · Fail-Fast)

| ID | Boring Limit | Fail-Fast |
|---|---|---|
| LC-ABORT | abortive op returns `Never`; its `perform` desugars to control-flow only | ICE if a `Never`-typed perform reaches a value position |
| LC-SCRUT | desugar matches EXACTLY `handle <direct-call-to-free-fn> { .. }`, else skips | non-direct scrutinee stays E004-gated; never partially rewritten |
| LC-CAP | a clause closure captures 0 cap **values** (borrows ok) | TS4 cap-walk over captures; any cap value → skip-and-gate (E004) |
| LC-ORDER | evidence params sorted by effect id (u32); def == every call site | `debug_assert!` order match per call → panic with fn name |
| LC-EXPORT | an exported/entry function gets 0 evidence params | ICE if a function with `export_name` would gain one |
| LC-THREAD | each effectful call threads exactly the callee's row (set-equal) | ICE if provided-evidence set ≠ callee row |
| LC-PHASE | two phases (sigs, then bodies); closures append to `module.functions`; ids monotone | phase 2 ICEs if a callee lacks its phase-1 signature |
| LC-PARTITION | the gate runs POST-desugar; the desugar fully removes handled nodes | any surviving node → `air::lower` `unreachable!` ICE |

**Ambient backstop:** `check_effect_handlers_gated` (E004) catches everything the desugar does not
transform, and the `air::lower` `unreachable!` catches anything that slips past both — so an incomplete
desugar is always a **loud rejection or ICE, never a silent miscompile**.
