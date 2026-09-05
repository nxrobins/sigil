# RS4 — Rust → SIGIL frontend: refinement preconditions (`#[sigil::requires]`)

Status: **SHIPPED (RS4a/RS4b).** The fifth capability increment of the Rust→SIGIL
frontend, after RS0 (core), RS1 (caps→T199), RS2 (effects→E001), RS3a/b/c (structs, enums, payloads).

## The synergy

Rust has no way to state — let alone *prove* — a function precondition. SIGIL does: a function
parameter may carry a refinement, discharged by the trusted compiler's **Z3** solver. RS4 maps a
Rust attribute to that machinery:

```rust
#[sigil::requires(amount > 0)]
pub fn guarded_draw(amount: i64) -> i64 { amount }
```
→
```
pub fn guarded_draw(amount: i64) where amount > 0 -> i64 { return amount; }
```

The headline: **memory-safe (Rust) ∧ refinement-*proven* (SIGIL Z3)**. Every call site of
`guarded_draw` must *establish* its argument is positive, or the trusted compiler rejects the program:
**T211** when the argument is symbolic with no preserved refinement (the unguarded, non-literal case),
or **T224** when it carries a refinement too weak to subsume the requirement. The untrusted translator
only emits the `where` clause; the proof is SIGIL's.

## Grounding (verified against `origin/main`, not the axis2 worktree)

- **Function-parameter refinements are real and shipped.** `fn f(x: i64) where x > 0 -> i64` compiles
  (`z3_corpus/100_refinement_guards_cap_sink.sigil`, `// expect-ok`). The `where` clause sits between
  `)` and `->` (`parser.rs::parse_optional_param_refinement_where`, "Wall 4 Step 7").
- **The predicate grammar is narrow.** `ast::RefinementClause { field, op, rhs }`,
  `RefinementOp ∈ {Le, Lt, Ge, Gt, Eq, Ne}`, `RefinementRhs = Literal(i64) | <field-ref>`. A clause
  is `<param> <cmp> <int|param>` — linear, no arithmetic.
- **The call-site obligation is Z3-discharged.** Fixture 100 calls `guarded_draw(amount)` only inside
  `if amount > 0 { … }`; the if-guard narrows `amount` so the solver discharges the precondition.
  **Verified empirically:** an unguarded, non-literal argument is rejected with **T211** (*"symbolic
  with no preserved refinement"*), not T224 — T224 is the sibling case where the argument *carries* a
  refinement that fails to subsume the requirement (and also fires on Z3 `Timeout`). The RS4 demo
  exercises the T211 (unguarded-symbolic) path.
- **Refinements do not mix with generics/closures** — **T226** (deferred, "Option B"). RS0–RS3 has no
  generics, so this is moot here.
- **The solver is feature-gated.** Refinement discharge lives behind `--features solver`
  (`z3_fragment_guard.rs`, `z3_*.rs`); C-code/refinement tests must be `cfg(feature = "solver")`.

## The crux: RS4 redefines the acceptance contract (SC-7′)

RS0–RS3 held a **sound-checker** invariant (SC-7): *an accepted input emits zero compiler T-codes* —
the frontend's own checker rejects every ill-typed program, so SIGIL never has to. **RS4 cannot honor
that for refinements**: proving a precondition holds at a call site is exactly what Z3 is for, and the
frontend embeds no solver. So RS4 splits acceptance into two tiers, mirroring RS1/RS2's enforcement
demos:

- **Tier A — accepted & provable (SC-7 preserved).** A `#[sigil::requires]` program whose call-site
  obligations are *dischargeable* (e.g. every call is guarded, or there are no intra-program calls)
  translates and compiles **clean**. These populate the SC-7 accepted-matrix.
- **Tier B — accepted & refuted (the T211 money-shot).** A program that translates fine but whose
  precondition *cannot* be established is **rejected by SIGIL** (T211 for an unguarded symbolic arg;
  T224 for an insufficient one) — the designed outcome, and the enforcement demo (the RS4 analog of
  `enforce_stale_cap_is_t199` / `enforce_effect_leak_is_e001`).

The frontend's guarantee narrows to: **(1) the predicate is well-formed and inside the emittable
fragment, and (2) it is emitted faithfully.** Semantic proof is delegated to the trusted solver. A
T211/T224 is never a frontend bug — it is the frontend working.

## Scope (RS4a)

- One `#[sigil::requires(<clause>)]` attribute per function → one param-`where` clause.
- `<clause>` = `<param> <cmp> <rhs>`, `<cmp> ∈ { < <= > >= == != }`, `<rhs>` = an `i64` literal or
  another parameter of the same function.
- The predicate parses in the RS1 attribute mini-parser (a new `requires` arm), not the general lexer.
- Emit `pub fn f(<params>) where <clause> -> <ret> { … }`.

### Out of RS4a (fail-closed deferrals)
Conjunctions / multiple clauses; arithmetic RHS (`x + 1`); return refinements (`where @ …`);
record-field & variant refinements; `#[sigil::requires]` combined with `#[sigil::cap]` or
`#[sigil::effects]` (cross-feature mode interaction — deferred).

## FE codes (proposed)
- **FE660** — malformed / out-of-fragment refinement predicate (not `<param> <cmp> <int|param>`; an
  unknown operator; arithmetic; a call; a boolean param; more than one clause).
- **FE661** — the predicate references a name that is not a parameter of the annotated function.

## Enforcement demo & tests
- `enforce_unprovable_requires_is_t211`: a fn with `#[sigil::requires(x > 0)]` called with an
  unguarded, non-literal argument → the emitted SIGIL is rejected with **T211** by
  `compile_named_module` (solver-gated).
- Tier-A round-trip + accepted-matrix fixtures (guarded call, or no intra-program call).
- Reject fixtures for FE660 / FE661.

---

# Hardening (harden-spec ritual, 2026-07-07)

## Strict Constraints (negative constraints — MUST / MUST-NOT)

- **SR-1 (fragment allow-list).** An accepted predicate MUST be exactly `<param> <op> <int-literal>`
  where `<op>` is one of the 6 tokens `{ < <= > >= == != }` and `<int-literal>` is a plain decimal
  `i64` (RS0 number rules — no radix/suffix/underscore). The frontend MUST NOT emit any predicate
  token sequence outside that shape. *(kills MC-1: out-of-fragment predicate echoed into the output.)*
- **SR-2 (non-vacuous).** The clause LHS MUST be a parameter identifier; a predicate that references
  **zero** parameters (a literal-only or tautological clause like `1 == 1`) MUST be rejected.
  *(kills MC-2: the silently-vacuous refinement.)*
- **SR-3 (parameter containment).** Every identifier appearing in the predicate MUST be an exact
  string match of one of the annotated function's already-`validate_ident`-checked parameter names.
  The emitted `where` therefore only ever names a validated parameter. *(kills MC-3 / MI-1.)*
- **SR-4 (total predicate parser).** The `requires` predicate parser MUST NOT panic or loop on any
  attribute byte string; every unrecognized token MUST fail-close to FE660. It reuses RS1's total
  mini-lexer and performs a fixed 3-token parse (LHS, op, RHS) with **no recursion**. *(kills MI-2.)*
- **SR-5 (fragment subset, test-pinned).** The frontend's accepted predicate set MUST be a subset of
  SIGIL's Z3 fragment, pinned by a round-trip test that compiles every accepted predicate shape
  **clean** under `--features solver` (zero T-codes) — the refinement analog of SC-7's
  oracle-agreement pin. *(kills MI-3 / UP-3: silent drift between the two crates' fragments.)*
- **SR-6 (honest enforcement demo).** The enforcement demo MUST assert the specific refinement code
  (**T211** for the unguarded-symbolic case the demo uses) **and** that the rejection is genuine — the
  diagnostic message MUST NOT contain `timeout` or a parse-failure marker — paired with a Tier-A
  companion that compiles clean (the `enforce_stale_cap_is_t199` "fresh-clean / violation-rejected"
  structure). *(kills MC-4 / UP-4.)*

## Explicit Anti-Goals (declared out — no fallback owed)

- **AG-1 (param-vs-param RHS).** `#[sigil::requires(x < y)]` is out of RS4a → **FE660**. *Why safe:*
  a fn-param `where` with a parameter RHS is unverified on `origin/main` (only literal-RHS is proven);
  `i < len`-style bounds await RS4b + empirical fragment confirmation. Fails loudly (FE660), never
  silently.
- **AG-2 (multiple clauses / conjunctions).** More than one `#[sigil::requires]` on a function, or a
  conjunction inside one, → **FE660**. RS4a is exactly one clause per function.
- **AG-3 (Tier-A is human-curated).** The frontend makes **no** provability claim. The SC-7
  refinement accepted-matrix is curated *provable-by-construction* (every call syntactically guarded,
  or no intra-program call at all). *Why safe:* a mis-curated "provable" fixture fails the SC-7 test
  **loudly** (a T211/T224 on a Tier-A row), never silently — it reads as a red test, and the fix is to move
  the row to the Tier-B demo. Delegating proof to Z3 is the design, not a gap.
- **AG-4 (mode interaction).** `#[sigil::requires]` on the same function as `#[sigil::cap]` or
  `#[sigil::effects]` is deferred → **FE660** (RS4a is requires-only, inner-ring). *Why safe:* the
  cap-XOR-effect mode split already partitions the file; refinements-in-effect-mode is a separate
  design question.
- **AG-5 (refined generics).** Moot by absence — RS0–RS3 admits no generic functions, so SIGIL's
  T226 (refined-generic) is unreachable. If generics ever land in the frontend, a refined generic MUST
  reject before this anti-goal is retired.
- **AG-6 (return / record / variant refinements).** `where @ …` return refinements and record-field /
  enum-variant refinements are out of RS4a.

## Constraints & Fallbacks (Boring-Limit / Fail-Fast matrix)

| Threat | The Boring Limit | The Fail-Fast Mode |
|--------|------------------|--------------------|
| MC-1 out-of-fragment predicate | Exactly `ident op int` — op ∈ a fixed set of **6** tokens; RHS a plain decimal i64 | **FE660** at the mini-parser, *before* any emit; message names the offending attr text |
| MC-2 vacuous predicate | LHS references **≥ 1** parameter (a literal-only clause is 0) | **FE660** "refinement must constrain a parameter" |
| MC-3 / MI-1 non-param name | LHS is an **exact** string match against the ≤ N param names (one lookup) | **FE661** "refinement references `<name>`, not a parameter of `<fn>`" |
| MI-2 parser totality | Fixed **3-token** parse, no recursion; input already ≤ `MAX_INPUT_BYTES` | Proptest over arbitrary attr bodies asserts no panic/hang; stray token → FE660 |
| MI-3 / UP-3 fragment drift | Accepted set is the finite product **{6 ops} × {i64 literal} × {1 clause}** | Round-trip test compiles every shape clean under `--features solver`; a shrunk Z3 fragment → a **red** Tier-A row |
| MC-4 / UP-4 wrong rejection | Demo asserts **T211** ∧ message ∌ `timeout`/parse-fail, + a clean Tier-A companion | `assert` fails loudly naming the actual diagnostics |
| AG-2 multiple clauses | **≤ 1** `#[sigil::requires]` per function | 2nd attribute → FE660 |

**Ambient backstop.** Every emitted module still passes the FE500 parse self-check before it is
returned; a predicate that (despite the above) produced malformed SIGIL is caught as an emitter bug,
never shipped. The `--features solver` gate means the T211 demo and SR-5 round-trip run on the solver
CI lane, matching `verify-the-way-ci-does`.

## Implementation sketch (RS4a)
- `parser.rs`: extend the attr mini-parser (`parse_attr`) with a `requires` arm → `RsRequire { param,
  op, rhs, span }` on `RsFunction`. Reuse `mini_lex`; add the 6 comparison ops.
- `check.rs`: SR-2/SR-3 (LHS ∈ params, non-vacuous); AG-1/AG-2/AG-4 rejects (FE660/FE661).
- `emit.rs`: emit `pub fn f(<params>) where <param> <op> <lit> -> <ret> { … }` (cap-mode/inner-ring).
- Tests: Tier-A goldens + round-trip (SR-5), `enforce_unprovable_requires_is_t224` (SR-6, solver-gated),
  FE660/FE661 reject fixtures, inline asserts, a totality proptest (SR-4).

---

# RS4b — record invariants (`#[sigil::invariant]`) — SHIPPED 2026-07-08

**The pivot.** RS4b was planned as parameter-RHS fn preconditions (`#[sigil::requires(i < len)]`).
An empirical probe killed it: SIGIL **rejects** any non-literal RHS on a fn `where` with **T224**
(*"function param refinement RHS must be an integer literal … Field / LengthOf RHS deferred per
N5-S7"*). AG-1 was right to fence it — it is not merely unverified, it is unsupported upstream.

**Where the richer refinements actually live: records.** SIGIL fully supports **cross-field record
refinements** — `record Range { lo: i64, hi: i64 } where lo <= hi` compiles, and a construction
violating it is refuted (corpus `25_refinement_pass` / `26_refinement_fail`). RS4b maps a Rust struct
attribute to that:

```rust
#[sigil::invariant(lo <= hi)]
struct Range { lo: i64, hi: i64 }
```
→ `record Range { lo: i64, hi: i64 } where lo <= hi` — enforced at **construction** (build a bad
`Range`, SIGIL refutes it with **T210**).

**What lands.** Attribute collection is centralized into the item-dispatch loop so an attribute may
precede a `struct` as well as a `fn`; a `#[sigil::invariant]` arm in `parse_attr` accepts a literal OR
a cross-field RHS. The checker validates the field(s) are declared `i64` fields (FE661 undeclared,
FE660 non-i64 — mirroring the compiler's T212), and rejects a self-referential clause (`x == x`
vacuous → FE660, mirroring T218). The emitter appends ` where <field> <op> <rhs>` to the record.

**Same SC-7′ two-tier as RS4a.** Tier-A (a satisfiable invariant + a valid construction) compiles
clean; Tier-B (a construction violating the invariant) is refuted with **T210** — the money-shot,
verified by running (`enforce_bad_construction_is_refined`). The SR-5 fragment-pin round-trip is
broadened to every fixture whose emitted SIGIL carries a `where` (RS4a + RS4b).

**Fragment (Boring Limit).** Exactly one clause `<field> <cmp> <field | non-negative i64 literal>`,
`<cmp>` in the 6-op set. Everything else fail-closed (FE660): non-i64 field, self-reference, a
negative RHS, `>1` invariant, or a non-field reference (FE661). `#[sigil::invariant]` on a `fn` (or
cap/effects/requires on a `struct`) → FE660.

**Codes:** reuses FE660 (malformed/out-of-fragment) / FE661 (broadened: a refinement references a
name that is not a parameter *or field*).

## RS4b Explicit Anti-Goals
- **Param-RHS fn preconditions** (`#[sigil::requires(x < y)]`) — **unsupported by SIGIL** (T224,
  literal-only). Not deferred-pending-work; blocked upstream. Retire only if Wall 4 Step 7 gains a
  field RHS.
- **Multiple / conjoined clauses** per struct → FE660 (single clause).
- **Array-length bounds** (`i < len(a)`) — needs SIGIL's `LengthOf` refinement, unwired for the
  frontend; a separate increment.
- **Return refinements** (`where @ …`) and non-i64 refinements — out.
