# RS5b — Rust → SIGIL frontend: `declassify` (the linear escape hatch)

Status: **SHIPPED 2026-07-08.** The seventh capability increment of the Rust→SIGIL frontend, after RS0
(core), RS1 (caps→T199), RS2 (effects→E001), RS3a/b/c (structs/enums/payloads/match), RS4a
(`#[sigil::requires]`→T211), RS4b (`#[sigil::invariant]`→T210) and RS5a (`#[sigil::taint]`→`@Label`→T001).

## The synergy

RS5a made the information-flow lattice *leak-proof* — a `@Secret` value returned where `@Public` is
declared is **T001**. But leak-proof with no escape hatch means a value computed from a secret is stuck
at `@Secret` forever. SIGIL's answer is `declassify(value, cap)`: it lowers any non-CT taint to
`@Public`, **consuming a linear `Cap<Declassify>`** so a declassification is an explicit, auditable,
un-forgeable, *use-once* event. RS5b maps a Rust surface onto it:

```rust
#[sigil::taint(s = Secret)]
pub fn reveal(s: i64) -> i64 { declassify(s) }
```
→
```
module reveal;
cap type Declassify {}
pub fn reveal(s: i64 @Secret, __fe_declassify_cap_0: Declassify) -> i64 {
  return declassify(s, __fe_declassify_cap_0);
}
```

The headline: **the escape hatch works** — the exact program that was T001 in RS5a now compiles clean,
*because* of `declassify`. The untrusted frontend synthesizes the linear cap; SIGIL proves the flow.
Like RS5a, this is a **default-feature** result (both `taint_check` and `ownership::verify` are
always-on — no `--features solver`).

## Grounding (verified on origin/main + probed with the real compiler)

- `declassify(value, cap)` is a reserved-keyword expression (`parser.rs:4572`) lowering a non-CT value
  to `@Public` (`taint_check.rs:758`). The cap is `cap type Declassify {}` — an **empty** cap type —
  received as a fn parameter. It is **linear**: reuse → **O001** (the F002 finding,
  `[[declassify-cap-not-consumed-F002]]`). An **unused** Declassify cap is silently accepted (the RS1
  FE011 lesson), so the frontend must guarantee every provisioned cap is consumed.
- The frontend lexes `declassify` as a normal `Ident`, so `declassify(x)` parses as a `Call` it
  intercepts. `is_sigil_keyword("declassify")` is `true`, so `declassify` as any emitted identifier is
  already FE620 (a free SC-2 guard).
- **Probed (SR-T11, 9 programs):** single `declassify` → CLEAN; two declassifies one cap → O001; leak
  w/o declassify → T001; unused cap → CLEAN (not flagged); two declassifies two caps → CLEAN;
  declassify `a`, return `b` → T001; intra-program call to a synthetic-param fn → T070.

## Design (RS5b)

**Surface — a recognized `declassify(value)` builtin call** (not an attribute — declassify is an
*operation* on a value at a point). Arity exactly 1; the linear cap is entirely frontend-synthesized
(AG-B6 — the Rust subset has no cap values). Rides taint-mode (inner ring); the `@Secret` comes from
RS5a's `#[sigil::taint]`.

**Provisioning — one synthetic `Declassify` cap PER declassify CALL** (the *faithful* choice: N
independent declassifies → N caps → all clean; the "one cap per fn" route would inject an O001 into a
legitimate 2-declassify program — AG-B2). `cap type Declassify {}` is emitted once. The parser assigns
each call a stable per-fn index `k` (a `Parser::declassify_idx` counter → `RsFunction::n_declassify`),
keeping `emit_expr` stateless; the emitter appends `__fe_declassify_cap_k: Declassify` params and
lowers the k-th call to `declassify(<value>, __fe_declassify_cap_k)`.

**SC-7′ two-tier** (the frontend cannot itself prove non-interference): **Tier A** — a `declassify`
that lowers a `@Secret` to the declared `@Public` return → clean (the escape hatch). **Tier B — the
money-shot** — declassify is *precise*: declassify `a` but return a still-`@Secret` `b` → **T001**. The
frontend guarantee: *the call is well-formed (arity 1, scalar arg) + faithfully lowered with a fresh
linear cap per call*, zero flow analysis (`taint_check` + `ownership::verify` are the oracles).

## Strict constraints (harden-spec)

- **SR-B1 (exact arity).** `declassify` takes exactly 1 argument; else **FE672** at parse.
- **SR-B2 (scalar-only arg, enforced).** The argument type must be `i64`/`bool`; else **FE672** in
  `check` (the RS5a SR-T10 rule; `@Label` was only ever observed on scalars).
- **SR-B3 (exact builtin name).** Recognize exactly `declassify`; `declassify_ct(...)` → **FE672**
  (RS5c), never silently treated as `declassify`.
- **SR-B4 (one linear cap per call, bijective).** #synthetic-caps == #declassify-calls per fn, each
  cap used once. A mismatch → the FE500 self-check + an FE011 decorative-cap assert (never an O001
  shipped as a policy verdict).
- **SR-B5 (declassify-bearing fn is a leaf).** A fn containing a `declassify` has synthetic cap params
  an in-subset call can't supply, so a call to it → **FE040** (the RS1 cap-callee gate, extended),
  before emit (otherwise a SIGIL arity error T070 leaks through).
- **SR-B6 (mode exclusivity).** `declassify` + cap/effects/requires/invariant → **FE672** (the RS5a
  AG-T7 gate, extended). `declassify` + `#[sigil::taint]` is the intended pairing and is allowed.
- **SR-B7 (honest default-feature demo).** `enforce_declassify_is_precise_t001` asserts `code ==
  "T001"` (verified by running); `enforce_declassify_makes_leak_clean` shows the T001→clean dual. No
  solver gate.
- **SR-B8 (non-vacuous matrix).** Each `declassify` matrix row does a real `@Secret → @Public`.
- **SR-B9 (no golden churn).** A program with no `declassify` emits byte-identically to RS5a.
- **SR-B10 (total recognition walk).** The count/leaf-check walk every expression position (SR-B10);
  a `never_panics_on_arbitrary_declassify` proptest pins totality.

## Explicit anti-goals (declared out, fail-closed)

- **AG-B1 `declassify_ct` / `@SecretCT`** — RS5c; a `declassify_ct(...)` call → FE672.
- **AG-B2 one-cap-per-fn (the O001 route)** — NOT chosen; per-call provisioning is faithful. The O001
  linear-reuse property is real (F002) but exercised at the SIGIL layer, not via under-provisioning.
- **AG-B3 non-scalar / record-field declassify** — scalar `i64`/`bool` only (SR-B2).
- **AG-B4 declassify-bearing fns as call targets** — a declassify fn is a leaf boundary (SR-B5).
- **AG-B5 `declassify` as an identifier** — already FE620 (`is_sigil_keyword` = true).
- **AG-B6 explicit cap in the Rust surface** — the cap is entirely frontend-synthesized.

## Codes
**FE672** (malformed / out-of-fragment `declassify`: arity, non-scalar, `declassify_ct`, mode-mix).
**FE040** is reused (SR-B5, the RS1 cap-callee gate). The linear cap itself is re-checked by
`ownership::verify` (O001 on reuse).

## Tests
4 golden pairs (`declassify_reveal`, `declassify_two`, `declassify_bool`, `declassify_expr`) byte-exact
+ round-trip; `enforce_declassify_makes_leak_clean` + `enforce_declassify_is_precise_t001`
(default-feature); 6 reject fixtures (FE672×5 + FE040×1); conformance-inline asserts incl. the emit
shape; 3 accepted-matrix rows; a totality proptest.

## Follow-ons
RS5c: `declassify_ct` + `@SecretCT` + the constant-time surface (T020–T032). Real `Cap<Declassify>`
values in the Rust surface (threaded through calls, retiring the SR-B5 leaf limit). Per-field record
taint + declassify.
