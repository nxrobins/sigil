# RS5a — Rust → SIGIL frontend: information-flow taint (`#[sigil::taint]`)

Status: **SHIPPED 2026-07-08.** The sixth capability increment of the Rust→SIGIL frontend, after RS0
(core), RS1 (caps→T199), RS2 (effects→E001), RS3a/b/c (structs/enums/payloads/match), RS4a
(`#[sigil::requires]`→refinement, T211) and RS4b (`#[sigil::invariant]`→record refinement, T210).

## The synergy

Rust has no way to declare — let alone *prove* — that a value is confidential. SIGIL does: a 4-level
information-flow lattice (`@Public < @Internal < @Secret < @SecretCT`) enforced **unconditionally** by
the trusted compiler. RS5a maps a Rust attribute onto it:

```rust
#[sigil::taint(s = Secret, ret = Secret)]
pub fn keep(s: i64) -> i64 { s }
```
→ `pub fn keep(s: i64 @Secret) -> i64 @Secret { return s; }`

The headline: **memory-safe (Rust) ∧ non-interfering (SIGIL)**. A `@Secret` value returned where a
`@Public` return is declared, with no `declassify`, is rejected with **T001** — the untrusted
translator emits the `@Label`; the proof is SIGIL's.

**The distinctive win:** taint checking is *always-on* (`compiler.rs:956`, `taint_check::check_taints`,
no `#[cfg(feature="solver")]`). So RS5a's enforcement demo (`enforce_taint_leak_is_t001`) is the first
`enforce_*` demo that fires on the **default feature set** — no `--features solver` lane, unlike RS4a/b.

## Grounding (verified on origin/main)

- Taint is a `@Label` type qualifier on params / lets / return types
  (`fn f(s: i64 @Secret) -> i64 @Public`). Levels `@Public < @Internal < @Secret < @SecretCT`;
  unannotated default = `@Public`. Return taint parses after the return type, before any `where`.
- Flow rule `can_flow_to = self ≤ target`; a downgrade with no `declassify` → **T001** at sinks:
  let-assignment, **return (`taint_check.rs:325`)**, actor send/ask. The checker is flow-sensitive — a
  value's actual taint is computed from the body (lub), so a "declared-but-not-flowed" secret is safe.
- **Probed (SR-T11):** `fn leak(s: i64 @Secret) -> i64 { return s; }` → T001; `Secret→Secret`,
  `Internal`-param/`Public`-return-not-flowed, and `bool @Secret` all compile clean — all on default
  features.

## Design (RS5a)

**Surface — fn-level attribute** (per-param attrs can't anchor the *return* taint, forcing a strictly
larger hybrid): `#[sigil::taint(<target> = <Level>, …)]`, `<target>` a parameter name or `ret`,
`<Level>` ∈ `{Public, Internal, Secret}`. Reuses the `collect_attrs`/`parse_attr`/`mini_lex` spine.

**SC-7′ two-tier** (the frontend cannot itself prove non-interference — SIGIL's always-on `taint_check`
does): **Tier A** (no illegal downgrade) compiles clean; **Tier B** (a `Secret` param → default
`@Public` return) → **T001**, the money-shot. The frontend's guarantee: *the annotation is well-formed
+ in the {Public,Internal,Secret}×{param,ret} fragment + faithfully emitted*, with **zero** flow
analysis (delegated to `taint_check`).

## Strict constraints (harden-spec, 2 passes)

- **SR-T1 (fragment allow-list).** `<target> = <Level>` clauses only; `<Level>` ∈ the fixed 3-set;
  anything else → **FE670** at parse. `SecretCT` gets a distinct FE670 message.
- **SR-T2 (target is a real param).** A non-`ret` target must be a validated param, else **FE671**.
- **SR-T3 (single attribute, distinct targets).** ≤ 1 `#[sigil::taint]` per fn; a duplicate target →
  FE670 — never merge/last-wins (a silently-untainted secret is the cardinal failure).
- **SR-T4 (total mini-parser).** A `never_panics_on_arbitrary_taint_attr` proptest pins totality.
- **SR-T5 (honest default-feature demo).** `enforce_taint_leak_is_t001` asserts `code == "T001"` +
  the Tier-A companion compiling clean — NO solver gate.
- **SR-T6 (non-vacuous matrix).** Each taint accepted-matrix row emits ≥1 `@Level` AND compiles clean.
- **SR-T7 (no default-label churn).** A non-targeted param/return emits **no** suffix; the unchanged
  RS0–RS4b goldens are the byte-identity regression guard.
- **SR-T8 (case-exact levels).** `TaintLevel::as_str` emits exactly `Public`/`Internal`/`Secret`
  (SIGIL's parser is case-sensitive); a mismatch → FE500 + a red `round_trip`.
- **SR-T9 (fragment-subset pin).** `round_trip_compiles` on the taint goldens pins the emitted
  `@Label` syntax ⊆ what `taint_check` accepts (the always-on analog of RS4a's SR-5).
- **SR-T10 (scalar-only, enforced).** A taint target's param/return type must be `i64`/`bool`;
  a struct/enum-typed target → **FE670** (`@Label` was only ever observed on scalars).
- **SR-T11 (verify the code by running).** The demo's `T001` was confirmed by compiling the exact
  emitted program before hard-coding it (the RS4a T224→T211 discipline).

## Explicit anti-goals (declared out, fail-closed)

- **AG-T1 `@SecretCT` / constant-time** — deferred (T020–T032 + a second return-sink T030); `SecretCT`
  as a level → FE670.
- **AG-T2 `declassify` / `declassify_ct`** — RS5b; needs the linear `Cap<Declassify>` + O001. Without
  it, RS5a Tier-A is upward-flow only (still useful: leak-proofing).
- **AG-T3 no frontend flow analysis** — labels emitted verbatim; `taint_check` is the sole flow oracle.
  *Corollary:* Tier-A accepted-matrix rows are human-curated-clean; a mis-curation fails **loudly** as a
  T001 red on `round_trip`, never silently.
- **AG-T4 explicit local (`let`) taint** — locals get inferred taint (lub); no annotation surface.
- **AG-T5 per-field record taint** — the compiler supports it, but RS5a is scalar params/returns only.
- **AG-T6 a parameter named `ret`** — not taint-targetable (`ret` is the return keyword).
- **AG-T7 mode interaction** — `#[sigil::taint]` on the same file as cap/effects/requires/invariant →
  FE670; on a struct/enum → FE670 (fn-only).

## Codes
**FE670** (malformed / out-of-fragment / SecretCT / duplicate / non-scalar / mode-mix / taint-on-item)
and **FE671** (target is neither `ret` nor a parameter).

## Tests
2 golden pairs are 4 fixtures (`taint_upward`, `taint_levels`, `taint_public_ret`, `taint_bool`) —
byte-exact + round-trip; `enforce_taint_leak_is_t001` (default-feature); 9 reject fixtures; 8 inline
asserts (incl. the per-level `@Label` emit shape); 3 accepted-matrix rows; a totality proptest.

## Follow-ons
RS5b: `declassify` (the linear `Cap<Declassify>` escape hatch). RS5c: `@SecretCT` + constant-time.
Per-field record taint.
