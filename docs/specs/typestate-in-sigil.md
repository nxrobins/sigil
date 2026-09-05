# Typestate (Protocol States in the Type) in SIGIL — Design

**Status:** TS0 (repr + parse + resolve) + TS1 (transition checking T266 + the mint T269) + TS2 (affine
consumption — a typestate value is `AirValueKind::Linear`, so the existing `ownership.rs` move-checker
fires **O001** on use-after-revoke / use-after-transfer) + TS3 (state-polymorphic ops — `fn op<@S>(f:
File<S>)` is generic over the state: a state-position arg that is an in-scope `@S` binder resolves to
`Type::Generic` and binds at the call site via the generic unify/subst channel, while state args are
dropped from the mono key so a state-poly fn collapses to ONE erased instance) + TS4 (affinity-smuggle
hardening — a typestate value may not be stored in an aggregate: record field / enum payload / array /
generic-aggregate are **T275**, closing the ST-6 vector where stashing a handle and extracting it twice
mints two from one and defeats O001; `type_contains_typestate` mirrors the cap-defense walker
T183/T184/T186/T242 arm-for-arm. A post-ship adversarial sweep found two MORE channels, both closed:
(a) an **actor state field** (T275 — the actor could take it out across handler calls; caps are allowed
there, typestate is not), and (b) a **closure capture** — a closure capturing an affine typestate value
is now itself Linear (lambda-lift copies the handle into the heap `__env`), so it cannot bind to a
non-linear `Fn` type or be called twice; the sanctioned channel is to pass the value as a closure
PARAMETER, exactly as for caps) **Implemented**; TS5 planned (transition tables T267). Epic 1 of
"lightweight dependent types" (the value-indexed bounds-refinement sibling is a later epic). The
whole-program strip pass + T268 residual gate are deferred — the lazy state-blind erasure (state-blind
`mangle_type` + `lower_type` ignoring `Named` args + the value-walker ICE backstops) covers it, proven by
the byte-identical-AIR gate, exactly as HKT deferred its EX-4 clean residual gate. TS2 keys affinity on
the `StateMarker` arg itself (no `typestate_nominals` threading); `AirValueKind` drives only the
ownership/capability verifiers, never wasm codegen, so the byte-identical gate is undisturbed.
**Scope:** the trusted (Rust) compiler. Self-hosted parity (`selfhost/typecheck.sigil`) is a deferred
follow-on (AG-TS-3).

This spec was produced through the project's adversarial-hardening ritual: Adversarial-Compiler teardown
→ Existential/Academic triage (code-grounded findings, each flip-tested) → Constraint Matrix (§8, Boring
Limit + Fail-Fast). It mirrors the structure of [hkt-in-sigil.md](hkt-in-sigil.md) and adopts the
normative format of [u256-refinements-soundness.md](u256-refinements-soundness.md).

---

## 1. Context & Goal

SIGIL has refinement predicates (Wall 4: `where field <op> rhs`, Z3-discharged). The next step in
expressiveness *and* security is **lightweight dependent types** — types that depend on values — to
**encode protocol states in the type system and make invalid states unrepresentable**, with the safety
discharged at compile time: *the proof IS the type, no runtime check.*

A protocol state lives in the value's **type**. A file handle is `File<Open>` or `File<Closed>`; an
operation that requires the `Open` state cannot be called on a `Closed` one, and an operation that
*consumes* a handle (a transition) leaves the old binding dead. No sequence of well-typed operations can
reach an invalid state.

```sigil
state File { Open, Closed }          // closed set of zero-size markers
record File<@S> { fd: i64 }          // @S = state-kinded type parameter

fn open(p: str)         -> File<Open>
fn read(f: &File<Open>) -> i64        // requires Open, borrow (non-consuming)
fn close(f: File<Open>) -> File<Closed>   // requires Open, produces Closed, CONSUMES

let f = open("/x");
let f = close(f);     // f rebinds to File<Closed>
read(&f);             // ✗ T266: read requires Open, f is Closed   (and O001 if not rebound)
```

Typestate is **purely type-level**; it **erases before AIR** and adds **zero security surface** (§3, §7).
The worst failure mode is *over-rejection*, never a memory-safety hole — the property that made it the
chosen first cut over bounds-refinement (whose payoff is *deleting* a runtime trap).

## 2. The oracle

The trusted compiler is the source of truth. The relevant pipeline (`compiler.rs`):
`name_resolution::resolve` → `typecheck`/`check_with_warnings` (monomorphization is **eager and
interleaved inside type-check**) → `ring_check` → `effect_check` → `taint_check` → `air::lower` →
`capability::verify` → `ownership::verify`. Two existing engines are reused wholesale:

- **`ownership.rs`** — a complete affine move-checker: `MoveKind` (11 consumption sites: `Call`, `Send`,
  `Ask`, `Restrict`, `Split`, `RecordField`, `Reassign`, …), `apply_moves` / `check_uses`, emitting
  **O001 use-after-move** and **O007 move-while-borrowed**. Typestate affinity is a new *client* of this
  engine, not a new engine.
- **caps** (`type_check/capability_tc.rs`) — `restrict`/`split`/`draw` change a `Cap(name, Vec<i64>)`'s
  authority while the value persists (weak typestate); `infer_cap_restrict_expr` is the transition
  template.

## 3. SIGIL representation — the erasure thesis (NOT HKT-style)

A protocol state is a **phantom type argument** on a nominal: `File<Open>` is
`Type::Named("File", [Type::StateMarker("Open")])`. This reuses the entire (complete) generics machinery —
`apply_subst` recurses `Named` args, `unify_inner` zip-unifies them, `type_compatible` compares them
**positionally and invariantly** (resolve.rs:1434), which is exactly the "no subtyping between distinct
states" rule we want.

One new `Type` variant (type_check/types.rs) — a **distinct** variant (not a nullary `Named` / a `Generic`
payload), so the exhaustiveness checker flags every walker that forgot an arm:

| Variant | Meaning |
|---|---|
| `StateMarker(String)` | a zero-size protocol-state token (`Open`, `Closed`, `Live`, `Revoked`); appears **only** as a phantom `Named` arg, never as a value type |

The distinct variant is load-bearing, not decorative: it is what lets the **checking-walkers**
(`type_compatible`/`unify_inner`/`apply_subst`) compare/bind state markers while the **value-position
walkers** (`lower_type`/`mangle_type`/`classify_value_kind`) reject them (§8 ST-3), and what carries the
per-nominal linearity (ST-2) and closed-set (ST-5).

**The erasure is NOT HKT-style.** HKT's `HktApp` erases to a `Named` with *real* args that *do* drive
monomorphization. State args must be load-bearing for *checking* yet **invisible to every layout/identity
computation**: `mangle_type` (air.rs:1118) flattens `Named("File",[Open])` → `File__Open` and
`build_field_registry` (air.rs:752) keys per-instantiation on that mangled name — both run *at*
monomorphization, *before* any post-typecheck strip. So a single projection `strip_state_args(ty)` is the
sole source of truth, applied at (a) the eager-mono mangle/instance key, (b) before `build_field_registry`,
(c) `air::lower`; and `mangle_type` is made **state-blind**. A typestate program and its
`<@S>`-textually-removed twin then produce an *identical* set of mono instances, field-registry keys,
`AirType`s, and wasm bytes (§8 ST-1). A whole-program `assert_no_residual_state` gate emits **T268** before
the soundness passes if any `StateMarker` survives (primary defense); ICE arms in the value-position
walkers are the backstop.

Surface syntax: a `state N { A, B }` item (the closed marker set; new lexer keyword `state`), and a
state-kinded binder `@S`. `ast::ParamKind` (already `{ Star, Constructor{arity} }` from HKT) gains `State`;
`ast::state_params` projects the state-kinded subset, beside `hkt_params`. `@` is already a lexer token.

### Transitions and minting

The **required input state IS the parameter/receiver type**; the **produced output state IS the return
type**. No new transition syntax: `close(f: File<Open>) -> File<Closed>` *is* the transition. A wrong-state
call is an invariant `Named`-arg mismatch routed to a dedicated **T266**. The output state threads to the
binding by ordinary let-rebinding (`let f = close(f)` rebinds `f: File<Closed>` — `check_let` already does
this).

`record File<@S>` has no field of type `S` (`@S` is *phantom*), and `RecordConstructExpr` (ast.rs:1109)
has **no type-arg slot** (so `File<Open>{..}` does not parse). The **mint rule** (ST-4): a bare
`File { fd: 1 }` infers its phantom state from the **expected type** (return ascription / let-annotation /
call-arg) — reusing the generics epic's return-type-directed inference, no new syntax. An unpinnable
phantom state is a hard **T269**, never defaulted.

### Affine consumption (the security half)

A typestate-protocol nominal classifies as `AirValueKind::Linear` (via the per-nominal `typestate_nominals`
flag, which survives stripping — ST-2), so the existing `ownership.rs` move-checker fires: a by-value
(consuming) `close(f)` is a `MoveKind::Call`, and a second use of `f` is **O001 use-after-move**. A revoked
or transferred handle is thus unusable **whether or not** the author rebinds: wrong-state path → T266
(pre-strip, type-check); stale-binding path → O001 (post-strip, AIR). This makes the kernel-doc S1
(use-after-revoke) and S2 (use-after-transfer) compile errors with no new ownership code.

## 4. The differential harness

Deferred (AG-TS-3). The Rust↔SIGIL `typecheck_differential` drift-locked `type_tag` map assigns
`StateMarker` the next free tag so it compiles, but — because the variant is check-time-only and erases
before any emitted typed-node stream — no typestate fixture appears in the differential corpus until the
self-hosted twin learns the states.

## 5. The PR ladder

Each rung is independently green (`cargo test --workspace`, `clippy -D`, `fmt`). Diagnostic codes
(confirm `diagnostics/codes.rs` ceiling at impl; reported T265, with T270/T272/T273 reserved by HKT):
**T266** wrong-state op · **T267** illegal declared transition · **T268** residual-state gate · **T269**
unpinnable / fabricated state at construction · **T274** cross-actor state-laundering · **T275** typestate
stored in a long-lived place. Parser **P028**. Ownership reuses **O001**/**O007**.

- **TS0 — repr + parse + resolve (no-op).** `Type::StateMarker`; `ParamKind::State` + `state_params`;
  `state` item + lexer keyword; `@S` binder parse (P028 malformed / marker-in-value-position);
  `resolve_type_expr_kinded` state resolution + closed-state-set registry (ST-5) + `typestate_nominals`
  (ST-2). **Walker arms SPLIT (ST-3):** real `StateMarker` arms in `type_compatible`/`unify_inner`/
  `apply_subst` (`(a,b)=>a==b` / bind / substitute) + `render_type`; ICE arms in `lower_type` /
  state-blind `mangle_type` / `classify_value_kind` (post-strip only). `strip_state_args` projection.
  Differential `type_tag` new tag. **Done-line:** declare-but-don't-operate parses/resolves/type-checks;
  AIR **byte-identical to the `<@S>`-stripped twin** (ST-1).
- **TS1 — transition checking + erasure pass.** Wrong-state call/method → **T266** (`infer_call_expr` /
  `infer_method_call_expr`, via `try_state_mismatch_diagnostic`); `strip_typestate` rewrites stated
  nominals before ring/effect/taint; `assert_no_residual_state` → **T268**; mint rule (ST-4) → **T269**.
  **Done-line:** the 3-state file protocol accepts the legal sequence, rejects `read` after `close`
  (T266); AIR sees one stripped `File`. *(Affinity not yet.)*
- **TS2 — affine consumption (the security rung).** `classify_value_kind` consults `typestate_nominals` →
  `Linear`; `ownership.rs` then fires **O001** (use-after-transition) and **O007** (move-while-borrowed);
  FnOnce propagation falls out. **Done-line:** kernel-doc **S1** / **S2** are compile errors, proven by an
  execution/AIR-validated fixture (not compile-only).
- **TS3 — state-polymorphic ops + transition tables.** `unify_inner`/`apply_subst` bind `@S` from the
  call-site state arg; optional `transitions { Open -> Closed via close }` table → an op whose declared
  `produces` is not a legal successor of `requires` is **T267** at *declaration* time. **Done-line:**
  state-poly ops monomorphize+erase; an illegal declared transition is rejected at decl.
- **TS4 — invalid-state hardening.** **T274** (state arg may not cross `send`/`ask`/`spawn` unless
  re-stated — `validate_dispatch_args`), defense-in-depth `StateMarker` arms in `type_contains_cap` (the
  walker-bug class), **T275** (`type_is_reassignable` bars typestate in a long-lived field / reassignment
  target — collapses cross-block aliasing to the proven linear-cap surface). **Done-line:** fabrication,
  resurrection, smuggling, cross-boundary laundering all rejected.
- **TS5 (deferred, AG-TS-3) — self-hosted parity.**

## 6. Reference scenarios (acceptance corpus)

From `docs/kernel-primitives-evolution-spec.md`, each must compile-error at the predicted site:

- **S1 — use-after-revoke.** `revoke(g: Grant<Active>) -> Grant<Revoked>` (consuming); `access(&Grant<Active>)`.
  `revoke(g); access(&g)` → O001 (g consumed) or T266 (g is Revoked) if rebound.
- **S2 — use-after-transfer.** `transfer(c: Capability<Live>, to) -> Capability<Transferred>`; the caller's
  `c` is moved (`MoveKind::Call`/`Send`); a later `use_cap(c)` → O001.

## 7. Security surface

Zero. Typestate is type-level and erases before AIR (ST-1). Every soundness pass (ring/effect/taint/
capability/region/Z3) sees only the post-strip concrete `TypedProgram`. The affine guarantee rides the
existing `ownership.rs` pass; no new AIR node, no wasm, no runtime cost.

---

## 8. Constraints & Fallbacks (the hardened Constraint Matrix)

Grounded in the real walker code. Mantra: dumb physical bound + loud failure. Every Boring Limit is a
strict negative constraint; every Fail-Fast names the exact mechanism.

| # | Threat | The Boring Limit | The Fail-Fast Mode |
|---|---|---|---|
| **ST-1** | State args reach mono/mangle/field-registry → duplicate `File__Open`/`File__Closed` instances; "byte-identical" gamed by re-accepting a bloated snapshot | ONE projection `strip_state_args(ty)` is the sole source of truth, applied at (a) the eager-mono mangle/instance key, (b) before `build_field_registry` (air.rs:706), (c) `air::lower`. `mangle_type` is **state-blind**. A typestate program and its `<@S>`-textually-removed twin yield an *identical* set of mono instances + field-registry keys + wasm bytes. | CI compiles the stated program and its hand-stripped twin and asserts **byte-identical AIR/WAT** (vs the TWIN, never a re-accepted snapshot). A `StateMarker` reaching `mangle_type`/`lower_type`/`build_field_registry` is `panic!("ICE")` — never a silent `File__Open` key. |
| **ST-2** | Typestate value defaults to `AirValueKind::Copy` (air.rs:5181) → affine tracking silently absent → use-after-transfer never caught | A `typestate_nominals: HashSet<String>` recorded at universe-build; the value-kind classifier consults it and returns `Linear` for any member, regardless of stripped args. No path classifies a typestate nominal `Copy`. | An execution fixture (`wasmtime::Module::new`-validated) does a use-after-transition and asserts **O001 fires**; a `Copy` misclassification makes O001 silent → fixture fails (vacuity guard). `typestate_nominals` MUST be non-empty whenever a `state` decl exists. |
| **ST-3** | ICE-everywhere breaks reflexivity → `type_compatible(File<Open>,File<Open>)` crashes/rejects → *every correct* program dies; or reject-everything passes a reject-only suite | Walker discipline SPLIT: `type_compatible`/`unify_inner`/`apply_subst` get **real** `StateMarker` arms (`(a,b)=>a==b` / bind / substitute); ICE arms ONLY in value-position walkers (`lower_type`, state-blind `mangle_type`, `classify_value_kind`), firing only post-strip. | A happy-path **accept** fixture (`read(&f)` on a correct `File<Open>` compiles) is required green *alongside* the T266 reject fixture — a reject-everything regression turns the accept fixture red. |
| **ST-4** | No mechanism mints a stated value; phantom `@S` is uninferable and `File<Open>{..}` doesn't parse | A typestate construction's phantom state is bound by exactly one source — the **expected type** (return ascription / let-annotation / call-arg). No default-to-first-state arm exists. | `let f = File { fd: 1 };` with no expected type → **T269** (unpinnable state) at the construct site, before mono. Pinned by a reject fixture + an accept fixture (`fn open()->File<Open>{ File{fd:1} }`). |
| **ST-5** | Undeclared marker `File<Banana>` silently admits an open-ended state space | A per-protocol `HashMap<nominal, HashSet<state>>` closed at the `state N {…}` decl; `File<X>` resolves only if `X` ∈ `File`'s declared states. | `File<Banana>` → **P028 / resolve T-code**; never resolved to a fresh nominal `Banana`. |
| **ST-6** | Aliasing defeats affinity → stale typestate after a transition (`let g=f; close(f); read(g)`; smuggle into field/closure/Vec/Tuple) | A typestate value is **non-storable** in a record field / closure capture / Vec/Tuple element / actor message in the transition rungs — the cap-smuggling walkers (`type_contains_cap`, `is_send_type`, `type_is_reassignable`) gain typestate arms **including the Tuple/Fn arms** the walker-bug memo proved load-bearing; a consuming move with a live borrow is caught. | Store in a long-lived place → **T275**; second use after move → **O001**; move-while-borrowed → **O007**. All loud; worst case over-rejection, never a stale alias. |

**Ambient backstop:** the always-on `assert_no_residual_state` whole-program walk (**T268**) runs before
ring/effect/taint and traps any `StateMarker` residual the specific bounds miss — a process-visible reject,
never a silent `AirType::Ptr`.

### Strict negative constraints (the load-bearing MUSTs)

- **NC-1 (single erasure projection).** Exactly one `strip_state_args` is the source of truth for removing
  state args; it is applied at the mono key, before `build_field_registry`, and at `air::lower`.
  `mangle_type` is state-blind. (ST-1)
- **NC-2 (linearity totality).** Every `state`/`record N<@S>` nominal is in `typestate_nominals`;
  `classify_value_kind` returns `Linear` for every member. No typestate nominal classifies `Copy`. (ST-2)
- **NC-3 (walker split).** `StateMarker` has *real* arms in `type_compatible`/`unify_inner`/`apply_subst`/
  `render_type`; it ICEs *only* in `lower_type`/`mangle_type`/`classify_value_kind`, *only* post-strip. (ST-3)
- **NC-4 (one mint source).** A phantom state is bound only by the expected type; an unpinnable state is a
  T269 reject, never a default. (ST-4)
- **NC-5 (closed states).** A state arg resolves only if its marker is in the protocol's declared set. (ST-5)

## 9. Explicit Anti-Goals (out of scope; no fallback owed)

Each fails *loud and bounded*, never silently — the test for a safe anti-goal.

- **AG-TS-1 — cross-module state fabrication / strong mint integrity.** A foreign module that can construct
  `File` may assert any initial state. Out of scope: SIGIL has **no per-field privacy** (`Field` ast.rs:580
  carries no visibility) and no proven opaque-handle story, so strong integrity can't be expressed soundly
  yet. Epic 1 ships *weak/tracking* typestate (wrong-state *use* is rejected in well-typed code). A
  fabricating module had to construct the record itself — loud, not a silent corruption of someone else's
  handle. Natural strengthening once opaque handles land.
- **AG-TS-2 — cross-block / control-flow-join typestate dataflow (shipped).** The production
  ownership checker now propagates may-moved and may-borrowed state across all AIR CFG edges,
  including joins and loop back-edges; returning paths contribute no successor state.
- **AG-TS-3 — self-hosted `typecheck.sigil` parity for states.** Deferred exactly like HKT's AG-HK-S7: the
  differential `type_tag` carries the new tag so the harness compiles, but no typestate fixture enters the
  differential corpus until the self-hosted twin learns states.
- **AG-TS-4 — method-receiver typestate (`f.close()` consuming `self`).** Free-function-first like HK1
  (`close(f)`); method-receiver state transitions are a later rung, not a hole.
- **AG-TS-5 — general distributed / cross-actor typestate.** The narrow case (a state arg crossing
  `send`/`ask`) is gated existentially by **T274** (re-state at the receiver); the general
  distributed-typestate problem is out.
- **AG-TS-6 — state params inherit generic-inference semantics, including its over-approximations (TS3).**
  A `@S` state binder resolves to `Type::Generic` and rides the exact same call-site (Option-A) inference
  as an ordinary type param, so it inherits that inference's known leniencies — e.g. a multi-param
  same-binder call `fn pair<@S>(a: File<S>, b: File<S>)` invoked with `(File<Open>, File<Closed>)` is
  ACCEPTED, identical to `fn pair<T>(a: T, b: T)` invoked with `(i64, bool)` (also accepted). This is an
  over-ACCEPT (a missed cross-arg consistency check), NOT a typestate-specific regression and NOT unsound
  at runtime (states erase). Strengthening cross-arg consistency is a generics-wide concern, out of scope
  for typestate. *(Adversarial-sweep finding; the sweep's one real bug — a state-poly impl-method mangle
  ICE — was fixed.)*
- **AG-TS-7 — turbofish on a state param is overridden by argument inference (TS3).** `fd::<Banana>(a)`
  where `a: File<Open>` type-checks as `fd<Open>` (the argument binds `@S`, the turbofish is ignored),
  exactly as turbofish is subordinate to argument inference for ordinary generics. The worst case is a
  silently-ignored turbofish, never an ICE or an unsound accept.

## 10. Test gates (must be green before each rung lands)

1. **TS0 no-op (ST-1):** a stated program and its `<@S>`-stripped twin compile to **byte-identical AIR/WAT**
   (vs the twin, not a re-accepted snapshot). A declare-but-don't-operate fixture parses/resolves/type-checks.
2. **TS1 accept+reject (ST-3, ST-4):** the legal file-protocol sequence ACCEPTS; `read` after `close`
   REJECTS (T266); an unpinnable construction REJECTS (T269). The accept fixture guards against
   reject-everything.
3. **TS2 affinity non-vacuity (ST-2):** an execution fixture (`wasmtime::Module::new`-validated) where a
   use-after-transition fires **O001** — a `Copy` misclassification makes it silent → red.
4. **No-residual non-vacuity (T268):** a fixture proving `assert_no_residual_state` rejects an
   artificially-injected unstripped marker (the gate must not be vacuous).
5. **Closed-set (ST-5):** `File<Banana>` REJECTS at resolve.
6. **CI surface:** `cargo test --workspace` (not hand-picked `-p`); assert an ok-count (an empty
   failure-grep ≠ green). Typestate is type-level — no `--features solver` needed.
