# Higher-Kinded Types in SIGIL — Design

**Status:** PR-HK0 through PR-HK3 implemented, including the HK3 hardening sweep.
**Scope:** the trusted (Rust) compiler. Self-hosted parity (`selfhost/typecheck.sigil`) is a deferred
follow-on epic (AG-HK-S7).

This spec was produced through the project's adversarial-hardening ritual: Adversarial-Compiler teardown
→ Existential/Academic triage (11 findings, code-grounded, each independently flip-tested → 5 existential
/ 6 academic, 0 contested) → Constraint Matrix (§9, Boring Limit + Fail-Fast). It mirrors the structure of
[type-checker-in-sigil.md](type-checker-in-sigil.md).

---

## 1. Context & Goal

SIGIL generics abstract over a *type argument* (`T`) but not over the *shape of a container*: there is no
way to write one function that works for `Vec<_>`, `Option<_>`, and `Map<_,_>` alike. HKT adds a
type-parameter that ranges over a **type constructor** — a variable `F` of kind `* -> *` that can be
instantiated to `Vec`, `Option`, etc. The headline payoff is making **functors / applicatives / monads
user-definable**:

```sigil
trait Functor<F: * -> *> {
    fn fmap<A, B>(self: F<A>, f: Fn(A) -> B) -> F<B>;
}
impl Functor<Vec> { fn fmap<A, B>(self: Vec<A>, f: Fn(A) -> B) -> Vec<B> { … } }
```

HKT is **purely type-level**; it adds **zero security surface** (see §7).

## 2. The oracle

The trusted compiler is the source of truth. The relevant pipeline (compiler.rs):
`name_resolution::resolve` → `typecheck_with_shadow`/`check_with_warnings` (monomorphization is **eager
and interleaved inside type-check**) → `ring_check` → `effect_check` → `taint_check` → `air::lower` →
`capability::verify` → `ownership::verify`. Generic (and higher-kinded) function bodies are checked **only
at concrete call sites** with a fully-concrete substitution; the emit-gate (`type_params.is_empty()`,
universe.rs) ensures only monomorphized, concrete-typed functions ever reach the soundness passes.

## 3. SIGIL representation — the erasure thesis

SIGIL has **no runtime type representation** and **eagerly monomorphizes**. An HKT variable `F` is a
**check-time-only artifact**: at each concrete call site it binds to a known nominal constructor name and
erases to an ordinary `Type::Named("Vec", […])` *before* AIR. No new AIR node, no wasm lowering, no
codegen, no runtime. This extends the "must be erased before AIR" invariant that `Type::Generic` and
`Type::IntLit` (PIL) already obey.

Three new `Type` variants (type_check/types.rs) — **distinct** variants, not a payload on `Generic`, so
the exhaustiveness checker flags every walker that forgot an arm (the "structural walker forgot an arm"
defense):

| Variant | Meaning |
|---|---|
| `HktVar { name, arity }` | a higher-kinded variable `F` of kind `* -> *` (arity 1), `* -> * -> *` (arity 2) |
| `HktApp { ctor, args }` | an application `F<A>`, `M<K, V>`, `F<G<A>>`; `args.len()` must equal the binder arity |
| `TypeCtor(String)` | the transient binding *target* `F |-> TypeCtor("Vec")`; lives only inside a `subst` map, consumed by `apply_subst` |

`HktVar`/`HktApp` erase before AIR; `TypeCtor` has a real arm only in `mangle_type` (`n.clone()`) and ICEs
everywhere else downstream — same discipline as `Generic`.

Surface syntax is the **explicit kind** `<F: * -> *>`. `*` and `->` are already lexer tokens, so the kind
grammar is a pure parser addition (`parse_kind`). `ast::TypeParam` gains `kind: ParamKind` (`Star |
Constructor { arity }`); `ast::hkt_params` projects the higher-kinded subset as `(name, arity)` pairs.

## 4. The differential harness

Deferred (AG-HK-S7). The Rust↔SIGIL `typecheck_differential` ET-T6 drift-locked `type_tag` map assigns
`HktVar`/`HktApp`/`TypeCtor` tags 24/25/26 so it compiles, but — because the variants are check-time-only
and erase before any emitted typed-node stream — no HKT fixture appears in the differential corpus until
the self-hosted twin learns these types.

## 5. The PR ladder

- **PR-HK0 — representation + parse + resolve foundation (no-op).** 3 `Type` variants; `ParamKind`;
  `parse_kind` (EX-5 grammar) + the `:`-clause fork; `resolve_type_expr_kinded` produces `HktVar`/`HktApp`
  for in-scope HKT binders; every `Type` walker gets a conservative/ICE arm; the spec doc. **Done-line:** a
  program declaring `<F: * -> *>` but never instantiating it parses, resolves, and type-checks. **Status:
  Implemented.**
- **PR-HK1 — free-fn HKT (arity 1): unify + mono + erasure.** EX-3 erasure arm; EX-4 residual gate;
  `mangle_type` `TypeCtor` arm; body-side subst consult; thread `hkt_params` into generic-fn sig/mono.
- **PR-HK2 — HKT-bounded traits + dispatch. SHIPPED, as a *higher-kinded `Self`* design** (the recon
  corrected the original `trait Functor<F: * -> *>` plan — traits had no type-level params at all, and the
  spec's `impl Functor<Box>` mis-parsed). As built: `trait Functor { fn fmap<A,B>(self: Self<A>, f: Fn(A)->B)
  -> Self<B>; }` + `impl Functor for Box` (the constructor in the *type* position — reuses the existing
  `impl Trait for Type` grammar). A trait whose methods use `Self` *applied* (`Self<A>`) is higher-kinded
  (`TraitContract.hkt_param = Some(("Self", arity))`, detected by `trait_self_arity`); its method sigs are
  built with `Self` threaded as the HKT binder. `constructor_satisfies` + the **EX-2 arity gate (T270)**.
  **No symbolic dispatch** — the recon proved (PROBE 4) it both doesn't exist and contradicts INV-1: under
  eager mono the body is checked only after `F` is concrete, so `xs.fmap(f)` resolves via the *ordinary*
  concrete method path. **Prerequisite fix:** generic impl methods (`fn fmap<A,B>` with the method's own
  type params) ICE'd today — `method_type_params` added to `FunctionSig` + inferred at dispatch (unify
  formals vs receiver+args); mono trigger / mangling / one-shot-emit-skip extended to method generics.
  *Deferred from this MVP:* full per-method signature conformance (enforced where the method is called in
  the mono body); single-constructor traits only (`Self<A>`, not `Self<A,B>` Bifunctors — HK3); no typeclass
  laws (AG).
- **PR-HK3 — multi-arg ctors `M<_,_>` + nesting `F<G<A>>`. SHIPPED — it FELL OUT of HK2's arity-generic
  build** (verify-and-test, almost no new code): `trait_self_arity`, `constructor_satisfies`, the
  `unify_inner`/`apply_subst` HKT arms, and `parse_kind` all *count* args/arrows — none were hard-wired to
  arity 1. Empirically confirmed at arity 2 and with nesting: a `trait Bifunctor { fn bimap<A,B,C,D>(self:
  Self<A,B>, …) -> Self<C,D>; }` + `impl Bifunctor for Pair` + `bimap2<F: * -> * -> * + Bifunctor>`
  type-checks, monomorphizes, and RUNS correctly (no side-swap); a free fn over `M: * -> * -> *` consumes a
  user `Entry<K,V>` (incl. mono-time field access `m.key`); a functor producing a nested `Box<Box<i64>>`
  erases + lowers + round-trips; the **EX-2 arity gate fires at arity 2** (arity-1 `Box` vs a 2-arg
  Bifunctor → T270); and the `MAX_KIND_ARITY = 2` cap rejects `* -> * -> * -> *` (P027). No `render_type`
  change was needed — a nested `HktApp` erases before it can surface in a diagnostic (an over-arity
  application fails at the unify gate as "could not infer F", which is already clear). Tests:
  `hkt_functor_runtime.rs` (+3 arity-2/nesting exec round-trips) + `hkt_kind_parse.rs` (+3 multi-arg
  accept/reject). Deferred unchanged from HK2: no typeclass laws; arity capped at 2 (a deliberate boring
  limit, not a gap).

### HK3 adversarial-sweep hardening (R1 / R2 / R3)

A 6-angle adversarial workflow over the shipped HK3 surface (independently re-verified, refute-by-default)
found **3 root-cause crashes / soundness holes** — 2 of them PRE-EXISTING on `main`, surfaced by the new
syntax. All fixed; each pins a regression test that may never PANIC.

- **R1 — EX-1 was never fully enforced.** The use-site arity gate existed only on the `let` path; function
  params, record fields, enum payloads, tuple/array/Fn positions, AND the HK turbofish all admitted a
  wrong-arity `Named` that tripped the `N10-PRDF` debug-assert (debug) / leaked a `Generic` into AIR
  (release). Fixes: `validate_lowered_type` gains the T231 arity arm + full composite recursion;
  impl-method sigs (raw-resolved) + record-field / enum-payload types (raw-resolved in `collect_type_universe`)
  get a dedicated `validate_field_payload_type_arity` pass; the `infer_path_expr` substitution site yields
  `Type::Error` (never panics, never leaks `Generic`) on a mismatch; and a turbofish arg for a higher-kinded
  param resolves to `TypeCtor`, not a malformed 0-arg `Named`.
- **R2 — non-injective monomorphization mangling** (pre-existing, all generics). The `_`-joined argument
  list fused distinct instantiations (`g<Foo_Bar, X>` ≡ `g<Foo, Bar_X>` ≡ `g__Foo_Bar_X`) → unsound-accept
  + wrong trait dispatch; and `Box<i64>`→`Box__i64` collided with a user `record Box__i64` → AIR ICE. Fix:
  argument lists join with `$` (outside the identifier grammar; the `$tuple` precedent) in `mangle_type`
  (Named / tuple / Array) + the free-fn and impl-method mono keys — injective among valid types given R1's
  arity gate; and user type names may no longer contain `__` (reserved for instance names) → **T271**. The
  self-hosted `typecheck.sigil` mangle (build + the `Array` parse) was updated in lock-step to keep the
  differential at parity.
- **R3 — `Generic` escaping into `type_compatible`.** An ill-typed Fn-argument to a generic method
  (`b.fmap(undefined)`) left the result-generic `B` unbound, surviving into the substituted return as
  `Generic("B")` → ICE. Fix: every method-generic gets a binding (unbindable → `Type::Error`) so
  `apply_subst` erases it; the arg's own error surfaces cleanly.

## 6. Core mechanics (target design for HK1–HK3)

- **Resolution** (`resolve_type_expr_kinded`): a use of an in-scope HKT binder resolves to `HktVar` (bare)
  or `HktApp` (applied), *preserving the type arguments* — before the ordinary-generic check, which would
  drop them. Once `subst` maps `F |-> TypeCtor("Vec")` (mono), `F<A>` resolves straight to `Vec<A>`
  (body-side erasure). **INV-3:** `check_let` must thread the mono subst into let-annotation resolution so
  `let r: F<i64>` inside a mono body erases rather than becoming a phantom `Named("F", [i64])`.
- **Unification** (`unify_inner`): `HktApp` vs `Named` — arity-gate, bind `ctor -> TypeCtor(name)`,
  zip-unify args; `HktVar` vs `Named` binds the head; `HktApp` vs `HktApp` (same ctor) zip-unifies. First-
  order/decidable because under eager mono the *actual* side is always a rigid `Named` (no flex-flex).
- **Substitution** (`apply_subst`): `HktApp` + `F |-> TypeCtor(c)` ⇒ `Named(c, args)` **only when
  `args.len()` equals c's declared arity** (EX-3); else `Type::Error`.
- **Monomorphization**: rides the existing `subst` (`F -> TypeCtor("Vec")`); `mangle_type(TypeCtor(n)) =
  n` ⇒ `map__Vec_i64_str`.
- **HKT-bounded traits**: `TraitContract.hkt_param`; check-time dispatch routes a method call on `F<A>`
  (F bounded by Functor) to the bound's contract; mono-time dispatch resolves the concrete `Vec::fmap`.
  **INV-2:** `type_satisfies_trait` must route `HktVar` through the existing `Generic` conservative-allow
  arm or it falsely emits T245.

## 7. The security-surface story (verified, not asserted)

The "zero security surface" claim is *earned*: monomorphization is interleaved inside type-check, and the
cap/ring/effect/taint/region/Z3 passes iterate only the all-concrete `TypedProgram` (verified pass order in
compiler.rs; emit-gate in universe.rs). The would-be cap-smuggling channel through an HKT-erased field
`f: F<cap Fuel>` is structurally unreachable: materializing the inner `Ctor<Fuel>` value first trips T186
(array literal) or T242 (generic aggregate, which walks the substituted type-args). Adding `HktApp`/
`TypeCtor` arms to `type_contains_cap`/`is_send_type`/`type_is_reassignable` (done in PR-HK0) is
defense-in-depth (INV-4).

## 8. Load-bearing Soundness Invariants

The academic waivers in §10.B hold **only** while these are preserved; a future rung that breaks one
reverts the corresponding waiver to an existential threat.

- **INV-1** (keeps AG-HK-3 academic): eager monomorphization, no symbolic body-check — the *actual* side
  reaching unify is always a rigid `Named`. If an Option-B / lazy body-check rung lands, re-open V3.
- **INV-2** (keeps AG-HK-3 / AG-HK-1): the loud/erasing arms ship with the feature (EX-3 erasure;
  `type_satisfies_trait` routes `HktVar` through the conservative-allow arm; mangle/type_compatible
  real-or-panic arms). Skipping them makes the hole self-revealing, not silently shipped.
- **INV-3** (a real pre-existing bug HK1 must fix): thread the mono subst into `check_let` annotation
  resolution so `let r: F<i64>` erases `F`.
- **INV-4** (defense-in-depth for AG-HK-1): `HktApp`/`TypeCtor` arms in the cap/send/reassign walkers.

## 9. Constraints & Fallbacks

A dumb physical constraint per vulnerability — **Boring Limit** (the exact numeric bound / hard equality /
count that makes the edge case impossible) + **Fail-Fast Mode** (exactly how it rejects/panics without
swallowing). Diagnostic numbers: `T270`/`T272`/`T273` are new (codes ≤ T265 are taken); the kind-grammar
parser code is **P027** (shipped in PR-HK0). The de-facto max type-constructor arity across stdlib+selfhost
is **2** (`Result<T,E>`, `Map<K,V>`), so `MAX_KIND_ARITY = MAX_HKT_CTOR_ARITY = 2`,
`MAX_MONOMORPH_DEPTH = 64` (reused).

**EX-1 (V4) — Use-site arity gate, every annotation position.** *Boring Limit:* `args.len() ==
declared_arity` for every `Named`/`HktApp` (record/enum `type_params.len()`, builtin fixed arity, HKT
binder kind-arrow count), enforced **inside `resolve_type_expr` at `Named` construction** — not the
bypassable `validate_lowered_type` wrapper (~40 callers skip it). *Fail-Fast:* **T231** as a real
`Diagnostic::error` (return `Type::Error`) at that construction point during type-check; replace the silent
`continue` at the AIR field-registry and the `Generic`-only `mangle_type` ICE with hard panics for any
residual mis-arity `Named` (no `debug_assert`, no release-strip).

**EX-2 (V5) — Impl ctor arity vs trait HKT-slot arity.** *Boring Limit:* `bound_ctor.arity ==
trait_slot.kind_arity` (exact equality) **AND** `kind_arity <= MAX_HKT_CTOR_ARITY = 2`, enforced at the
single ctor-binding/erasure choke point. *Fail-Fast:* `Diagnostic::error(T270)` at the binding span; the
always-on error-severity gate in `check_with_warnings` aborts before AIR — **not** a validator `continue`,
which drops nothing (impl methods register earlier in `collect_type_universe`); `mangle_type` ICE backstops.

**EX-3 (V6) — `apply_subst` erasure arity-totality.** *Boring Limit:* every `Named(ctor, args)` produced by
`apply_subst` (the sole erasure point) must satisfy `args.len() == ctor's declared type_params.len()` — a
real check the `Named` arm lacks today. *Fail-Fast:* the `apply_subst` `Named` arm (and the `mangle_type`
`Named` arm) `panic!` on mismatch — a **release-surviving panic**, not a `debug_assert` and not a
`continue` — broadening the `Generic`-only ICE which today lets a wrong-count concrete `Named` mangle
silently to wasm. (A deferred `T272` error is unavailable until that code is defined.)

**EX-4 (V8) — No residual symbolic HKT reaches codegen.** *Boring Limit:* the **transitive** node-count of
`HktVar|HktApp|TypeCtor` over every Type in the TypedProgram (descending Fn params/return, Tuple, Array,
Ref, Slice, Ptr/MutPtr, **and** Named args) == 0. *Fail-Fast:* an always-on `assert_no_residual_hkt` walk
(not `debug_assert`, not a discardable `Result`) emitting a new post-typecheck **T273** **before**
`compiler.rs` runs ring/effect/taint (the `mangle_type` ICE cannot guard those — they precede `air::lower`);
plus separate explicit panic arms for all three variants in `mangle_type`/`lower_type`/`classify_value_kind`/
`type_compatible`, each placed so it can never fall into the `=> AirType::Ptr`, `_ => AirValueKind::Copy`,
or `_ => expected==actual` catch-alls. (PR-HK0 shipped the per-walker arms; the whole-program gate lands in
PR-HK1 alongside the first instantiation path.)

**EX-5 (V11) — Kind well-formedness + application arity.** *Boring Limit:* two purely-syntactic parse-time
bounds — kind arrow-count ∈ `[1, MAX_KIND_ARITY = 2]` and type-expr nesting-depth ≤ 64; application-arity
is the exact equality `args.len() == binder arity` checked at the **post-resolution** erasure/use-site gate
(binder arity is unknown at parse). *Fail-Fast:* arrow-count/depth violations `return`/emit **P027**
consuming no further tokens, before name-resolution; arity mismatch → T231/T272 before AIR; residual HKT is
a dedicated `Type` variant whose only `mangle_type` arm is `panic!` (never the silent `Named`/`IntLit`
arms). `lower_type` is not a primary guard sink. (PR-HK0 shipped `parse_kind` + the `[1,2]`/arity-0/
dangling-arrow rejections as P027; the nesting-depth counter + post-resolution arity gate land with the use
sites in PR-HK1/HK3.)

## 10. Explicit Anti-Goals

### A. Scope anti-goals (feature boundaries — deliberately unsupported)
- **AG-HK-S1** HKT var as a first-class value / partial application (`let g = Vec;`, passing `F`).
- **AG-HK-S2** Higher-rank / rank-N polymorphism (binders only at fn/trait/impl level).
- **AG-HK-S3** Kind inference beyond syntactic arrow-count — no kind variables, no kind unification.
- **AG-HK-S4** HKT over structural builtins `Fn`/`Tuple`/`Array`/`Ref`/`Slice` — `TypeCtor` wraps a
  **nominal `Named` constructor name only**.
- **AG-HK-S5** Type-alias constructors as HKT instantiations (aliases expand eagerly, non-parametric).
- **AG-HK-S6** Functor/monad *laws* or coherence/overlap beyond existing structural+orphan rules.
- **AG-HK-S7** Self-hosted (`selfhost/typecheck.sigil`) parity — deferred follow-on epic.

### B. Threat-waiver anti-goals (academic edge-cases — formally declined; do NOT engineer fallbacks)
Each survived an independent adversarial flip. Waiver justification in italics.

- **AG-HK-1: HKT symbolic-stub soundness under pass ordering.** SIGIL does not engineer a separate
  fail-closed soundness path in the cap/ring/effect/taint/region/Z3 passes for symbolic HKT types, because
  eager monomorphization erases every HKT variable to a concrete `Type::Named` before AIR and the emit-gate
  ensures only monomorphized concrete-typed functions reach those passes; the only would-be cap channel
  (`f: F<Fuel>`) is structurally unreachable (T186/T242 at the inner construction). *Adding the cap-walker
  arms (INV-4) is defense-in-depth, not a guard against a reachable exploit.*

- **AG-HK-2: bare-String constructor identity.** SIGIL does not give `TypeCtor(String)` a DefId- or
  module-qualified identity; it matches a constructor by surface name exactly as `Type::Named` and the
  universe tables already do. Within the single-crate, flat-type-namespace model this is not a new hole.
  **⚠ TRIP-WIRE (reopen as EXISTENTIAL before either lands):** multi-crate compilation OR per-module type
  namespaces make `TypeCtor(String)` existential — promote ctor identity to a DefId/module-qualified key in
  `TypeCtor`, the unify/type_compatible `Named` arms, and the universe record/enum keys.

- **AG-HK-3: symbolic-actual flex-flex in HKT unification.** SIGIL does not perform higher-order (flex-flex)
  unification of a symbolic actual against a symbolic expected, because eager mono makes the actual side a
  rigid `Named`; survivors are caught LOUDLY (type_compatible/mangle_type ICE). **Depends on INV-1/INV-2/
  INV-3.** *No occurs-check / two-symbolic-side unifier fallback is required.*

- **AG-HK-7: free-variable trait-method signatures are not well-formedness-checked at trait-declaration
  time.** A method signature naming a type that is neither `Self`, the trait's `hkt_param`, nor a
  method-local param silently resolves to `Named(n, args)`; this is inert because its sole consumer
  (`structural_satisfies`) feeds a structural `==` that a free var can never pass, so every candidate impl
  rejects with **T246** before any lowering. *No fallback required.*

- **AG-HK-9: accidental structural constructor-trait satisfaction.** A constructor whose inherent methods
  happen to match a trait's methods (exact name + exact signature) satisfies the bound structurally, as the
  scalar tier already does for `Hash`/`Eq`. Sound because satisfaction and dispatch resolve through the
  identical key + resolver; worst case is a type-correct semantic surprise, never invalid wasm. *No
  mandatory nominal-impl recording required.*

- **AG-HK-10: polymorphic-constructor recursion bound.** SIGIL does not compute a precise occurs-check for
  a generic function that re-applies its own constructor parameter at strictly greater depth; the unbounded
  instance set is cut off by `MAX_MONOMORPH_DEPTH = 64` with a fail-closed **T150/T151** at every growth
  site — the same bound non-HKT recursive generics already inherit. *No deep-finite-vs-infinite distinction
  required below depth 64.*

## 11. PR-HK0 — what shipped

- `Type::{HktVar, HktApp, TypeCtor}` (types.rs) + `ast::{ParamKind, hkt_params, MAX_KIND_ARITY}`.
- Every exhaustive `Type` walker handles the new variants: `mangle_type`/`lower_type`/`runtime_type`/
  `classify_value_kind`/`type_compatible` ICE; `apply_subst`/`resolve_type_expr_kinded` produce/preserve
  symbolic HKT; `type_contains_cap`/`is_send_type`/`type_is_reassignable`/`render_type`/
  `default_int_lit_in_type` handle them conservatively; the differential `type_tag` ET-T6 map tags them.
- `parse_kind` + the `:`-clause fork in `parse_type_params`; `P027` for malformed kinds (bare `*`,
  dangling `->`, over-arity > 2).
- `resolve_type_expr_kinded` (the HKT-aware core; the old `resolve_type_expr` is a `&[]` wrapper) producing
  `HktVar`/`HktApp` for in-scope binders, preserving type args.
- Tests: `tests/hkt_kind_parse.rs` (10) + `type_check::tests::hkt_resolve_tests` (3); `cargo test
  --workspace`, `clippy -D warnings`, `fmt --check` green.

## Cross-references
- Generics precedent: [type-checker-in-sigil.md](type-checker-in-sigil.md) §11/§12.
- Walker bug class: the "structural walker forgot an arm" memo.
