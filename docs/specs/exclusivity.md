# Call-Site Exclusivity — the Binding-Level AG-1 Closure

**Status:** Implemented — v1 complete (PR-0 … PR-5)
**Date:** 2026-06-04
**Authors:** Nigel Robinson

---

## 1. Design Summary

`@ReadOnly` (`docs/specs/readonly.md`) gives a *callee-side* promise: a function will not
mutate through a frozen handle, and will not leak a mutable alias of it. The one threat it
was always honest about not closing is **AG-1 — remote aliasing**: a *second* binding to the
same heap object, mutable, mutated *while* the frozen view is live, breaking the read-only
invariant mid-execution. This is Rust's shared-XOR-mutable property, and `@ReadOnly` §4
names it as the boundary that "needs regions/borrows (DEF-2)."

Call-site exclusivity closes the **reachable core** of AG-1 without a whole-program
points-to or borrow checker. The insight is that, given SIGIL's actual expressiveness, the
only place a frozen view and a *simultaneously-live* mutable alias of one object can coexist
is **within a single call**:

> **`reject ⟺` one argument of a call reaches a FROZEN (`@ReadOnly`) parameter and an
> OVERLAPPING (alias- or field-related) argument reaches a MUTABLE (`@Mut`/bare) parameter
> of the SAME call.**

```sigil
record Box { v: i64 }
fn store(a: Box @ReadOnly, b: Box @Mut) -> i64 { return 0; }

fn caller() -> i64 ! { Alloc } {
    let p: Box = Box { v: 1 };
    return store(p, p);     // REJECTED at compile time (T255): `b` could mutate `p`
                            //   through the mutable handle while `a` holds it frozen.
}
```

It is **fully static, zero-cost, behaviour-additive**: T255 fires only on programs that are
genuinely new violations (essentially none in today's `@ReadOnly`-sparse corpus), and the
emitted AIR/WAT of every accepted program is byte-identical. DEF-2c *proves* the property;
it does not perform the **DEF-1** default-frozen flip that relies on it (§8).

### Core Principles

1. **The reachable core, not the global property.** v1 closes the AG-1 case that is
   *expressible and live* in SIGIL today — one call handing one object to a frozen and a
   mutable parameter. The global "no alias anywhere mutates this object" property still needs
   full regions/borrows; the documented remainder (through-RETURN extraction, container-
   mediated aliasing) is §6.
2. **Frozen-ness is the PARAMETER's, not the argument's.** A bare *mutable* local passed to a
   `@ReadOnly` parameter is frozen *on entry*. The conflict test keys on the callee's
   `param_mutability.is_frozen(i)`, never on whether the argument was already readonly.
3. **Overlap is conservative root equality.** Two argument places overlap iff, after alias
   resolution, they share a root local. Field/element STORES can make sibling paths hold one
   object, so same-root is treated as potential alias. Over-rejection is the safe direction
   (§6, AG-2c-9); a missed alias would be unsound.
4. **Fail-closed.** An un-resolvable place (a call result, a fresh construct, a scalar) is its
   own distinct identity, matched against nothing — never spuriously, never the silent
   non-conflict.
5. **Predicate-driven, so DEF-1 is a flip, not a rewrite.** The gate routes the frozen
   decision through the single `Mutability::is_frozen` predicate, so the default-flip
   (`bare ⇒ frozen`) auto-extends every gate with no DEF-2c change (§8).

---

## 2. Findings & Rationale

### 2.1 Why the surface collapses to the call site

Four facts about SIGIL's model narrow AG-1's reachable surface to one call:

- single-threaded synchronous tools + sequential actor handlers ⇒ no concurrent aliasing;
- no mutable globals (the capability model) ⇒ no free-floating mutable state;
- no first-class closures with per-parameter mutability (`Type::Fn` carries none, AG-2c-6);
- `@ReadOnly` is **parameter-only** — a local is frozen ONLY by `let`-propagation from a
  frozen parameter, so there are no author-frozen locals to alias-then-mutate temporally; and
- the existing escape gate (**T253**) already forbids a frozen value reaching a mutable sink.

Given all that, a frozen view and a simultaneously-live mutable alias of one object can only
co-exist inside a single call. Close that and AG-1's reachable core is closed.

### 2.2 Why not region-disjointness ("disjoint regions are provably non-aliasing")

The memory model's literal north star — *prove two values cannot alias because their regions
are disjoint* — is **not** the v1 proof. With one global bump allocator (no per-region arena,
the `regions.md` §16 honesty boundary) the implication is *structural, not physical*: two
"disjoint"-region values can still be the same pointer. It proves nothing for the common
same-region / `Global` corpus, and — fatally — its fail-closed direction is the *unsound* one
(a missed disjointness edge becomes a false non-aliasing claim). It is the DEF-2c+ north star,
correct once per-region arenas exist; it is recorded as an anti-goal (AG-2c-3), not built.

### 2.3 Why root equality, with no sibling admission

A first instinct is to admit *disjoint* sibling fields — `f(rec.a @ReadOnly, rec.b @Mut)` —
since `a` and `b` look like different objects. This is **unsound**: a prior `rec.a = x;
rec.b = x;` makes the siblings alias one object, so mutating `rec.b` breaks the frozen
`rec.a`. The adversarial review killed the place-prefix sibling-admission; v1 keys overlap on
the resolved ROOT and accepts the resulting over-rejection of genuinely-disjoint siblings
(AG-2c-9) as the safe, honest cost.

### 2.4 Cost model

| Operation | Cost |
|-----------|------|
| Representation (`MonomorphTracker.alias_origin: HashMap`) | One map per function body; seeded empty, `mem::take` save/restore like `readonly_locals`; never reaches `TypedParam`/AIR/WAT |
| The alias-origin propagation | One write per `let` at typecheck (aliasable place ⇒ resolved root, else removed) |
| The exclusivity partition | One all-pairs scan over the call's arguments at each of three call chokepoints, at typecheck |
| Runtime cost | **Zero.** Every check is at typecheck; the WAT is byte-identical to the un-gated program. |

---

## 3. Mechanisms — The Enforcement Model

### 3.1 `alias_origin` — the binding→root map (LD-1, PR-0)

`MonomorphTracker.alias_origin: HashMap<String, String>` maps a binding to the root local
whose heap object it aliases. It is seeded **empty** at every function-body entry (a parameter
is its own origin — the callee cannot know caller aliasing), saved/restored via `mem::take`
exactly like `readonly_locals` (so a generic-monomorph re-entry cannot corrupt the caller's
map), and grown **write-per-`let`** in `check_block`'s let-handler:

```text
let b = <aliasable PLACE>   ⇒   alias_origin[b] = resolve(root(place))   (the root it aliases)
let b = <anything else>     ⇒   alias_origin.remove(b)                   (b is its own root)
```

The write-per-`let` discipline (NOT append-only) is load-bearing: aliasing is **non-monotone**
under shadowing — a re-binding must *clear* a stale alias, unlike the monotone `readonly_locals`
(NC-2c-4).

### 3.2 `resolve_alias_root` — transitive, bounded, acyclic (NC-2c-3)

Resolution follows `alias_origin` to the terminal root, so a multi-hop launder
`let y = x; let z = y; f(x, z)` chains `z → y → x`. Each `let` only points a NEW name at an
EXISTING root, so the graph is acyclic by construction; the walk is bounded by the live-binding
count and `debug_assert!`-trips (an ICE, never an infinite loop) if that bound is exceeded.

### 3.3 `exclusivity_partition` — the conflict scan

`exclusivity_partition(args, param_mutability, alias_origin)` returns one conflict per ordered
pair `(i, j)` where parameter `i` is frozen and parameter `j` is mutable (both aliasable types)
and the alias-resolved roots of `arg_i` and `arg_j` are equal. It scans **all ordered pairs in
both directions** (so a mutable-first signature still fires), defaults an absent/unknown
`param_mutability[i]` to MUTABLE (the over-reject direction), and skips non-aliasable arguments
(scalars are copied, never aliased) and un-rooted arguments (a distinct identity). Conflicts
emit in argument-index order (deterministic).

### 3.4 The three sink sites — the closed call surface (NC-2c-1)

The gate is invoked at exactly the closed set of call-resolution chokepoints in
`type_check/expressions.rs`, each reusing the existing T253-loop scaffold:

| Site | Covers |
|------|--------|
| `infer_call_expr` | free + cross-module-synthetic + str/trait reroute (all land in the resolved `CrossModuleResolution::Found(sig)` arm) |
| `infer_method_call_expr` | true method + receiver (`typed_args[0]` is `self`, param index 0) |
| `infer_associated_fn_call` | no-`self` associated fn (generic-impl constructor) |

Closures / indirect calls carry no per-parameter mutability (AG-2c-6) and are not a sink;
record construction has no frozen/mutable parameters (a T253 escape sink, not a T255 one). A
contract test (`exclusivity_surface_is_closed`) counts the live `exclusivity_partition` call
sites and reddens if the surface changes without a conscious re-audit.

### 3.5 Scope-correct alias map (NC-2c-4, PR-3)

`alias_origin` is a flat tracker field, but a nested block's `let` shadow must not leak past
the block. `check_block` snapshots `alias_origin` on entry and restores it on exit — the
block-scope analogue of the cloned `env`. Without it, an inner `let x = <fresh>` would remove
the outer `x`'s alias and MASK a later outer-scope conflict (under-reject = unsound); the
mirror — an inner `let x = p` leaking a SPURIOUS conflict — is the over-reject the same restore
prevents. For a flat (no-nested-block) body the restore is a no-op-equivalent, so byte-identity
is preserved; the fix engages only when a nested block shadowed an outer binding.

---

## 4. The Soundness Boundary

What v1 **guarantees**: within any single function body, no single call hands one heap object
to a frozen parameter and a simultaneously-live mutable parameter — directly (`f(p, p)`),
through a `let`-launder of any depth (`let y = x; f(x, y)`), or through a shared field root
(`f(w.inner, w)`). This holds across every call-dispatch flavor (NC-2c-1) and composes with the
`@ReadOnly` escape gate: T253 proves "a frozen value never becomes a mutable sink downstream,"
T255 proves "no two coexisting aliasing arguments of differing mutability"; AG-1's core needs
both (NC-2c-8).

What v1 does **not** guarantee (and does not claim):

- **Through-RETURN extraction (AG-2c-1).** A mutable alias of a frozen object's interior pulled
  out through a method/function RETURN (`let m = ro.get(i); f(ro, m)`) — `m` has no place root,
  so it is a distinct identity, never matched. Inherits `@ReadOnly` AG-4; the frozen guarantee
  stays shallow. (DIRECT place extraction — `let m = rec.field` — IS a place and IS caught.)
- **Container-mediated cross-root aliasing (AG-2c-8).** Two values stored into DIFFERENT
  container roots that hold the same object alias through field STORES, not a `let` chain, so
  their distinct roots make the gate admit the pair. Detecting it needs whole-program points-to.

These are the same class — a value crossing a call or container boundary escapes the
binding-level tracker — and are closed, not patched, when full borrow checking lands.

---

## 5. Diagnostic Inventory

| Code | Severity | Fires when |
|------|----------|------------|
| **T255** | Error | one call hands the same heap object (alias-resolved root equality) to a frozen (`@ReadOnly`, or bare since DEF-1) parameter and a mutable (`@Mut`) parameter |

T255 aborts compilation (no bytecode emitted, per the standing `has_errors() ⇒
abort-before-AIR` rule). **T256** stays reserved (a possible future cross-region-exception
trace). The message names the shared root and prescribes the workaround (pass a copy to one of
the two arguments).

---

## 6. Explicit Anti-Goals

Formally OUT OF SCOPE for v1. A program exhibiting any of these does NOT violate the
exclusivity guarantee, and contributors are NOT required to detect or engineer fallbacks for
them.

- **AG-2c-1 — Through-CALL extraction aliasing.** A mutable alias obtained through a method/
  function RETURN (`let m = ro_vec.get(i); f(ro_vec, m)`). Direct place extraction IS caught;
  only the through-CALL remainder is out. Inherits `@ReadOnly` AG-4.
- **AG-2c-2 — Cross-actor shared payloads.** Zero-copy iff a common-ancestor region; today
  `send` copies, the surface isn't live. The actor epic.
- **AG-2c-3 — The disjoint-region MAY-alias precision (Shape C).** Admitting an overlap as safe
  because two bindings are in provably-disjoint regions. Physically sound only with per-region
  arenas (§2.2). The DEF-2c+ north star; the inert seam is not built.
- **AG-2c-4 — A `@Unique` / affine ownership axis.** No move/poison, no sole-ownership marker.
- **AG-2c-5 — The DEF-1 default-frozen flip itself.** DEF-2c proves the property; flipping
  `is_frozen` + the corpus `@Mut` migration is the separate DEF-1 epic.
- **AG-2c-6 — Closures / indirect calls.** `Type::Fn` carries no per-parameter mutability; not
  a live sink.
- **AG-2c-7 — Whole-function temporal aliasing without a call.** Not expressible — there are no
  author-frozen locals, so a frozen view and a mutable alias of one object cannot both be live
  in a body except via a call (covered) or a return (AG-2c-1).
- **AG-2c-8 — Container-mediated cross-root aliasing.** Two values stored into DIFFERENT
  containers holding one object alias through field STORES, not a `let` chain; their distinct
  roots make the gate admit the pair. Needs whole-program points-to.
- **AG-2c-9 — Sibling-field precision (the accepted over-rejection).** Two genuinely-distinct
  fields of one record passed to a frozen and a mutable parameter — `f(rec.a @ReadOnly,
  rec.b @Mut)` — are conservatively REJECTED, because a field store can make siblings alias
  (§2.3). The workaround is to copy one argument; per-field points-to is not built.
- **AG-2c-10 — let-handler non-interference proven by byte-equality.** The `alias_origin`
  population shares `check_block`'s let-handler with `@ReadOnly` and region propagation; its
  non-interference is guaranteed by the snapshot + shadow byte-identity gates, not by a
  hand-proof of statement ordering.

---

## 7. Constraints & Fallbacks

Each Existential Threat from the design's Adversarial-Compiler review reduced to a hard bound
(the **Boring Limit** — a count or closed set that makes the edge case impossible) plus a loud,
non-swallowing stop (the **Fail-Fast** — a specific diagnostic plus the standing `has_errors()
⇒ abort-before-AIR` rule). These are compile-time bounds; the units are counts and closed sets.

- **NC-2c-1 — One closed sink set.** *Limit:* gate sites = exactly `{free + cross-module +
  str/trait (infer_call_expr), method + receiver, associated-fn}`; ungated call paths = **0**.
  *Fail-Fast:* an un-gated flavor reddens `exclusivity_surface_is_closed`; a conflict → T255 →
  0 WASM.
- **NC-2c-2 — Root-equality overlap; no sibling admission.** *Limit:* overlap predicates that
  admit a same-root frozen×mutable pair = **0**; place-prefix sibling-admission paths = **0**.
  *Fail-Fast:* a same-root frozen×mutable pair → T255 (the sound over-rejection is AG-2c-9).
- **NC-2c-3 — Bounded, acyclic, transitive resolve.** *Limit:* `alias_origin` out-edges per
  binding ≤ 1; cycles = **0** (a `let` points a NEW name at an EXISTING root); `resolve` hops ≤
  the live-binding count. *Fail-Fast:* an over-long walk is a `debug_assert!`/ICE, never an
  infinite loop.
- **NC-2c-4 — Write-per-`let`, scope-correct alias map.** *Limit:* `let`s that leave a STALE
  `alias_origin[name]` = **0** (every `let` WRITES the bound name); inner-scope shadows that
  corrupt an outer origin after scope-exit = **0** (snapshot/restore at the block boundary).
  *Fail-Fast:* a regressed fresh-/inner-shadow test reddens PR-3; a stale alias firing is a
  spurious T255 caught by the corpus scan.
- **NC-2c-5 — Default-mutable on unknown; all-pairs both orders.** *Limit:* partition slots
  defaulting to frozen-on-unknown = **0**; (frozen, mutable) pairs skipped by positional order =
  **0**. *Fail-Fast:* a mutable-first `f(m @Mut, p @ReadOnly)` alias → T255.
- **NC-2c-6 — Un-rooted args are distinct identities.** *Limit:* shared sentinels for un-rooted
  args = **0**; scalar co-args reaching the partition = **0** (`is_aliasable_type`). *Fail-Fast:*
  `f(g(), h())` differing-mutability → CLEAN; a scalar `f(n @ReadOnly, n)` → CLEAN.
- **NC-2c-7 — Byte-identity MEASURED.** *Limit:* PRs moving a pre-existing snapshot = **0**;
  new-T255 hits on existing fixtures/stdlib = **0** (measured by the workspace corpus scan, not
  assumed). *Fail-Fast:* snapshot drift / shadow divergence fails the per-PR gate.
- **NC-2c-8 — T253 is a load-bearing precondition.** *Limit:* DEF-2c soundness claims that hold
  independent of T253 = **0**; AG-1's core needs both gates. *Fail-Fast:* a composition test
  pins that the canonical violation trips both codes, so a T253 regression surfaces as a red
  test, not a silent hole.

---

## 8. The Arc Beyond v1

DEF-2c was the last blocker on **DEF-1 — the default-frozen flip — which has since SHIPPED**.
With AG-1's call-site core closed, `bare ⇒ frozen` became soundly enforceable: the change was
one line — `Mutability::is_frozen` became `matches!(self, ReadOnly | Default)` — plus the
stdlib/corpus `@Mut` migration (done by hand; the flip is **global**, not scoped/opt-in).
Because every gate (the `@ReadOnly` write/escape gates and this exclusivity gate) routes through
that single predicate, the flip auto-extended all of them with no DEF-2c rework — exactly as the
flip-readiness suite predicted (it inverted on the flip, as designed). A bare parameter now
participates in T255 on the FROZEN side; `@Mut` is the only mutable state. See
`docs/specs/readonly.md` §8.

Beyond DEF-1: the disjoint-region non-aliasing PROOF (Shape C, AG-2c-3) and cross-actor
zero-copy become correct at the per-region-arena seam — *the region hierarchy is the
supervision tree* (`docs/memory-model.md`). Then **DEF-3** (capabilities-as-values) and
**DEF-4** (authority-origin) continue the capability arc.

---

## 9. Verification

The shipped suite (`crates/sigil-compiler/tests/exclusivity_compile.rs`,
`exclusivity_launder.rs`, `exclusivity_surface.rs`, `exclusivity_stress.rs`):

- **The conflict (T255):** `f(p, p)` frozen+mutable; the `let y = x; f(x, y)` launder and the
  transitive 2-hop `let y = x; let z = y; f(x, z)`; the mutable-first signature; same-root field
  `f(w.inner, w)`; the receiver+arg method case `p.rstore(p)`; the generic associated-fn
  `W::make(p, p)`; qualified and genuine cross-module `helpers::sink(p, p)`.
- **Negative controls (compile clean):** distinct objects `f(p, q)`; two `@ReadOnly` readers; two
  `@Mut` handles (no frozen view); scalar co-args; the fresh same-block shadow `let x = p;
  let x = Box{}; f(p, x)`; the inner-block alias that does not leak.
- **Scope-correctness:** the inner-block shadow that must not mask an outer conflict (under-reject
  guard) and the inner-block alias that must not leak one (over-reject mirror); doubly-nested
  restoration.
- **Composition:** T255 co-fires with T253 (escape) and T254 (region escape) on one call;
  `@SecretCT` taint does not mask or induce T255; generic-monomorph re-entry preserves the
  caller's `alias_origin`.
- **Closed surface + flip-readiness:** `exclusivity_surface_is_closed` (exactly three gate
  sites); the `@ReadOnly`-vs-bare witness pair differing only by `is_frozen(Default)`.

**Zero-cost invariant:** the type-check, AIR, Wasm, and workload snapshots remain byte-identical;
DEF-2c adds enforcement at typecheck and nothing to the emitted artifact.

---

## 10. References

- Boyland. "Alias Burying: Unique Variables Without Destructive Reads." SP&E 2001. (Read-only
  references over a shared heap without full linearity.)
- Clarke, Potter, Noble. "Ownership Types for Flexible Alias Protection." OOPSLA 1998.
  (Confinement and read-only views — the substrate the region/borrow layers reach toward.)
- Matsakis, Klock. "The Rust Language." (Shared-XOR-mutable — the property whose reachable core
  this gate enforces, and the borrow checker DEF-1's flip converges toward.)
- `docs/specs/readonly.md` §4, §7 (AG-1), §8 — the callee-side promise this closes the remote
  half of. `docs/specs/regions.md` §9 — the lifetime substrate. `docs/memory-model.md` — the
  per-region-arena seam the disjoint-region proof awaits.
