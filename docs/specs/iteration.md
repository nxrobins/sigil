# Iteration — the Lean Structural Iterator Protocol

**Status:** Implemented — v1 for `Vec<i64>` (Iterator epic): the `for x in <it>` desugar + shape gate (#224), the wasm match-structurer fix it surfaced (#225), and `Vec::iter()` / `VecIter` (#226)
**Date:** 2026-06-08
**Authors:** Nigel Robinson

---

## 1. Design Summary

`for x in …` historically accepted **only arrays** (`Type::Array`, else T052). The
COMPLETENESS frontier is `for x in coll` over the *collections* — `Vec`, `Map`,
`BoundedVec`. The "proper" answer is an `Iterator` trait with an associated `Item`
type — but **associated types do not exist** in SIGIL, and building them is a 2–3-week
type-system change in the same class as const generics (LOCKED-deferred). So v1 takes
the **lean structural** path, consistent with SIGIL's existing *structural* trait
satisfaction (a type satisfies `Hash`/`Eq` by having the right-shaped methods, no `impl`
block needed):

> **An iterator is any type with a `next(self @Mut) -> Option<T>` method.** Recognized by
> SHAPE — no `Iterator` trait, no associated types. `for x in it` desugars to a `while`
> loop over `it.next()`.

```sigil
let mut v: Vec<i64> = Vec::new();
v.push(10); v.push(20); v.push(30);
let mut sum: i64 = 0;
for x in v.iter() {        // VecIter has next(self @Mut) -> Option<i64> → iterable
    sum = sum + x;
}                          // sum == 60
```

### Core Principles

1. **Duck-typed, not trait-bound.** Iterability is a *shape* (`next(self @Mut) ->
   Option<T>`), checked exactly where method dispatch already resolves methods. No new
   trait machinery; nothing to `impl`.
2. **A desugar, not a new lowering.** `for x in it` rewrites (in the type checker) into
   `while`/`if`/`let` over `it.next()` — reusing all existing lowering. **Zero `air.rs`
   change.** The array `for`-loop path is untouched and byte-identical.
3. **Fail loud on a near-miss.** A type with a `next` of the WRONG shape (not `@Mut`, not
   `Option`-returning, extra params) is rejected AT the loop with **T259**, never
   mis-routed to the array path or silently iterated.

---

## 2. The Protocol

### Detection (the shape gate, T259)

In the `for`-loop type-check, the iterable is inferred once. If its type is a
`Type::Named(name, _)` whose `{name}::next` (resolved exactly as method dispatch does —
local sigs then a cross-module impl scan) matches a single dumb predicate:

- exactly one parameter (`self`),
- that `self` is **`@Mut`** (a bare `next(self)` is frozen → not an iterator),
- the return is **`Option<_>`** (one type argument),

then it is an iterator. Anything else routes as before: `Type::Array` → the existing
index loop; a `Named` type with a *mis-shaped* `next` → **T259** (abort-before-AIR); any
other type → the pre-existing T052. (A correctly-shaped *domain* `next()` — e.g. a
parser's `next() -> Option<Token>` — being iterable is by-design duck typing.)

### The desugar

`for x in <iterable> { <body> }` over an iterator becomes (built as untyped AST, checked
in a child scope, and spliced into the statement stream):

```text
let mut $for_it_K  = <iterable>;        // evaluated exactly once
let mut $for_go_K  = true;
while $for_go_K {
    let $for_opt_K = $for_it_K.next();
    if $for_opt_K.is_some() {
        let <x> = $for_opt_K.unwrap_or(0);
        <body>
    } else {
        $for_go_K = false;
    }
}
```

- **Hygiene.** The synthetic temps are `$`-prefixed — *outside* the `[A-Za-z_][A-Za-z0-9_]*`
  identifier grammar, so a user can neither collide with nor name them — and suffixed by
  the loop's byte offset `K`, so distinct (and nested) loops never clash.
- **`check_block` does the bookkeeping.** Checking the desugar through the real
  `check_let`/`check_while`/`check_if` gives `$it` its full treatment (mutables /
  readonly / region / alias) for free, and a `for` never guarantees return — so reachability
  is identical to the array path.
- **Why `if`/`is_some`/`unwrap_or`, not `match`.** See §5. v1 iterators yield `i64`
  (Anti-Goal AG-4), so the `is_some`-guarded `unwrap_or(0)` is the right width and its
  default is never observed.

---

## 3. The Surface (`Vec` iteration)

`stdlib/sigil/vec.sigil` gains a cursor and a constructor:

```sigil
record VecIter<T> { src: Vec<T>, pos: i64 }

impl VecIter<T> {
    pub fn next(self: VecIter<T> @Mut) -> Option<T> {
        if self.pos < self.src.len() {
            let v = self.src.get(self.pos);   // LEN-bounded via Vec::get (traps past count)
            self.pos = self.pos + 1;
            return Some(v);
        } else {
            return None;
        }
    }
}

impl Vec<T> {
    pub fn iter(self: Vec<T> @Mut) -> VecIter<T> {
        return VecIter { src: self, pos: 0 };
    }
}
```

- **`iter` takes `@Mut self`, deliberately.** A `VecIter` is a *mutable* handle (its
  cursor advances), so storing a frozen (`@ReadOnly`/default) Vec into it would re-widen
  authority — the escape gate rejects it (**T253**). The honest signature is therefore
  `@Mut`. In practice a Vec is built mutably and then iterated, so `let mut v; … for x in
  v.iter()` is the natural shape, no extra burden.
- **Reference semantics.** `VecIter` holds the Vec by reference (records are pointers), so
  it reads the SAME buffer. Mutating the Vec mid-iteration is memory-safe — every read is
  `Vec::get`-bounds-checked — but unspecified (Anti-Goal AG-2).
- **`Alloc`-free.** `iter` (a record literal) and `next` (bounds-checked reads) allocate
  nothing; only the Vec's own `push` carries `Alloc`.

---

## 4. Ambient injection (the transitive `option` edge)

`vec.sigil` now uses `Option` (`VecIter::next`'s return — `Some`/`None`). The ambient
token scanner runs on **user** sources *before* injection, so it never sees vec.sigil's
own `Some`/`None`. Therefore the `need_vec` trigger must transitively inject `option`
(which pulls `result`, as `Option::ok_or` uses `Ok`/`Err`) — mirroring how the `map` and
`strings` injections already pull their Option deps. Each transitive dep is suppressed if
the user shadows it with their own module.

This is **byte-identical for existing Vec programs**: `VecIter` / `iter` / `next` and the
injected `option` are all generic, so they are monomorphized (and emitted) only on use. A
Vec program that never calls `.iter()` gains no Wasm, as pinned by workload snapshots.

---

## 5. The match-statement detour (a bug found, fenced, then fixed)

The natural desugar destructures the `Option` with a `match`:

```sigil
match $for_opt_K { Some(x) => { <body> }, None => { $for_go_K = false; } }
```

Building it surfaced a **pre-existing wasm-backend defect**: a `match` STATEMENT whose
arms do not all `return` compiled to invalid wasm. Every stdlib match arm returns (e.g.
`option.sigil`'s `map`/`and_then`), so the path was never exercised. The AIR-level match
lowering was correct (it passes the `exit` block as each arm's continuation); the bug was
in the AIR→WASM CFG structurer's `merge_targets`, which — when a branch's two arms fall
through to *different* blocks (`Some(x)` flows `arm → extract → body → exit`, `None` flows
`arm → exit`) — arbitrarily returned the LEFT block, mis-structuring the merge.

- **Fenced (PR-1, #224):** the desugar uses `if`/`is_some`/`unwrap_or` (the well-trodden
  non-returning-branch path) instead of `match`.
- **Fixed (#225):** when the two fallthroughs differ, the structurer now computes the
  FIRST common successor of the two arms (`first_common_successor`). Scoped to `match`
  (the `merge_targets` path is reached only when `merge_block` is `None`; `if`/`else`
  carry an explicit merge and bypass it), so returning-arm matches and all `if`/`else`
  are byte-identical, as pinned by snapshots.

The fix unblocks side-effecting (non-returning) match arms generally; the iterator
desugar could now use the cleaner `match` form, though `if` is retained (it works and is
tested).

---

## 6. Constraints & Fallbacks (as shipped)

The epic's adversarial Constraint Matrix produced ten existential threats. Each, as it
landed:

- **ET-1 — shape-gated detection.** `next` must be arity-1 `@Mut self` returning
  `Option<_>`. A near-miss is **T259** at the loop, never mis-routed. *(Tests: missing
  `@Mut`, non-`Option` return, associated `next`.)*
- **ET-2 — evaluate once.** The iterable appears in the desugar exactly once (`let mut
  $it = <iterable>`); never re-evaluated.
- **ET-3 — hygienic temps.** `$`-prefixed (ungrammatical for users) + byte-offset suffix;
  nested-loop test pins no clash.
- **ET-4 — `return` propagates.** The body is spliced verbatim into the `is_some` branch;
  a `for x in it { return … }` returns from the enclosing function. *(Tested.)*
- **ET-5 — array path byte-identical.** Arrays/Slices keep the existing index loop; the
  iterator branch is reached only for non-array `Named` types. Snapshots pin the boundary.
- **ET-6 — block bookkeeping.** The spliced statements run through the same `check_*`; a
  `for` reports `guaranteed_return = false`, identical to the array path.
- **ET-7 — concrete loop-var type.** The element type comes free from the `unwrap_or`
  return inference; an unresolved type errors cleanly rather than reaching the backend.
- **ET-8 — full transitive ambient closure.** `vec` → `option` (+ `result`); a from-scratch
  `for x in v.iter()` compiles with no `use`. *(Ambient unit test.)*
- **ET-9 — memory-safety floor.** `VecIter::next` reads only via the bounds-checked
  `Vec::get`; no `next()` behavior yields an OOB.
- **ET-10 — capability gates.** The escape gate fired as designed (T253 on a frozen Vec in
  a mutable handle), resolved by `iter(@Mut self)`; verdicts match hand-written code.

---

## 7. Anti-Goals (v1 does NOT build / guarantee)

- **AG — associated types / a formal `Iterator` trait.** Deferred (same class as const
  generics). The structural protocol delivers `for x in coll` without them; a trait would
  buy generic-over-any-iterator code, not capability.
- **AG-1 — `Map`/`Set` iteration.** Iterator-v1 yields a single value, not the `(K, V)`
  pair `Map`/`Set` need. Tuples have since shipped (#229), so the pair is now expressible; a
  `Map::iter()` yielding `(K, V)` is unbuilt follow-on work, not a v1 iterator feature.
- **AG-2 — iterator invalidation.** Mutating a collection during its own iteration is
  memory-safe (ET-9) but UNSPECIFIED, fuel-bounded. No guard.
- **AG-3 — termination.** No static check; an iterator whose `next` never returns `None`
  is a fuel trap, not a compile error or UB.
- **AG-4 — non-`i64` element types.** Inherits the pre-existing `Vec<i32>`/`Vec<bool>`
  literal-call-width limitation; the desugar's `unwrap_or(0)` default is `i64`.
- **AG-5 — implicit `for x in v`.** The v1 surface is explicit: `for x in v.iter()`.
  Auto-calling `iter()` on a non-iterator iterable is a deferred ergonomic.
- **AG-6 — richer adapter kinds (PARTIALLY LIFTED, Completeness Phase 7).** `map`/`filter`/
  `take` SHIPPED — both as eager `Vec` methods that materialize a fresh `Vec<i64>`
  (`v.map(f).filter(g).sum()`) and as lazy `VecIter`→`MapIter`/`FilterIter`/`TakeIter`
  adapters that compose fluently and lazily (`v.iter().filter(g).map(f).take(n).collect()`),
  alongside the terminals `sum`/`fold`/`any`/`all`/`find`/`collect`. STILL OUT (no fallback):
  `zip`/`enumerate`/`skip`/`step_by`/`chain`/`flat_map`/`rev`, `DoubleEndedIterator`/`peekable`,
  type-changing `map` (`U ≠ i64`), and non-`i64` element pipelines (inherits AG-4 — the
  adapters are `Fn(i64)->…`-typed, i64-only by construction; a non-i64 element is a T071 type
  error, never a silent widen). The adapters are pure stdlib (`stdlib/sigil/vec.sigil`), no
  compiler change.
  - **Closure-signature checking (HARDENED — was a pre-existing compiler gap).** A *mis-typed
    closure* passed to an adapter METHOD is now cleanly rejected with T071: a wrong return
    type (`v.map(fn(x) -> bool …)`), wrong param type (`v.map(fn(s: str) …)`), or wrong arity
    (`v.fold(0, fn(a) …)` — previously a wasm-backend ICE) all surface as a type error at the
    arg span, matching the strict free-function path. The method-call arg loop now routes a
    `Type::Fn`-typed argument through the same `type_compatible` `Type::Fn` structural check
    (arity + param types + return type + linearity) that free calls use. The new strictness is
    scoped to `Type::Fn` params only, so the generics epic's int-literal-flex method args
    (scalar `T` positions) are unaffected. See `crates/sigil-compiler/tests/method_closure_arg_type.rs`.

---

## 8. The Arc Beyond

The structural protocol is the seam everything else hangs off — any type that grows a
`next(self @Mut) -> Option<T>` is iterable, for free:

1. **`BoundedVec` / array-slice iteration** — a `BoundedVecIter` (the bounded-collection
   family) and enabling `for x in slice` (the AIR already supports slices; the type-check
   gate just needs opening).
2. **Implicit `for x in v`** (AG-5) — when the iterable lacks `next` but has `iter`, seed
   the desugar with a synthetic `.iter()`.
3. **`Map`/`Set` iteration** — tuples landed (#229), so a `Map::iter()` yielding `(K, V)`
   is now expressible (closes AG-1's blocker).
4. **A formal `Iterator` trait** — if/when associated types are built, the structural
   `next` shape is exactly the contract it would formalize, so existing iterators become
   trait impls with no surface change.

The marquee consumer is the **SIGIL lexer-in-SIGIL**: `for token in lexer` over a
token stream is precisely a `next(self @Mut) -> Option<Token>` iterator — now expressible.

---

## Cross-references

- `docs/specs/bounded-collections.md` — the sibling monomorphized-collection epic;
  `BoundedVecIter` is the next iterator.
- `docs/specs/readonly.md` — default-frozen / T251–T253 (the `iter(@Mut self)` rationale).
- `docs/specs/strings.md` — the "trap is the floor, no silent corruption" principle the
  shape gate inherits.
