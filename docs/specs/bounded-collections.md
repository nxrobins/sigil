# Bounded Collections — Monomorphized, Stack-Backed, `Alloc`-Free

**Status:** Implemented — `BoundedVec_i64` v1 complete (BoundedVec epic, #220–#222): associated-fn dispatch (#220), the construction seal + module + corpus (#221), the `_64`/`_256` sizes + `set` + the `[0; N]` array-repeat literal (#222)
**Date:** 2026-06-07
**Authors:** Nigel Robinson

---

## 1. Design Summary

The unbounded collection family — growable `Vec<T>` and generic `Map<K, V>` — is the
heap **escape hatch**: it carries `! { Alloc }`, grows without a static ceiling, and is
exactly what a self-hosting compiler's symbol tables want. The COMPLETENESS *inner ring*
wants the opposite: a collection whose entire footprint is **bounded and known at compile
time**, so an agent-authored tool that must run under a fixed fuel/memory budget can hold
a working set with **no `Alloc` effect at all**.

A `BoundedVec` is that collection. It is a **monomorphized fixed-`N` record** — a concrete
`record BoundedVec_i64_8 { data: [i64; 8], count: i64 }`, *not* a parametric
`BoundedVec<T, N>`. Const generics are outside this concrete family; it instead ships as
concrete sizes per element type.
v1 ships the `i64` element at three capacities:

```sigil
let mut v: BoundedVec_i64_8 = BoundedVec_i64_8::new();   // capacity 8
v.push(10);
v.push(20);
let n: i64 = v.len();                                    // 2
let o: Option<i64> = v.get(0);                           // Some(10)
v.set(1, 99);                                            // overwrite the live cell at 1
let p: Option<i64> = v.pop();                            // Some(99); len → 1
// BoundedVec_i64_64 and BoundedVec_i64_256 are the same API at larger N.
```

### Core Principles

1. **Bounded backing, not a refinement.** The elements live in a FIXED `[i64; N]` array.
   Resource-boundedness is a *physical* fact of that backing, not a static `len ≤ N`
   proof — the refinement system is construction-time and does not model mutation, so
   the ceiling is enforced where the bytes are, by the array's own bounds check (§4).
2. **No `Alloc`.** The backing is a bump-allocated region the fuel system accounts for
   statically (N·8 bytes), with **no `alloc()` call** — so the whole API is `Alloc`-free,
   the property that separates it from `Vec` (§3, §5 ET-2).
3. **Overflow traps; it never corrupts.** A `push` past capacity writes `self.data[N]`,
   which trips the backing array's `idx ≥ N` trap. A write therefore NEVER escapes the
   N·8-byte region — memory safety is *free*, independent of the logical `count` (§4).
4. **The length claim is sealed, so it's trustworthy.** Memory safety is free, but the
   *integrity* of `count` (the "I hold `count ≤ N` live elements" claim a verifier reads)
   requires that `count` cannot be forged. The record is **construction-sealed** (T258):
   buildable only inside its module, never via a `BoundedVec_i64_8 { count: 99 }` literal
   in user code (§4, the keystone).

---

## 2. The Model

A `BoundedVec_i64_N` is an ordinary SIGIL record, so it inherits the standard runtime
representation — a compact **12-byte header** `[data_ptr: u32 @0, count: i64 @4]` (an array
field lowers to a `u32` pointer, and fields pack with no alignment padding) — over a
**separate** array backing:

```
record header (BumpAlloc, 12 B)        array backing (BumpAlloc, 4 + N·8 B)
┌──────────────┬───────────┐           ┌──────────┬──────────┬─────┬──────────┐
│ data_ptr:u32 │ count:i64 │ ────────▶  │ len:u32  │ cell[0]  │ ... │ cell[N-1]│
│      @0      │    @4     │            │  = N @0  │   @4     │     │          │
└──────────────┴───────────┘           └──────────┴──────────┴─────┴──────────┘
```

This layout carries the load-bearing insight of the whole design: **there are two
lengths.**

- `count` (in the record header) is the **logical** length — how many cells the API
  treats as live. It drives `len()`, `is_empty`/`is_full`, and the `get`/`set`/`pop`
  bounds.
- `len = N` (in the *backing's* own 4-byte header) is the **physical** length — the array's
  intrinsic size. It drives the hardware bounds trap on every `self.data[i]`.

`count` is data the user's value carries; `N` is a fact of the allocation. The bounds trap
reads `N`, never `count` — so **no value of `count`, however forged, can make
`self.data[i]` reach past the N·8-byte backing.** Memory safety does not depend on `count`
being honest. That is what lets the seal (§4) be about *integrity* alone, not safety.

Like every SIGIL record, a `BoundedVec` has **reference semantics**: a by-value copy
duplicates the 12-byte header (and shares the `data_ptr` backing), exactly as a `Vec` copy
shares its buffer. This is why `push`/`pop`/`set` take `@Mut self` and why a region-born
`BoundedVec` is region-escape-tracked (§6).

### Why no `Alloc`

Both BumpAllocs — the header and the backing array literal `[0; N]` — are *array/record
literals*, and the effect checker emits the `Alloc` effect **only** for the `alloc()`
intrinsic. A bump-allocated literal carries no effect. So `BoundedVec_i64_8::new()` and
every method compile inside a `tool_main` declared with **no `! { Alloc }`** — contrast
`Vec::new()`/`push`, whose heap growth *does* carry `Alloc`. The bounded footprint is
real (N·8 bytes of fuel), but it is *statically* charged, not a dynamic allocation
capability.

---

## 3. The Surface

The API lives in **`stdlib/sigil/bounded_vec_i64.sigil`** (`module bounded_vec_i64;`, **no
effect annotation** — `Alloc`-free). Each size is an independent `record` + `impl` (the
accepted cost of monomorphized slots); they differ ONLY in `N` — the backing length, the
`capacity()` constant, the `is_full` bound, and the out-of-range force-trap index `data[N]`.

| Method | Signature | Semantics |
|---|---|---|
| `BoundedVec_i64_8::new()` | `() -> BoundedVec_i64_8` | empty vector — the ONLY public constructor (the record is sealed) |
| `v.len()` | `(self) -> i64` | the logical length `count` |
| `v.capacity()` | `(self) -> i64` | the constant `N` (8 / 64 / 256) |
| `v.is_empty()` | `(self) -> bool` | `count == 0` |
| `v.is_full()` | `(self) -> bool` | `count == N` |
| `v.push(val)` | `(self @Mut, i64) -> i64` | append; returns the new length. At `count == N`, `self.data[N]` traps (overflow) |
| `v.pop()` | `(self @Mut) -> Option<i64>` | remove + return the last, or `None` if empty |
| `v.get(i)` | `(self, i64) -> Option<i64>` | read cell `i`, or `None` if out of `[0, count)` — LEN-bounded |
| `v.set(i, val)` | `(self @Mut, i64, i64) -> i64` | overwrite the LIVE cell `i`; an out-of-range `i` TRAPS — LEN-bounded (§5 ET-7) |

`get` and `set` are the read/write pair over the **live** region `[0, count)`. They differ
in their out-of-range behavior, and deliberately so: `get` returns `None` (a read of an
absent cell is a benign question), while `set` **traps** (a write that misses the live
region is a correctness bug — a silently-dropped or tail-clobbering write would be the
"silent corruption" the language's floor forbids; cf. the UTF-8 epic, `strings.md` §5 AC-2).

### Dispatch (PR #220)

`BoundedVec_i64_8::new()` is an **associated function on a concrete record** — there is no
`self` receiver to route on, so the usual method-dispatch path does not apply. The fix is
`is_associated: bool` on each `FunctionSig` (true iff an impl method's first param is not
`self`); the `Type::method()` reroute resolves an associated function when its `is_associated`
flag is set. A records-only outer guard (the receiver names a `universe.records` entry and
is not a shadowing local) keeps the reroute from hijacking enum-variant constructors,
module-qualified calls, or ordinary `self`-methods (§5 ET-5).

### Ambient injection

`bounded_vec_i64.sigil` is auto-injected when the token scanner sees any identifier with
the **`BoundedVec_i64_` prefix** (an annotation `: BoundedVec_i64_64` or a constructor
`BoundedVec_i64_256::new()`). One module defines all three sizes, so any size triggers the
whole unit; an unused size is dead-code-eliminated from the WASM. Because `pop`/`get` return
`Option<i64>`, injecting the module pulls `option.sigil` transitively. A user `module
bounded_vec_i64;` or a user `record BoundedVec_i64_*` suppresses injection (the standard
dup-module / collision guard). A different element type (`BoundedVec_i32_*`) does not match
the `i64` prefix — it is a different (future) module.

---

## 4. The Keystone: construction sealing (T258)

The fixed backing already makes every element access **memory-safe** — a forged index just
traps against the backing's physical `N` (§2). What it does NOT give for free is
**integrity**: without a seal, a user could write

```sigil
let v: BoundedVec_i64_8 = BoundedVec_i64_8 { data: [0; 8], count: 99 };
```

and mint a value that *claims* `len() == 99` while backed by 8 cells. Nothing about that
value is memory-unsafe (a `get(50)` returns `None`; a forged index still traps) — but the
`count ≤ N` invariant a verifier relies on is a **lie**. A pre-seal spike confirmed records
are not module-private by default: even `Vec { count: 99 }` compiled in user code. That is
the killer the adversarial teardown surfaced, and the seal is the epic's keystone.

**The seal.** The type universe now records each record's defining module
(`record_modules: name → module`). Constructing a record whose defining module name begins
with `bounded_` from *outside* that module is rejected with **T258**, abort-before-AIR. So
the `count` field can only ever be written by the module's own `new()` / mutators, which
maintain `count ≤ N` by construction. `BoundedVec_i64_8::new()` (constructed *inside* the
sealed module) and all methods compile cleanly from user code; the direct literal does not.
The gate is keyed on the **module**, not the type, so it covers every size in the family —
a forged `_64` is T258 exactly like a forged `_8`.

This is the **verifier thesis** in miniature: memory safety from the hardware-checked
backing, integrity from the seal, and nothing in between left to trust.

---

## 5. Constraints & Fallbacks (as shipped)

The epic's adversarial Constraint Matrix produced seven existential threats. Each, as it
actually landed:

### ET-1 — a forged `count` lies about the length
**Limit:** `count` is writable only inside the sealed module. **Fail-fast:** **T258**
(compile-time, abort-before-AIR) on any `bounded_*` record literal in user code; pinned by
`bounded_vec_seal.rs` (forge `_8` `{count: 99}` → T258, forge `_8` `{count: 0}` → T258 — the
gate is on the module, not the values; forge `_64` → T258; `::new()` + methods compile; a
user's own record is unaffected).

### ET-2 — a hidden `Alloc`
**Limit:** the backing is a bump-allocated literal, and `Alloc` is emitted only for
`alloc()`. **Fail-fast:** the entire runtime corpus compiles under a `tool_main` with **no
`! { Alloc }`** — so every passing test (new/push/pop/get/set/len/capacity/is_empty/is_full
at all three sizes) is *also* a no-`Alloc` proof. An accidental `alloc()` in any method body
would make the tool fail to type-check (missing effect).

### ET-3 — overflow corrupts instead of trapping
**Limit:** a full `push` targets `self.data[count]` at `count == N`, i.e. `self.data[N]`,
which the backing's `idx ≥ N` check traps. **Fail-fast:** a **rigorous positive-return trap
detector** (`body_traps`: the tool returns `v.len() + 1`, so a clean run is `Ok` and only a
genuine wasm trap is `Err(Trapped)` — a `0 - x` sentinel body would itself *look* trapped,
hiding a missing trap) asserts the 9th push into a `_8`, the 65th into a `_64`, and the
257th into a `_256` all trap, while exactly N pushes are clean.

### ET-4 — a region-born backing escapes and dangles
**Limit:** the backing is a `BumpAlloc`; inside a `region {}` the arena frees at region exit
(DEF-2a), so an escaped `BoundedVec` would dangle UNLESS region-tracked. **Fail-fast:** this
falls out of EXISTING machinery — `region_of_value` already scores the array-backed record
region-born, so the **T254** region-escape gate rejects it at **parity with `Vec`**
(`bounded_vec_region.rs` measures both: a region `Vec` escape and a region `BoundedVec`
escape produce the identical T254 verdict). No bounded-collection exemption.

### ET-5 — the associated-fn reroute over-fires
**Limit:** the `Type::method()` reroute keys on `is_associated` AND a records-only outer
guard (the receiver names a record, not a shadowing local). **Fail-fast:**
`assoc_fn_concrete_record.rs` pins that `::new()` and an associated fn with an arg resolve
for a concrete record, a `self`-method still dispatches normally, and — the negative —
`enum_variant_ctor_not_hijacked` confirms an enum constructor of the same shape is left
alone.

### ET-6 — `capacity()` drifts from the backing
**Limit:** `capacity()` returns a hand-written constant that MUST equal the backing `N`; a
drift (say `capacity()` says 64 but the backing is 8) would silently mis-report. **Fail-fast:**
the behavioral-N is pinned directly — at every size, filling exactly `N` is clean *and*
`is_full`/`len == capacity` hold, while the `N+1`th push traps. The `_256` case fills 256
clean and traps on 257, the direct proof that `capacity() == 256` matches the `[0; 256]`
backing with no constant/length drift.

### ET-7 — `get`/`set` leak or clobber outside the live region
**Limit:** both are **LEN-bounded** to `[0, count)` — not merely capacity-bounded.
`get(i)` returns `None` for `i < 0` or `i ≥ count` (so a popped-stale or never-written cell
in `[count, N)` is unreachable). `set(i, val)` writes only a live cell; an out-of-range `i`
is forced into the backing trap via `self.data[N]` (SIGIL has no user `trap()`), and its own
`i < 0` guard covers the negative index the `idx ≥ N` check would otherwise miss.
**Fail-fast:** `get(5)`/`get(-1)` on a len-2 vector return `None` (clean); `set` overwrites a
live cell and preserves its neighbors + `len`; and the LEN-vs-CAP distinction is pinned
explicitly — **`set(count)` traps even though `count < N`** (an index in the `[count, N)`
capacity tail is within the backing but is not a live cell, so a length-bounded write must
reject it).

---

## 6. Composition with the capability gates

- **regions / T254.** §5 ET-4: a `BoundedVec` built in a `region {}` is region-born; escaping
  it is rejected at parity with `Vec`; in-region use is clean.
- **default-frozen / T251–T253.** `push`/`pop`/`set` mutate the shared header, so they take
  `self: BoundedVec_i64_N @Mut`; `len`/`get`/`capacity`/`is_empty`/`is_full` take a bare
  (frozen) `self` and only read. Passing a bounded vector to a frozen param and mutating it
  there is the standard T253 escape hazard, unchanged by this family.
- **the `[0; N]` enabler.** `new()` initializes the backing with the **array-repeat
  expression literal** `[0; N]` (#222) — `[elem; count]`, which desugars at parse time into
  an `N`-element array literal (mirroring the type-position `[T; N]` grammar: a strict
  integer-literal count in `0..=65535`, T239 on deviation; the element must be a literal so
  cloning it `N` times equals evaluating it once). It is the readable form that makes a
  256-cell `new()` a one-liner instead of a hand-counted 256-zero list, and it is a pure
  parser addition — `[e; N]` was always a syntax error before, so every existing array
  literal is byte-identical.

---

## 7. Anti-Goals (v1 does NOT build / guarantee)

- **Const generics / a parametric `BoundedVec<T, N>`** — deferred. This type-system change
  (Type-enum extension, numeric-literal type-args, substitution) blocks nothing while the
  family remains monomorphized. Revisit
  ONLY when the slot count exceeds ~5 variants of one type AND the enumeration is
  demonstrably painful.
- **A static `len ≤ N` *type-level* proof.** Boundedness is physical (the backing traps),
  not a refinement — the refinement system is construction-time and does not model the
  mutation `push`/`pop` perform. A tool that needs a compile-time-proven non-overflow must
  guard its own `push` with `is_full()`.
- **Value/move semantics.** A `BoundedVec` copy shares its backing (reference semantics, like
  `Vec`); there is no deep-copy-on-assign and no move-checker. `@Mut` + the region gate carry
  the aliasing discipline.
- **Secure-erase on `pop`/drop.** `pop` decrements `count` and returns the cell; the byte is
  not zeroed (a later `push` overwrites it, and `get` can't reach it). A zeroizing bounded
  buffer for secrets is a separate, future concern.
- **Element types beyond `i64`** — `Str`/`Bool`/`U32` bounded vectors are the next slots in
  the same pattern (the LOCKED plan's 12-module family); not in v1.
- **`BoundedMap` / `BoundedSet` / `BoundedString`** — the same monomorphized-backing pattern
  applied to the other shapes; future (§8).

---

## 8. The Arc Beyond

`BoundedVec_i64` establishes the full pattern — a sealed, fixed-`N`, `Alloc`-free record
whose overflow is a hardware trap and whose integrity is a compile-time seal. The arc
extends it along three axes:

0. **Functional transforms — SHIPPED (Phase 2).** Every `BoundedVec_i64_N` carries the
   eager, i64-only, **`Alloc`-free** pipeline: `map(f)` / `filter(pred)` /
   `filter_map(f: Fn(i64)->Option<i64>)` / `take(n)` → a fresh same-`N` `BoundedVec_i64_N`
   (built via the sealed `::new()`+`push` API, so the result aliases nothing and `count<=N`
   is unforgeable), plus the terminals `sum` / `fold(seed,g)` / `any` / `all` / `find` /
   `zip(other)` / `enumerate()`. `zip`/`enumerate` yield the tuple-element family
   `BoundedPairVec_i64_i64_N` (parallel `fst`/`snd` arrays, `get -> Option<(i64,i64)>`,
   sealed + `Alloc`-free), pulled transitively (and dead-code-eliminated when unused). The
   transforms mirror the Phase-7 `Vec` adapters but never need `cap Alloc` — the inner-ring
   thesis. Anti-goals (v1, no fallback): non-i64 elements, type-changing `map`, cross-size
   `zip`, a `u32` `enumerate` index.
1. **More element types.** `BoundedVec_str_N` / `_bool_N` / `_u32_N` are mechanical repeats
   of this module; they complete the LOCKED 12-module slot family. The `[0; N]` literal and
   the `BoundedVec_<elem>_` prefix trigger already generalize to them.
2. **More shapes.** `BoundedMap<K, V, N>` and `BoundedSet<T, N>` — **SHIPPED (Phase 4)**, the
   same fixed-backing + seal recipe applied to keyed/set shapes. Parallel fixed arrays
   (`keys`/`vals` + `count`) with a count-bounded LINEAR scan (no hashing — that is the
   unbounded `Map`'s job); content key-equality via `str_bytes_eq` for `str` keys (chosen
   when `==` was still pointer-identity; since PR #699 `==` also byte-compares, and the
   helper stays because the certified source is fenced to zero `str ==`). Concrete
   monomorphs: `BoundedMap_i64_i64_64`,
   `BoundedMap_str_str_64`, `BoundedMap_str_i64_64` (`new`/`insert`/`try_insert`/`get`/
   `get_or`/`contains_key`/`len`/`capacity`/`is_empty`/`is_full`); `BoundedSet_i64_64`,
   `BoundedSet_str_16` (`new`/`insert`→bool/`contains`/…). Sealed (T258, structural via the
   `bounded_*` module prefix), region-tracked at `Map` parity (T254), `Alloc`-free, full+new
   force-traps; `try_insert` is the graceful (non-trapping) full path. Anti-goals (v1, no
   fallback): `remove`, `keys()`/`values()` (need a `BoundedVec_str`), `union`/`intersection`
   (set-algebra capacity is ill-defined). `BoundedString` remains future.

Both axes stay **compiler-change-free** (pure stdlib + the now-shipped seal/dispatch/literal
seams) and orthogonal to self-hosting. If the slot enumeration ever becomes painful across
element types, that is precisely the const-generics revisit trigger — not before.

---

## 9. The N-ary atomic airdrop (`batch_transfer`) — SOL-COLLECTIONS Rung C

The Solidity frontend's from-debit **airdrop** (`for (i) { _transfer(msg.sender,
recipients[i], amounts[i]); }`) is the collections story's first *state-mutating* batch: it
sends one holder's balance to N recipients in a single all-or-nothing shot. It reuses the
`BoundedVec` + `BoundedMap` recipe unchanged and adds ONE trusted primitive — no
trusted-compiler change.

- **`BoundedVec_u256_64`** (`stdlib/sigil/bounded_vec_u256.sigil`) — a mechanical `i64→u256`
  clone of §8's sealed vec (T258-sealed `count` = the trustworthy loop bound), minimal API
  (`new`/`len`/`capacity`/`is_full`/`push`/`get`) plus a **trapping `at(i)`** (`i < 0 || i >=
  count ⇒ trap()`) — the cross-module value fetch the primitive iterates with. Capacity **64**
  to match the map (a from-debit airdrop to >64 distinct recipients traps at the 65th key
  regardless — the NC-L1 ceiling, loud never silent).
- **`batch_transfer(self @Mut, from, recipients, amounts) -> bool`**
  (`stdlib/sigil/bounded_map_u256_u256.sigil`, the `transfer_split` sibling) — **atomicity
  WITHOUT rollback at variable N.** SIGIL `trap()` is terminal and does not undo prior storage
  writes, so a naive single-pass loop that traps on leg *k* would leave legs `0..k` committed
  — a partial airdrop. Instead:
  1. **Length guard** — `trap_if(amounts.count < recipients.count)` (faithful to Solidity's
     `amounts[i]` OOB revert).
  2. **Pass 1 — validate on an INDEPENDENT deep clone.** `deep_copy` builds a fresh
     `::new()`-backed map (MI-5: NEVER `let work = self`, which would share the backing and
     corrupt self), then `batch_apply` replays the whole airdrop on the clone. Every
     underflow (`trap_if(fb < a)`), credit-overflow (checked u256 `+`), and capacity
     (`insert`'s 65th-key force-trap) fires HERE — with **self byte-untouched**.
  3. **Pass 2 — trap-free BLIT commit.** `self.count = 0; while j < work.count { copy slot }`
     — direct field writes, **no per-slot `get_or`/`insert` Calls.** This is the
     **MI-FUEL** decision: a *replay* commit would re-run ~14N fuel-decrementing Calls, so a
     fuel trap mid-replay could commit a partial airdrop; the blit's only fuel cost is `count`
     back-edges, minimizing the commit's danger window. HISTORY: the original
     `bt_max_atomic_at_recommended_budget` "empirical proof" was VACUOUS — the ephemeral
     runtime SATURATED fuel instead of trapping, so the check could never fail (see
     docs/specs/forge-fuel-enforcement.md). Since the loop-aware-budget arc the check is
     real: fuel is ENFORCED on the forge path, the WCC `recommended_budget` covers the
     max-N airdrop's measured cost, and the test passes non-vacuously. Note the forge
     path discards the whole execution on any trap (no partial state is observable there);
     the mid-commit exposure that motivated the blit belongs to the ACTOR path (retained
     state + always-enforced fuel) — that audit is a flagged follow-on, not yet done.
- **Aliasing is correct by LIVE-SLOT SEQUENTIAL REPLAY, not pre-computation.** `batch_apply`
  processes the map's live slots one leg at a time (each leg's credit `get_or`-re-reads),
  so a **duplicate recipient** accumulates and a `recipient == from` **self-leg** nets zero
  (but is still underflow-checked before the debit) — exactly as Solidity's per-`_transfer`
  loop does. The tempting `sum(amounts) <= balance` shortcut is UNSOUND: `from=5,
  recipients=[A, from], amounts=[3, 4]` has non-self total 3 ≤ 5 yet Solidity reverts at leg
  1 (`bal[from]=2 -= 4` underflows). Only faithful replay reproduces this (`bt_underflow_self_leg`).

**Divergence ledger (vs `erc20_update`):** a `recipient == address(0)` is credited to
`balances[0]` FAITHFULLY — the plain airdrop has no zero-address sentinel (a source `require(to
!= 0)` translates separately as a surviving `Require`). A zero-amount leg materializes no slot
(NC-L1). >64 distinct recipients trap at the 65th (the map/vec 64-cap; loud).

**The frontend fold is a fixed emit; the recognizer's ONLY soundness duty is the exact-shape
gate.** `recognize_airdrop` (`desugar.rs`) folds the exact `[debit, credit]`-per-leg shape
(loop-invariant + pure `from`, counter-indexed `recipients[i]`/`amounts[i]`, one map, matching
amounts) → `self.<map>.batch_transfer(from, recipients, amounts)`; the surviving
`require(recipients.length == amounts.length)` lowers to a faithful `.len()` runtime `trap_if`
(UP-LENGTH). Every deviation fails CLOSED: a non-`[debit,credit]` body / off-index amount /
per-leg-varying sender → **FE492**; an external-call or `while` loop → **FE401**; an array
type outside a param, or a sized/2-D array → **FE491**; and — the headline soundness item — a
**cap-mode** airdrop whose loop body uses `msg.sender` is caught by the SOL-CAP scanners
(which recurse the raw `AirdropLoop` node, not a `_ => false` catch-all) → **FE454**, so the
authority gate can never silently drop. All aliasing lives in the exec-proven trusted
primitive; the recognizer maps source operands to `batch_transfer` args in fixed positions
(the M-B "aliasing-in-the-primitive" discipline).

**Correctness oracle.** The primitive is proven FIRST and independently: `bt_*` exec cases
(hand-enumerated aliasing/trap classes) + `prop_airdrop_matches_reference` (a proptest fuzzing
the N × collision × underflow space against a Rust live-slot reference) in
`crates/sigil-runtime/tests/bounded_map_u256.rs`, and `sol_airdrop_e2e.rs` runs a *translated*
airdrop end-to-end (real `BoundedVec` inputs, asserted final balances). Anti-goals (v1, no
fallback): the up-front-SUM-debit shape (debit outside the loop) → FE492; a multi-sender
airdrop → FE492; `≥2` maps in the batch → the existing FE412 CEI gate; `while`/general
`for`/`break`/`continue`/nested loops → FE401.

---

## Cross-references

- `docs/specs/regions.md` — T254 region-escape (§5 ET-4).
- `docs/specs/readonly.md` — default-frozen / T251–T253 (the `@Mut` mutators, §6).
- `docs/specs/strings.md` — the sibling COMPLETENESS inner-ring epic; the "trap is the
  floor, no silent corruption" principle `set` inherits (§3).
- `docs/specs/foreign-frontends.md` + `stdlib/sigil/bounded_map_u256_u256.sigil` — the airdrop
  batch primitive `batch_transfer` (§9), its `transfer`/`transfer_split`/`erc20_update`
  sibling family, and the `recognize_airdrop` frontend fold
  (`crates/sigil-frontends/src/solidity/desugar.rs`).
