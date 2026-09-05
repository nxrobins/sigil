# Persistent Pointer-Bearing State — `Map` / `str` / `Vec<aggregate>` across dispatches

**Status:** EPIC COMPLETE — PPS-0 through PPS-5 SHIPPED (capstone landed 2026-07-29). This is the planning artifact for the epic that closed the
remaining C012 fence: `mut` actor-state shapes that carry POINTERS (`Map`, `str`,
`Vec<aggregate>`, nested aggregates) surviving message dispatches. Scoped 2026-07-28 against
the persistent-aggregate-state arc (AGG-1 → AGG-2b, on the mainline).
**Lineage:** the name "persistent collection heap" belonged to the PREDECESSOR epic — AGG-2b's
`mut Vec<scalar>` slice (ratified 2026-07-19, B1 floor-raise; complete via AGG2b-0…4 and its
journal retired per the repository-canonicalization hygiene rule). This spec scopes the half
that epic explicitly deferred, under a fresh name so the retired journal stays retired.
**Depends on:** the persistent-aggregate-state arc — SATISFIED: its persistent floor,
`alloc_persistent` channel, and C012 fence (`docs/specs/persistent-aggregate-state.md`) are
in-tree; every slice below builds on them.
**Authors:** Nigel Robinson · Claude

---

## 1. Problem statement

The AGG arc made actor state real for exactly the shapes whose persistence needs ONE
allocation stamp:

| Persists today (branch) | Mechanism |
|---|---|
| non-`mut` aggregates of any shape | allocated in `init`, below the persistent floor (AGG-1) |
| `mut` record/array/tuple of inline scalars | mutated in place in already-persistent storage (AGG-2a) |
| `mut Vec<scalar>` | grow-`push` routes to a state-backed mono instance whose growth lowers to `alloc_persistent`, raising the floor (AGG-2b) |

Everything else is fenced fail-closed at the state-field seam
(`type_check/universe.rs::check_state_field_types`, C012): a `mut` **nested aggregate**,
**`Map`** (5 nested Vecs), **`str`**, **256-bit aggregate**, or **`Vec<aggregate>`** "needs
per-element persistent allocation the single-header stamp does not cover — the remaining
fenced half." (C011 separately fences cap/ref-bearing `mut` fields and is NOT in scope here.)

The qualitative jump: a `Vec<scalar>` buffer is one flat allocation, so one recolored grow
path suffices. A `Map` or `Vec<record>` is a **reachable subgraph** — interior pointers to
child allocations made at arbitrary program points, possibly deep inside helper functions.
Persistence must hold for **every allocation reachable from the state slot**, which is exactly
the branch spec's Change rule. This epic is that rule, mechanized.

## 2. Design center

Two complementary mechanisms, mirroring `docs/memory-model.md`'s actor-message result
("mutable payloads copy; frozen payloads share; the type system says which") one level down —
**storing into actor state is a promotion boundary**, the same kind of boundary `send` is:

1. **State-backed coloring** (generalizing AGG-2b): stdlib-internal allocations performed BY a
   state-rooted collection's own methods (a `Map`'s rehash building new bucket Vecs, a
   state-rooted `Vec<scalar>` growing) route to `alloc_persistent` via state-backed monomorph
   instances. This is static, zero-copy, and already proven for one collection; slice PPS-0
   extends it to `Map`'s five inner Vecs.
2. **Promotion at the store boundary** (the new primitive): a value CONSTRUCTED anywhere
   (dispatch arena, helper function — its provenance is transient) that crosses into actor
   state (`state_vec.push(record)`, `state_map.insert(k, v)`, `state.field = new_str`) is
   **deep-copied into the persistent heap at the crossing**, by a compiler-generated,
   monomorphized `promote<T>` walk over the record layout. Static coloring cannot reach these
   cases — user code builds values through arbitrary call chains, and proving persistent
   provenance through those chains IS the deep-aliasing/borrow-checking remainder. Promotion
   is sound today; provenance-typed zero-copy construction (`Record::in_region(actor_heap)`,
   the memory-model's "region-polymorphism is the default") is the LATER optimization, not the
   v1 gate.

Non-mechanisms, explicitly rejected:
- A dynamic "currently mutating state ⇒ all allocs persistent" mode bit — pins transient
  scratch forever, unbounded space, semantically blind. No.
- A tracing collector — the memory-model's Layer-3 verdict stands ("build approximately
  never"); reclamation posture is §5.

## 3. Slice ladder

Each slice lands independently, relaxes C012 for exactly one shape family, and must satisfy
the branch spec's Change rule: aliases, helper calls, taint, restart, arena exhaustion, and
cross-actor isolation each get explicit negative or end-to-end tests BEFORE the fence moves.

**PPS-0 — `Map<scalar, scalar>` state fields. ✅ SHIPPED.** Reuse the AGG-2b pattern on `map.sigil`'s
internals: a state-rooted Map's five inner Vecs become state-backed instances; rehash
(construction of REPLACEMENT inner Vecs inside Map methods) allocates persistent. No promotion
machinery needed — Map's interior pointers are all stdlib-authored. Exit: counters/indexes as
`mut Map<i64, i64>` state; rehash across dispatches; alias-insert rejected (T253 family);
exhaustion traps clean; isolation canary.

**PPS-1 — the promotion primitive + whole-value replacement. ✅ SHIPPED (flat aggregates).** Compiler-generated
`promote<T>`: monomorphized structural deep copy of tree-shaped values into the persistent
heap, invoked implicitly at state-store boundaries. Relax T128 (whole-value replacement of a
`mut` aggregate state field) — replacing state with a freshly-built-then-promoted value is the
natural functional-update idiom and becomes legal exactly here. Semantic note to document
loudly: promotion DUPLICATES shared substructure (records have reference semantics; a value
stored twice promotes twice). Interior aliasing that must stay shared uses the memory-model's
arena-of-nodes + integer-index pattern instead. Exit: replace a `mut` record state field from
a helper-built value across dispatches; the promoted copy survives arena reset; the transient
original dies; double-store duplicates (pinned by test, documented).

**PPS-2 — owned `str` in state. ✅ SHIPPED — 2a (`mut str` fields) and 2b (string-KEYED maps).** Promotion of byte buffers (a `str` is ptr+len; promote =
copy bytes persistent + rewrap), unlocking `mut str` fields and — with PPS-0 — string-KEYED
maps (`Map<str, V>` insert promotes the key). Exit: a `mut str` field replaced every dispatch;
`Map<str, i64>` session-table pattern; taint preserved through promotion (T001 family holds).

**PPS-3 — record elements in collections. ✅ SHIPPED (flat elements; transitive walk deferred).**
Pushing a record into state promotes it by PPS-1's field copy at the storing push; state-rooted
element ACCESS returns pointers into the persistent heap, and in-place mutation of those
elements is AGG-2a-legal (already-persistent storage). Shipped: `Vec<str>`, `Vec<Record>`,
`Map` with record keys AND values (flat scalar records only), the capstone-shape
`Map<str, Record>`. Deferred with fences: elements with POINTER-BEARING interiors (records
containing str/Vec/record fields) and nested collections (`Map<i64, Vec<i64>>`) — those need
the transitive subtree walk.

**PPS-4 — reclamation posture (the honest one). ✅ SHIPPED.** Abandonment is bounded for
monotone growth (doubling waste ≤ live size) but UNBOUNDED for replace-heavy state (a `str`
replaced per dispatch abandons every predecessor). v1 posture, formalized rather than
hand-waved: per-actor persistent-heap byte cap (grant-shaped knob) → exhaustion traps clean
and DISTINCT (R818) → **supervised restart IS the collector**: the restart discards the heap
and REPLAYS a compile-time replay-safe `init` with retained handles. "Let it crash" as memory
management — Erlang's per-process-heap-freed-on-death, made literal. A free-list or compacting
promotion pass is the named follow-on IF real workloads outgrow restart-as-GC. Shipped exit:
exhaustion → clean trap → restart → sane state (proven end to end); the cap and current floor
are observable; the abandonment math is documented per shape (as built, below).

**PPS-5 — capstone. ✅ SHIPPED.** A resident session-table actor: `mut Map<str, Record>` (string
keys, record values), hundreds of dispatches of insert/update/replace, interleaved transient
scratch, restart clears, exhaustion handled, cross-actor isolation held — the AGG-3 ledger's
successor, proving "actor state is USEFUL," not just "actor state persists." Landed with a REAL
bug found on arrival (the insert-OVERWRITE promotion hole; as built, below)."

Sequencing: PPS-0 is independent and highest value-per-risk; PPS-1 unlocks 2 and 3; PPS-4 can
land any time after PPS-0; PPS-5 requires all.

### PPS-5 as built (2026-07-29)

The integration slice: no new admission, one real fix, and the epic's exit proof.

**The hole the capstone caught on arrival.** A map insert on an EXISTING key overwrites via
`self.vals.set(self.vidx.get(s), val)` — a STORING call, but not a `push`. The PPS-2b/3
promotion was armed only at `__push__` callees, so an overwritten str/record value stored a
TRANSIENT pointer into persistent storage and dangled after the dispatch (probed: baseline
insert-then-read passes; overwrite-then-clobber-then-read traps, floor pinned at the
pre-overwrite value). Every prior slice's runtime tests inserted DISTINCT keys, so the
overwrite path — half the words in "insert/update/replace" — had never been executed with
pointer-bearing values. The fix is one line of the same rule: promote at the innermost storing
call, now `__push__` OR `__set__` on a `$state`-suffixed callee (the transitive coloring
already names the overwrite path's `vals.set` instance `$state`). The control (fix reverted)
reproduces the dangle; `overwrite_of_pointer_valued_entries_persists` pins both value kinds.

**The exit proof** (`pps5_session_table_capstone.rs`): a resident `Map<str, Session>` actor
survives 300 dispatches in three phases over 100 runtime-built f-string keys — insert, then
in-place update THROUGH the retrieved element pointer (`s.hits = s.hits + 1` inside the match
arm — AGG-2a on a promoted element), then whole-value replace (the `__set__` path) — with
transient scratch built BEFORE every promoting store (the adversarial order that strands
scratch below the raised floor; 300 dispatches of that residual budget-tested against the 64KB
arena, and the 16-element variant overflows it exactly as the abandonment math predicts).
Replace-heavy churn on one hot key under a 4KB cap exhausts, restarts (replay-safe store-only
init), and keeps serving — last write wins across restarts. Two session tables on one host
stay disjoint under interleaved churn.

**Epic verdict.** The long-lived state model the epic was scoped to deliver now holds for the
session-table shape end to end: string keys, record values, all three mutation verbs, scratch
interleaving, bounded reclamation, isolation. The remaining fenced territory (pointer-bearing
record interiors, nested collections — the transitive walk) and the deep-aliasing remainder
stay documented fences, not silent gaps.

### PPS-4 as built (2026-07-29)

The reclamation posture, made mechanical. Three pieces:

**The knob.** `RuntimeHost::set_persistent_cap(bytes)` / `--persistent-cap` — a per-actor
persistent-heap byte cap, default the arena size (64 KB, no behavior change until lowered),
clamped to it. A persistent allocation that would raise the actor's floor past the cap traps
with the DISTINCT `PersistentHeapExhausted` error (R818: actor, requested bytes, would-be
floor, cap) instead of the generic arena message — checked before the arena bound so the
restart-as-GC path gets its own diagnostic. Observability: `persistent_bytes(actor)` (floor −
arena base) and `persistent_cap()`.

**The collector.** Under `Restart(n)`, the exhaustion trap routes into the existing AL-3
restart, which now REPLAYS cap-init actors too: the spawn retains the ordered init-argument
handles (`ActorInstance::record_init_caps`), and the restart rebuilds the argument vector via
the same `build_init_args` and re-runs `init` after resetting the cursor to
`arena_base + state_size` — the heap is discarded, state is rebuilt at birth, a new floor is
captured. Replaying with the retained handles moves no authority: the actor is handed the same
caps it already holds, so nothing is re-spent or re-minted (pinned by the retargeted
`restart_of_stateful_cap_init_actor_does_not_respend_state_cap`, whose assertions survived
verbatim while its rationale changed).

**The replay-safety line, drawn at compile time.** AG-AL7's blanket fence ("cap-init actors
never replay") existed because replaying an init that DERIVES from its cap — `power =
f.draw(10)` — would mint a second sub-cap. That is a property of the init BODY, so the
compiler now computes `RuntimeActorSpec::init_replay_safe` with a fail-closed walk over the
typed init: fenced outright are the cap-table ops (draw/split/restrict/mint), spawn/send/ask,
extern/grant/effect constructs, any call passing a capability- or actor-ref-typed argument,
and ANY unrecognized construct (`_ => false` — a future AST variant pessimizes GC, never
unsounds it); a second gate requires the init's effects row to be at most `Alloc` (the
transitive summary that catches a cap-arg-free helper doing extern work). Store-only inits —
the canonical PPS shape — pass; deriving inits keep the preserve-state path and their heap is
deliberately NOT reclaimed, the honest boundary.

**Abandonment math, per shape** (waste = persistent bytes unreachable from state):

- *Monotone `Vec`/`Map` growth*: doubling abandons every predecessor buffer; the sum of
  predecessors is < the live buffer, so waste < live and total footprint ≤ 2× live. Bounded —
  the cap only fires when live data itself approaches the cap.
- *Map rehash*: abandons the old bucket trio (keys/vals/hashes); same doubling bound.
- *Replace-heavy `mut str`* (and map-value overwrite churn): EVERY replacement abandons the
  predecessor's payload+header, so waste grows linearly with dispatch count — unbounded.
  Dispatches-to-exhaustion ≈ (cap − birth bytes) / bytes-replaced-per-dispatch; the trap +
  restart then reclaims everything above birth.
- *Watermark residual*: transient scratch allocated before a persistent grow in the same
  dispatch is stranded below the raised floor (the documented bounded leak); the restart
  reclaims it with everything else.

### PPS-3 as built (2026-07-29)

Record ELEMENTS in state collections are admitted — `Vec<str>`, `Vec<Record>`, `Map` record
keys and values (flat scalar records), and the epic's capstone shape `Map<str, Record>` — plus
the resolution of PPS-2b's `Vec<str>` tombstone.

**The tombstone first, because it reshaped the slice.** `Vec<str>` state trapped during PPS-2b
despite the storing-push promotion existing. A probe proved plain (non-state) `Vec<str>` works,
which localized the fault: ADMISSION/ROUTING DRIFT. The C012 seam admitted `Vec<str>` but the
routing gate in `methods.rs` still required a SCALAR element, so a state `Vec<str>` never routed
to a `$state` mono instance at all — its buffer grew on the transient channel AND the storing
push (the promotion site) never got the `$state` suffix that arms promotion. One cause, two
symptoms, zero new mechanism needed. The fix makes both gates consume the same predicate
(`universe::is_persistable_scalar_vec`), so they cannot drift again; the lesson generalizes to
"admission and routing must share their predicate, structurally."

**Record elements needed one genuinely new step**: `lower_call_expr` now promotes a flat-record
argument to a `$state`-suffixed `__push__` callee via `promote_flat_aggregate` (PPS-1's field
copy, aimed at the innermost storing call exactly as PPS-2b aimed `promote_str`). Everything
else falls out of composition: element GET returns a pointer into the persistent copy, so
in-place element mutation is AGG-2a on already-persistent storage (pinned by test); promotion
still COPIES (mutating the transient original after the push does not change the stored
element — pinned).

**Record KEYS came along free, deliberately.** The stdlib map is trait-based —
`key.hash()` / `stored.eq(key)`, both CONTENT functions — so a promoted key copy still matches
probes built fresh from the same field values (pinned by runtime test). Hashability is the
trait Wall's business, enforced in mono for state and non-state maps identically, so C012 does
not re-gate it.

**The line after this slice**, and why: promotion is PPS-1's straight-line field copy — it
duplicates exactly the fields the registry lists. A record whose field is itself a pointer
(str/Vec/record interiors) would be copied SHALLOWLY and dangle; those stay C012-fenced
(`pps3_record_element_fences.rs`), as do non-record aggregate elements (`Vec<Vec<i64>>`,
`Map<i64, Vec<i64>>`), which have no field registry to copy from. Reaching them is the
transitive-walk follow-on, not this slice. (Amusing moat: the UNSPACED `Vec<Vec<i64>>` spelling
doesn't even parse — `>>` lexes as one token — so the spaced form is what the fence pins.)

Change-rule carries: taint joins into a record at construction and survives the field copy
(@Secret-bearing record into public state is T001); the alias/dangle gates (T253) and
wholesale-replacement fence (T128) cover record-element collections. The C012 message, registry
hint, and five prior fence tests were retargeted at the new line.

### PPS-2a as built

`mut str` actor-state fields are admitted; a wholesale replacement in a handler promotes.

A `str` is a fat pointer — an 8-byte header (`data_ptr@0`, `len@4`) over bytes allocated
elsewhere — so promotion has to move BOTH halves, and the payload's length is a RUNTIME value.
That is the one thing PPS-1's straight-line field copy could not express, so this slice adds a
single AIR statement, `PromoteBytes { dst, src, len }`: allocate `len` bytes on the persistent
channel, then `memory.copy` into them. The str case then composes — promote the payload, allocate
a persistent header, write `data_ptr`/`len` over the copy. Still no loop and no recursion; the
wasm layer already had bulk-memory (message deserialization uses it).

Promoting only the header would have left the field pointing at reclaimed bytes; the
sliced-string test is the one that would catch it, since a substring's payload points into a
buffer the promotion does not otherwise touch.

Fences: `mut str` leaves C012 and T128 (replacement is a `str`'s only update form, since strings
are immutable). Taint survives the byte copy — storing a `@Secret` str into a `@Public` state
field is still T001. A record CONTAINING a str, `Vec<str>`, and `Map<str, _>` all stay fenced.

### PPS-2b as built

`Map<str, V>` and `Map<K, str>` state fields are admitted; the session-table pattern works.

The promotion boundary is the new thing. Everything before this promoted at a STATE STORE — a
place the compiler can see a transient value crossing into persistent storage. A map insert has
no such store: it mutates the map in place, and the key's bytes enter storage deep inside the
stdlib. The rule that resolves it: **promote at the innermost STORING call**, i.e. a `str`
argument to a `$state`-suffixed `Vec::push`. `Map<str, V>::insert` therefore promotes exactly
once, at `keys.push(key)`, rather than once per frame on the way down — and a read path
(`get`/`contains`) promotes nothing, so lookups allocate no persistent bytes.

The gate is `callee.ends_with("$state") && callee.contains("__push__")` over the mangled name,
with the argument's own type deciding (only `str` args promote). Mangled-name matching is a real
fragility; the end-to-end tests are what pin it, and any drift in the mangling scheme fails them
loudly rather than silently disabling promotion.

`Vec<str>` state was probed during this slice and **traps** — promotion at the storing push is
not by itself sufficient for a directly-state-rooted `Vec<str>`. It stays fenced, with a
tombstone test (`vec_of_str_state_stays_fenced_pending_pps3`) so the fence is deliberate rather
than an omission, and PPS-3 owns finding out why.

**PPS-2b (superseded by the section above): string-KEYED maps.** `Map<str, V>` needs the key's bytes
promoted at `keys.push(key)` INSIDE the stdlib insert path — a promotion boundary inside colored
code, not at a state store. That is a genuinely different mechanism from everything above, which
is why it is now its own slice rather than the back half of this one. `PromoteBytes` is the
primitive it will use.

### PPS-1 as built (2026-07-28)

Shipped for FLAT FIXED aggregates — records/arrays/tuples of inline scalars — which is the slice's
exit criterion (a helper-built record replacing a `mut` state field, persisting across dispatches)
and the foundation PPS-2/3 extend.

The primitive turned out to need no new AIR statement and no wasm change: a handler's wholesale
aggregate store lowers to a `BumpAlloc { persistent: true }` plus a fixed sequence of
LoadField/StoreField pairs driven by the field registry's own offsets. Layout stays
single-sourced, the copy is straight-line (no loop, no recursion, no runtime size), and the
existing conditional-append `alloc_persistent` import carries it. `init` lowering is untouched —
it already allocates below the persistent floor — so its bytes are unchanged.

Semantics, pinned by tests rather than left implicit: promotion COPIES. The transient original
keeps its own identity (mutating it after the store does not move the state field), and one value
stored into two fields promotes twice. This is the documented exception to the language's
reference semantics, and it is exactly the behavior the "arena-of-nodes + integer indices" pattern
exists to work around when sharing must be preserved.

Fences moved with the shape: T128 now admits flat aggregates and rejects pointer-bearing ones with
a message naming the reason. The AGG-2a `wholesale_reassign_…_is_t128` assertion inverted, and the
adversarial sweep's entire `wholesale-reassign` family (8 fixtures) flipped from fenced to
`COMPILES_CLEAN_SOUND` — every one stores a flat aggregate. Wholesale replacement of a state `Vec`
or `Map` stays T128: those are pointer-bearing, so a shallow copy would dangle.

Not yet reached (PPS-2/3): transitive promotion. A record holding a `Vec`, a nested record, and a
`str` still fail closed, because a shallow copy would leave their interiors in per-dispatch
scratch.

### PPS-0 as built (2026-07-28)

Landed as designed, with two mechanisms the scope anticipated only in outline:

1. **Transitive coloring.** A state-rooted mutating `Map` call routes to a state-backed instance
   AND raises a monomorph-depth marker for its body build; every generic instance built beneath it
   inherits the suffix. This covers methods and — the hole the rehash test caught —
   ASSOCIATED functions, so `Vec::with_capacity`'s pre-sized bucket buffer is persistent too.
2. **Persistent record headers.** `BumpAlloc` gained a `persistent` flag (set from the instance
   name, honored at the wasm layer) because a rehash REPLACES interior `Vec` headers, which are
   record constructs rather than `alloc` intrinsics — a channel AGG-2b never had to touch.

`map.sigil` was restructured so every allocation lives in colorable generic-impl code
(`map_filled_i64` → `Map::filled`; `with_capacity` inlines its fill loops). No promotion primitive
was needed, exactly as the design predicted for this slice.

Fences moved with the shape: the `T253` alias/`@Mut`-parameter dangle gates and the taint sink now
cover `Map` receivers and arguments, and AGG-2b's "Map stays fenced" assertion was replaced by the
new boundary (`Map<str, _>` and aggregate keys/values remain `C012`).

## 4. Invariants preserved (non-negotiable)

- **Byte identity for state-free code**: modules that never touch actor state import no
  `alloc_persistent`, the fixed builtin-import prefix does not move, ordinary `Vec`/`Map`
  instances and the certified self-host image are byte-unchanged (the AGG-2b invariant,
  extended to every slice).
- **The ephemeral tool path is untouched**: `execute_ephemeral`, the bench corpus, and every
  `sigil forge` tool see zero behavioral or byte difference.
- **Determinism** (I3/I6): promotion order and heap layout are deterministic; compile twice,
  byte-identical.
- **Fail-closed default**: shapes not yet admitted by a landed slice STAY C012; no slice may
  widen by accident (the fence test matrix grows with each slice, never shrinks).
- **Bounded work**: every promotion is O(size of the promoted value); the persistent heap is
  capped; exhaustion is a clean trap, never a dangle or cross-actor write.

## 5. Explicitly out of scope

- Persistent 256-bit aggregates (`u256` state) — small, but rides after PPS-1 mechanically;
  not called out as its own slice.
- Provenance-typed zero-copy state construction (`in_region(actor_heap)` at the surface) —
  the optimization that removes promotion copies; blocked on the deep-aliasing/borrow
  remainder and DEF-3 capabilities-as-values. The promotion ABI is designed so this can
  arrive later as a pure optimization (same boundary, copy elided when provenance proves
  persistent).
- Free-list / compacting reclamation — named follow-on to PPS-4, demand-driven.
- Mailbox persistence policy, actor I/O (grants into `RuntimeHost`), timers, threading — the
  RUNTIME half of the production story, tracked separately; this epic is the memory half.

## 6. Open questions (to resolve in PPS-0/1 design review)

1. **Promotion of `Vec` inside promoted records** — promote the buffer eagerly (simple, full
   copy) vs. lazily on first state-rooted grow (cheaper, more machinery). Lean eager: the
   Change rule's test burden favors the simple invariant "everything reachable from state is
   persistent, immediately."
2. **`promote<T>` emission site** — per-monomorph generated function (like the state-backed
   instances) vs. inline expansion at each store site. Lean generated function: one body to
   verify per shape, smaller wasm.
3. **Diagnostic surface** — whether promotion is silent (it is semantics, like `send`'s copy)
   or carries an informational lint at store sites (the T252-style honesty channel). Lean
   silent + documented, with the lint available behind the existing warning channel if agent
   feedback wants it.

---

*Grounding: `check_state_field_types` (universe.rs, branch) for the exact fence;
`docs/specs/persistent-aggregate-state.md` (branch) for the floor/watermark/`alloc_persistent`
machinery, restart semantics, and the Change rule; `stdlib/sigil/vec.sigil` (`alloc` handle
field) and `docs/specs/regions.md` (DEF-2a/2b) for the allocator seams this epic generalizes;
`docs/memory-model.md` §Layer 2 and §Actor messages for the promotion-boundary design center.*
