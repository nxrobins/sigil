# Persistent aggregate actor state

**Status:** Implemented for immutable aggregates, mutable flat fixed aggregates, mutable
`Vec<scalar>`, and — via PPS-0 (`persistent-pointer-state.md`) — mutable `Map<scalar, scalar>`.
Other mutable dynamic or nested shapes remain fail-closed.

## Memory contract

An actor arena is divided conceptually into:

```text
[ durable state slots | persistent reachable objects | transient dispatch tail ]
```

Aggregate state slots contain pointers. After initialization, the runtime captures the actor's
persistent floor above every object allocated while building initial state. Each top-level dispatch
resets the allocation cursor to that floor, reclaiming only the transient tail.

This makes an immutable aggregate initialized once persistent without changing its pointer layout.
A mutable fixed aggregate is also safe when handlers mutate its already-persistent object in place.

## Supported shapes

| Shape | Handler operation | Verdict |
|---|---|---|
| Unmarked record, array, tuple, string, collection, or other initialized aggregate | Read only | Persistent through the initialization floor |
| `mut` record/array/tuple containing only inline scalars | In-place field/index update, or WHOLESALE replacement (PPS-1) | Persistent — in place, or via promotion at the store |
| `mut Vec<T>` where `T` is an inline scalar | Direct state-rooted `push` and reads | Persistent through the state-backed allocation path |
| `mut Map<K, V>` where both are inline scalars | Direct state-rooted `insert` (including rehash) and reads | Persistent through transitive state-backed coloring (PPS-0) |
| `mut str` | Wholesale replacement | Persistent through byte + header promotion (PPS-2a) |
| `mut Vec<T>` / `mut Map<K, V>` where each element (Vec element, Map key/value) is an inline scalar, `str`, or a FLAT scalar record | Direct state-rooted `push`/`insert` and reads; in-place mutation of retrieved record elements | Persistent — scalars by coloring, `str`/records by promotion at the storing `push` (PPS-2b/3). Record keys hash/eq by contents, so promoted copies match fresh probes. Includes the capstone `Map<str, Record>` |
| Mutable nested aggregate, 256-bit aggregate, generic record, an element with a POINTER-BEARING interior (a record containing `str`/`Vec`/record fields), or a nested collection (`Vec<Vec<_>>`, `Map<_, Vec<_>>`) | Any mutation | `C012` — awaits the transitive-walk slice |
| Mutable POINTER-BEARING aggregate (holds a `Vec`/`str`/nested record) | Whole-value replacement in a handler | `T128` — only the storing-push mutation path is promoted |

Inline scalars are `bool`, `i32`, `u32`, `i64`, `u64`, and `f64`.

## Growing state vectors

A state-rooted `Vec<scalar>::push` uses a separate state-backed monomorph instance. Its growth
allocation lowers to the conditional `alloc_persistent` host import, which advances the actor cursor
and raises the persistent floor. Ordinary local vectors keep the normal transient `alloc` path.

The separation is a byte-identity invariant:

- state-free modules do not import `alloc_persistent`;
- the fixed builtin import prefix does not move;
- ordinary `Vec` instances and the certified self-host image remain unchanged;
- only a direct grow through the state field selects the state-backed instance.

Growing through an alias or a mutable parameter is rejected with `T253`, because that receiver would
select a transient allocation path and leave the state header pointing at reclaimed memory. Reads
through aliases are allowed. State-rooted collection values remain taint sinks, so secret pushes
into public state are `T001`. PPS-0 extends all three fences to `Map` receivers and arguments.

## Growing state maps (PPS-0)

A `Map`'s allocations happen in CALLEES — `ensure_buckets` / `grow` / `filled` and their interior
`Vec` operations — not in the routed body, so a single routed instance is not enough. The
state-backed instance therefore raises a monomorph-depth marker for the duration of its body build,
and every generic instance built beneath it (methods AND associated functions such as
`Vec::with_capacity`) inherits the state-backed suffix. Record HEADERS allocate through the same
channel, so a rehash's replacement bucket vectors — header and buffer alike — land below the
persistent floor. `stdlib/sigil/map.sigil` keeps every allocation inside generic-impl code for this
reason: the former `map_filled_i64` free function is now the `Map::filled` method, and
`with_capacity` inlines its fill loops.

## Runtime boundaries

`alloc_persistent` reuses the per-actor arena and its existing exhaustion checks. Persistent growth
is bounded by the arena; exhaustion traps cleanly rather than dangling or crossing into another
actor's arena.

Raising a watermark retains every allocation made earlier in the same dispatch, including transient
scratch created before a persistent grow. This is a bounded space leak, not data corruption, and is
pinned by a canary. Repeated interleaving eventually reaches the arena limit and fails closed.

A replayable restart discards accumulated persistent allocations, reinitializes state, and captures
a new floor. A non-replayable state-preserving path resets to the existing floor. PPS-4 makes the
discard path the RECLAMATION mechanism: a per-actor persistent-heap byte cap turns runaway growth
into a clean distinct trap (`R818`), and under `Restart(n)` the replayed init IS the collector.

## Evidence

- `aggregate_state_persists.rs` covers initialized aggregate persistence and actor isolation.
- `mut_aggregate_state_persists.rs` covers mutable flat fixed aggregates.
- `agg2b_state_vec_persists.rs` and `agg2b_state_vec_capstone.rs` cover vector growth across
  dispatches, multiple doublings, and the watermark residual.
- `agg2b_4_holes.rs` covers alias growth, mutable-parameter growth, taint, and false-positive guards.
- `persistent_alloc_differential.rs` covers the persistent allocation channel and isolation.
- `state_mut_launder_fences.rs` and `state_mut_fences.rs` pin declaration and write boundaries.
- `pps4_restart_as_gc.rs` covers the cap, the distinct exhaustion trap, floor observability, and
  reclaim-by-restart for replay-safe inits.
- `pps5_session_table_capstone.rs` covers the insert-OVERWRITE promotion (the `__set__` storing
  call), 300-dispatch sustained churn with in-place element updates, exhaustion-restart mid-churn,
  and two-table isolation.
- `pps0_state_map_persists.rs` covers map persistence across dispatches, rehash survival,
  interleaved insert/clobber cycles, and two non-aliasing state maps; `pps0_map_fences.rs` and
  `pps0_byte_identity.rs` cover the moved fence and the state-free byte-identity invariants.

## Change rule

A newly admitted aggregate shape must prove that every allocation reachable from its state slot
survives dispatch reset. Direct success is insufficient: aliases, helper calls, taint, restart,
arena exhaustion, and cross-actor isolation require explicit negative or end-to-end tests before a
`C012` fence is relaxed.
