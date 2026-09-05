# Mutable actor state

**Status:** Implemented for the bounded surface below.

## Runtime model

Each actor owns a durable state region at the front of its arena. Actor handlers receive that state
pointer as `VarId(0)`; payload parameters follow it. Initialization writes state fields through the
same layout, and handlers load fields from durable state rather than treating them as closure
captures.

The transient allocation cursor resets after each top-level dispatch. Objects reachable from state
therefore persist only when they are below the actor's persistent floor or use the dedicated
persistent-allocation path. Aggregate details are defined in
[persistent-aggregate-state.md](persistent-aggregate-state.md).

## Language contract

```sigil
actor Counter {
    state { mut count: i64 }
    init(fuel: Fuel) { count = 0; }
    on Increment() { count = count + 1; }
}
```

A `mut` marker is legal only on actor-state fields. A handler may assign a marked field and reads
observe the latest write. An unmarked field remains immutable after initialization.

Mutable state intentionally forfeits schedule-independent quiescent behavior for that actor:
message order may affect accumulated state. Replayable restart reinitializes state; the runtime does
not promise to preserve accumulated mutable values across such a restart.

## Compile-time fences

| Code | Contract |
|---|---|
| `C011` | A mutable field must be plain reassignable data. Capability-, reference-, borrow-, function-, or pointer-bearing mutable fields are rejected so overwrite cannot bypass linear accounting. |
| `C012` | Mutable aggregate shapes are accepted only when their reachable storage is known to persist. Nested/dynamic unsupported forms fail at declaration. |
| `T123` | Handler writes to an unmarked field are rejected, including projected writes and writes through aliases rooted at that field. |
| `T124` | A mutable field is assigned more than once at the top level of `init`. |
| `T125` | A mutable field lacks exactly one unconditional top-level assignment in `init`. |
| `T126` | An actor with mutable state may not return early from `init`; initialization must run to completion. Returns inside nested closures are not actor-init returns. |
| `T128` | A mutable aggregate cannot be replaced wholesale in a handler when the replacement allocation would not persist. Use supported in-place operations. |

State-field writes remain taint sinks. A secret-to-public write is `T001`, including value arguments
to state-rooted collection mutation. Borrow/alias escape and mutation continue to use the existing
readonly/exclusivity fences; adding `mut` does not grant an unrestricted mutable reference.

The state grammar does not admit a refinement `where` clause, so mutable refinements cannot be
expressed without first adding a per-write preservation proof.

## Capability state

An unmarked capability field remains supported as immutable, borrow-only state. `C010` prevents a
handler from consuming that stored capability, and the closure/escape fences prevent laundering it
through another value. Mutable capability state is not supported.

## Evidence

- `state_mut_marker.rs` covers syntax and the targeted marker.
- `state_mut_fences.rs` covers `C011`, `T123`-`T126`, taint, initialization, and fresh reads.
- `state_mut_launder_fences.rs` covers projected writes, aliases, early returns, and aggregate
  boundaries found by adversarial review.
- Actor runtime state tests cover persistence, restart, isolation, and read-after-write behavior.
- The self-host byte capstone ensures state support does not silently move the certified compiler
  image.

## Change rule

Widening mutable state requires all three pieces in one change: a persistence mechanism for the new
shape, a compile-time fence for every unsupported alias/write channel, and an actor-host test across
at least two dispatches. A program that can compile and later read reclaimed bytes is never an
acceptable intermediate state.
