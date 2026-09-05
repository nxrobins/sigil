# Resident actor runtime

**Status:** Implemented.

SIGIL actors can run as resident services while retaining bounded work per dispatch, bounded
per-actor memory, explicit supervision, and deterministic host-fed input.

## Per-dispatch resources

### Fuel

Before each top-level message delivery, the runtime restores the receiver's configured fuel grant in
both the actor ledger and Wasmtime's fuel counter. A synchronous call tree does not refill between
calls, so one top-level dispatch still shares one finite budget. An over-budget handler traps even
though the actor may receive a fresh grant on a later dispatch.

### Arena

Before each top-level delivery, the actor allocation cursor resets to its persistent floor. This
reclaims dispatch-local scratch without touching durable state or persistent objects reachable from
state. Nested calls share the same dispatch arena. Per-actor arena bounds remain enforced.

The state and persistent-floor contract is defined in
[persistent-aggregate-state.md](persistent-aggregate-state.md).

## Supervision

`Restart(n)` supervision performs a real host-side restart up to the declared limit:

1. restore the per-dispatch fuel grant;
2. reset the arena;
3. re-run initialization when its arguments are replayable;
4. increment and audit the restart only after successful recovery.

An initialization that traps during replay fails loudly. Which inits replay is decided at compile
time (PPS-4, restart-as-GC): the compiler marks an init `init_replay_safe` when a fail-closed walk
finds no capability-table operation (draw/split/restrict/mint), no spawn/send/ask, no
extern/grant/effect construct, no capability or actor-ref passed to a helper, and an effects row of
at most `Alloc`. The spawn retains the ordered init-argument handles, and a restart replays the
init with those IDENTICAL handles — the actor is handed the same authority it already holds, so
nothing is re-spent or re-minted, and the replay discards the persistent heap (the collector). An
init that DERIVES from its capability (`power = f.draw(10)`) is not replay-safe: replay would mint
again, so its restart path refills resources and preserves the existing durable state instead —
that heap is deliberately not reclaimed. Entry actors remain `Stop`-supervised.

## Serve mode

`sigil run <source> --serve` bootstraps the entry actor, drains boot messages, then reads stdin one
line at a time until EOF. Each valid line becomes a host-enqueued message for a handler taking one
`i64` or `bool` parameter.

- `--on <handler>` selects the target. Without it, the sole non-`Start` compatible handler is used.
- Handler shape and lowered Wasm parameters are validated before any input is consumed.
- Invalid UTF-8 or unparsable scalar lines are skipped and counted.
- A line is capped at 64 KiB; an overlong unterminated line fails loudly.
- On a full queue, the host drains and retries once. It never grows the queue without bound.
- No actor ABI import was added; the host uses the existing message-enqueue API.

The loop is deterministic with respect to its byte input. It introduces no actor-visible clock or
randomness.

## Boundaries

- Resident execution does not make a single dispatch unbounded.
- Replayable restart reinitializes mutable state; accumulated values are not durable across that
  restart.
- Capability-initialized actors replay when their init is compile-time replay-safe (store-only
  bodies); deriving inits preserve state rather than replay.
- Serve mode accepts only one scalar line argument. Structured input, sockets, timers, and
  multiplexed sources are outside the current interface.
- Wall-clock scheduling fairness is not a language guarantee.

## Evidence

- `actor_live_fuel_refill.rs` proves long-lived dispatches and shared nested-call fuel.
- `actor_live_arena_reset.rs` proves scratch reclamation and per-dispatch bounds.
- `actor_live_restart.rs` proves clean replay, capability-init handling, restart limits, and
  fail-loud reinitialization.
- `pps4_restart_as_gc.rs` proves the restart-as-GC posture: cap exhaustion → distinct trap →
  replayed init reclaims the heap; deriving inits preserve state and never re-mint.
- `actor_live_serve.rs` proves stream completion, malformed-line handling, deterministic results,
  startup type validation, and the line cap.
- Mutable and aggregate state suites prove that the arena reset preserves the persistent floor.

## Change rule

Any new resident input source or resource lifetime must preserve top-level-only refill/reset,
bounded queues and input, fail-loud supervision, and the persistent-state floor. Host-side
convenience must not create a new guest authority channel implicitly.
