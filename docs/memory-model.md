# SIGIL Memory Model — Design Note (north star)

**Status (updated 2026-07-28):** North star, now substantially REALIZED. This note was written
when nothing below was built; it has since been executed in two arcs, and the design held:

- **The ownership/discipline half SHIPPED** as the default-frozen arc (PRs #175–#209, June 2026):
  mutation-as-capability → default-frozen (`@ReadOnly`/`@Mut`, T251–T253), lexical regions with
  real runtime reclamation and the escape gate (DEF-2a, T254), region polymorphism — `@in r`,
  the outlives lattice, `Vec::in_region(r)` / `Map::in_region(r)` (DEF-2b), and call-site
  exclusivity (DEF-2c, T255). See `docs/specs/{readonly,regions,exclusivity}.md` and
  `docs/sigil-roadmap-alignment.md`. The documented boundary is the deep-aliasing remainder
  (AG-1 remote / AG-4 through-return), to be closed by borrow checking at the region seam.
- **The actor-state half has largely landed** via the persistent-aggregate-state arc
  (AGG-1 → AGG-2b) and the persistent-pointer-state epic (PPS-0…3): immutable aggregates,
  `mut` flat aggregates, `mut str`, and `mut Vec`/`Map` collections whose elements are
  scalars, `str`, or flat scalar records (including `Map<str, Record>`) now persist across
  message dispatches via the persistent floor, the state-backed `alloc_persistent` channel,
  and promotion at the storing write; every not-yet-covered mutable shape (pointer-bearing
  record interiors, nested collections, 256-bit elements) fails closed under C012. See
  `docs/specs/persistent-aggregate-state.md`.
- **The reclamation posture is mechanical** (PPS-4): a per-actor persistent-heap byte cap
  turns runaway growth into a clean distinct trap (R818), and under `Restart(n)` supervision
  the restart IS the collector — it discards the heap and replays a compile-time replay-safe
  `init` with retained capability handles. Replace-heavy state is bounded by the cap;
  monotone growth wastes at most its live size.
- **The persistent-pointer-state epic is COMPLETE** (PPS-0…5, July 2026): the capstone
  session-table actor — `mut Map<str, Record>`, hundreds of insert/update/replace dispatches,
  scratch interleaving, exhaustion-restart, isolation — runs end to end. What remains fenced
  (pointer-bearing record interiors, nested collections) is a documented C012 line with a named
  follow-on (the transitive walk), not a gap — `docs/specs/persistent-pointer-state.md`.
- The one forward-compat residue this note asked for — the `Vec` allocator-handle field — landed
  and is now load-bearing twice over (`Vec::in_region` and the state-backed grow path).

The body below is preserved as the design rationale; its stress-test results stand, and the
"Implications for today" section is retained as the historical record of a bet that paid off.
The core idea was **stress-tested across four axes** (closures, actor messages, generics,
supervision/restart) and held on every one — each time by reusing or mirroring machinery SIGIL
already has.

---

## The problem

SIGIL has two memory regimes today, one fine and one missing:

- **Ephemeral tool mode (the current target):** a tool allocates, runs, and exits; the OS reclaims
  everything. Leaking until process exit is *free and correct*. The growable `Vec<T>` that doubles
  without freeing is fine here — leaked prior generations die with the process in milliseconds.
- **Indefinitely-running programs (actors, servers):** a `Vec` (or any growing structure) that
  never frees leaks unboundedly — roughly 3× memory for a fully-grown vector, forever.

Underneath is a deeper gap: SIGIL has **no ownership/lifetime discipline**. Records are shared heap
pointers with reference semantics (`let b = a; b.push(x)` mutates `a`). Unrestricted aliased
mutation of heap state is in quiet tension with SIGIL's entire reason to exist — the
capability / constant-time / taint guarantees. The borrow checker is what Rust built to tame
exactly this; SIGIL has nothing.

## The thesis

> **Arenas by default, regions when you need hierarchy, tracing only when you need cycles — and all
> of it is a capability, not invisible runtime magic.**

The move that makes this SIGIL-native rather than bolted-on Rust: **allocation lifetime becomes a
capability** — visible in the type signature, composable with the existing cap model, enforced by
the type system. This is not merely memory management. It is the **ownership system SIGIL was
missing**, and the thing that makes the security thesis whole
([below](#why-this-completes-the-security-thesis)).

## The governing principle: annotate decisions, derive consequences

SIGIL is an **agent-authored** language. That single fact resolves the tradeoff every region system
agonizes over (explicit lifetimes vs. inferred). "Verbose to write" is a *human* cost; an agent
won't complain, it'll comply. So the axis to optimize is not brevity — it's **single-source-of-truth
and machine-checkability.** That gives a sharp rule:

- **Decisions are explicit.** "Allocate in the caller's region," "this function returns into region
  `r`," "this value must die by the request deadline" — these are choices the author makes. Make
  them explicit and go *maximal*; verbosity is free, so there's no reason to hide a decision behind
  inference.
- **Consequences are derived (inferred).** Some facts are not decisions — they are mechanical
  consequences of the code. A closure's region is the meet (shortest) of the regions it captures
  from. You do not *decide* that; it falls out of the body. Forcing the author to *restate* a
  derived fact is strictly worse than computing it, even for a tireless agent: a hand-written
  derived fact is either **redundant** (the compiler had to compute the truth to check it, so the
  annotation added nothing) or **unsound** (the compiler trusts it, and a wrong value is a dangling
  pointer the type system just "blessed"). It also goes stale on every edit, and it doesn't even
  survive generic composition — `compose(f, g)`'s region depends on the actual `f`/`g`, so it
  becomes a region *variable* unified at the call site, i.e. inference by another name.

So inference in SIGIL isn't a concession to lazy humans — it's the correct *placement* of derived
facts. **Explicit where it's a decision (free for agents, maximal), inferred where it's a
derivation (one source of truth).** This is cleaner and more defensible than "explicit lifetimes"
or "inferred lifetimes," because it explains *why* the line falls where it does.

## Reframe: two mechanisms, not three

An arena is a *flat* region; a region hierarchy is *nested* arenas. The first two layers below are
the **same primitive** — bump-allocate, bulk-free-on-scope-exit — at different nesting depths. The
real architectural boundary is:

1. **Scoped bulk-free** (arenas/regions): one allocator that can nest. Zero per-object cost; free is
   a pointer reset.
2. **Tracing** (a GC): a fundamentally different runtime. Probably avoidable indefinitely.

The hard work is *one* allocator + *one* type-system discipline, then optionally a collector much
later.

---

## Layer 1 — Arena-scoped allocation (the cheap, partial win)

Each cycle (a request, a message, a compile pass) gets a bump allocator: `alloc(n)` bumps a pointer;
a `Vec` doubling leaves the old buffer in the arena (it dies in milliseconds); on scope exit the
pointer resets and everything is gone in one operation, zero per-object cost. **The arena is a
capability** available implicitly within its scope.

**The hard part it glosses — escape / promotion.** Returning or storing a heap value *beyond* the
arena requires either a deep copy out, or having allocated it in a longer-lived region to begin
with — moving "the header" of a `Vec` isn't enough, its buffer lives in the dying arena. So Layer 1
alone only covers the stateless "compute-and-return-a-value" case; the instant you mutate
longer-lived state with shorter-lived data (`self.connections.push(conn)`), you are in Layer 2.

## Layer 2 — Region hierarchy (the heart)

```
Server     (until shutdown)
└─ Session    (until client disconnects)
   └─ Connection  (until TCP close)
      └─ Request     (until response sent)
         └─ Handler arena  (until handler returns)
```

Each level is a region; allocations die when their region ends. The safety rule: **a value may
reference its own region or any *parent* (longer-lived) region, never a *child* (shorter-lived,
already-dead) region.** Point up the hierarchy, never down.

```sigil
fn process_batch(r: &Region, items: &[Item]) -> Summary {
    let mut accum = Vec::in_region(r);
    for item in items { accum.push(transform(item)); }
    return summarize(accum);
}   // accum dies when r's region ends
```

The compiler's job is a **region-outlives checker** — a simplified, *explicit* `'a: 'b`, where the
author passes the region. Per the governing principle, the verbosity of threading `&Region` is **not
a cost** for an agent author — so SIGIL goes explicit on these (they're *decisions*) and reserves
inference for the one place it's a *derivation*: closure capture regions.

**Promotion is resolved by the agent-language framing.** The classic crux — "deep-copy on escape
(slow)" vs "region-polymorphize everything (verbose)" — only forced the copy because the verbosity
was unpalatable to humans. For agents it's free, so **region-polymorphism is the default**: pass the
target region in, allocate-in-place, copy almost never. Deep-copy promotion becomes the rare
fallback, not the norm.

## Layer 3 — Capability-gated tracing (the nuclear option — probably avoidable)

```sigil
cap type TracedHeap;
fn build_graph(heap: &TracedHeap) -> Graph { /* cycles OK; collected under pressure */ }
```

Tracing is **opt-in and capability-scoped** — only the genuinely-cyclic parts pay for GC.

**Resist building this.** A real tracing GC is mark-sweep + precise root enumeration, and wasm makes
root scanning painful (no stack introspection → shadow stack / precise root maps). More importantly,
the standard escape hatch for graphs/cycles is **not** `Rc<RefCell>` — it's **arena-of-nodes +
integer indices**: a `Vec<Node>` where edges are `u32` indices, all in one region; cycles are
trivial, the whole graph dies with the region. That's how compilers represent ASTs/CFGs and it
covers the overwhelming majority of "unpredictable lifetime" structures. **Layer 3 is likely a 99%
solution away from being needed.** Document it; build it approximately never.

---

## The synthesis

| Pattern                  | Mechanism                  | Cost                              | When                                              |
| ------------------------ | -------------------------- | --------------------------------- | ------------------------------------------------- |
| Compile-and-die          | Global heap, leak it all   | 0                                 | CLI tools, **compilers**, scripts (today's target)|
| Short-lived computation  | Arena (bump alloc)         | ~0 (pointer bump + bulk reset)    | Request handlers, compile passes, message handling|
| Nested lifetimes         | Region hierarchy           | ~0 (bulk free per region)         | Sessions, connections, actor state                |
| Arbitrary graphs/cycles  | Arena + integer indices    | ~0                                | ASTs, CFGs, most graphs (the Layer-3 *avoidance*) |
| True unpredictable death | Capability-gated tracing   | GC pauses, isolated to traced heap| Caches, cyclic graphs you can't index — rare      |

Every mechanism is a capability; the type system knows which allocator a value lives in. This is
Rust's safety guarantee expressed as **capabilities** rather than **lifetimes** — which is more
SIGIL.

---

## Stress tests: what validated the model

Four axes, each a place the model could have cracked. It held on all four, and the recurring
pattern — *the region model is the existing capability system (containment + deadlines + grants +
the supervision tree) lifted onto a lifetime lattice* — is the strongest evidence the framing is
right.

### 1. Closures — held (and sharpened the principle)

A closure's lifetime is bounded by the shortest-lived thing it captures, so closures are exactly
where "explicit lifetimes" gets ugly. The resolution is the [governing principle](#the-governing-principle-annotate-decisions-derive-consequences):
a closure's **actual region is a derivation** (the capture meet) → inferred; an optional **upper
bound** ("this closure must not outlive the request") is a **decision** → explicit, and it maps
directly onto the existing `CapRestrictDeadline` / T195 cap-deadline machinery. So closures get an
explicit annotation of the *right* thing (the deadline), and the lifetime itself is computed. No new
mechanism; reuses cap-deadlines.

### 2. Actor messages — held (and promoted `@Frozen` to a prerequisite)

Message delivery decouples sender and receiver lifetimes: the sender's handler returns (its arena
dies) before the receiver runs, so a payload in the sender's arena is **dead on arrival**. The model
therefore *derives* the standard actor rule — **`send` is a promotion/copy point** — rather than
asserting it. But it does better than "always copy":

> **Mutable payloads copy (isolation); frozen payloads share by pointer (zero-copy). The type system
> says which.**

This makes **`@Frozen` a prerequisite, not optional polish** — it's what lets immutable data cross
the actor boundary zero-copy while preserving isolation (the Rust `Send`-owned vs `Arc<T>`-shared
line). Message *retention* (`on Connect(conn @ self)` — stored into actor state) is an **explicit
decision** the handler declares, making use-after-free of message data a type error. Region-caps in
messages reuse the existing cap-containment (T183/T186) + deadline (T195) checks, generalized to
lifetimes.

### 3. Generics — held (regions are values, not types)

A region is a **runtime value** (`&Region`, an allocator handle), not a type-level `'a`. So
region-polymorphism is just passing a different handle — **no monomorphization blow-up**, no
type-level region variables. The only static part is the *outlives constraints* (`where region(v):
region(f)`), which are **decisions** the author declares → explicit, free for agents. (Like a cap:
runtime value, statically-checked restrictions.)

### 4. Supervision / restart — held, and produced the keystone

**The region hierarchy IS the supervision tree.** An actor's region is parented by its supervisor's
region (`server ⊃ supervisor ⊃ actor ⊃ handler-arena`). Once you see that, every supervision
question answers itself:

- **Crash = atomic subtree teardown** — one pointer reset, no leaks, no partial state. The model
  *mechanizes* "let it crash + clean restart" (BEAM's per-process-heap-freed-on-death, statically).
- **It argues for restart-not-resume** — restart tears down + recreates the actor-state region (a
  half-done mutation vanishes; clean slate); resume preserves a possibly-inconsistent region. The
  model makes restart clean and resume sketchy, deriving the Erlang philosophy from memory mechanics.
- **Cross-actor zero-copy is sound iff the payload lives in a common-ancestor region** (statically
  checkable from the tree); else copy. Config in server-region → shared everywhere zero-copy; an
  actor's private data → copied to a sibling (independent lifetimes). No actor system I know
  expresses this statically; SIGIL can, because the supervision tree gives the ancestor lattice.
- **Dynamically-acquired handles force copy** — when only a runtime handle is held (region
  relationship not statically known), zero-copy isn't provable → copy (always sound). Zero-copy is
  the opt-in optimization where topology is static (spawn-time parentage). Graceful degradation.
- **Actor handles live *outside* the region model** — actor lifetimes are dynamic (stop/crash/
  restart), not lexical, so a handle is a scheduler-managed token with runtime-checked validity
  (send-to-dead → dead-letter), not a region pointer. Clean boundary: **regions govern data
  lifetime; the supervision tree governs actor liveness.**

The single **policy choice** (a decision, not a derivation) this surfaces: does a crashed actor's
**mailbox** die with the incarnation (Erlang — messages lost) or survive into the restart
(persistent)? The model expresses both cleanly (which region parents the mailbox) but shouldn't
dictate — the language exposes it.

## Why this completes the security thesis

Regions are the **ownership discipline** that bounds *where mutable state flows* and *how long it
lives* — the guarantee that makes SIGIL's shared-mutable heap safe — and it composes with the
existing caps:

```
@SecretCT + @Region(request)  ==  "secret material that physically cannot outlive the request
                                   and cannot escape its scope" — enforced by the type system,
                                   not by convention.
```

A crypto key whose lifetime is *in its type* is SIGIL's whole pitch. And `@Frozen` now earns its
place three times over: opt-in immutability, the region story, **and** the enabler of safe zero-copy
message passing. This turns "we have constant-time and taint and capabilities" into "…and the data
those protect cannot leak, cannot outlive its authorization, and crosses actors without copying only
when provably immutable."

## Open questions (for the epic, not today)

Resolved by the stress testing: closures (intent/derivation), promotion (region-polymorphism is the
default, free for agents), the actor boundary (`send` = copy/promotion; `@Frozen` = zero-copy
enabler), and the supervision story (region tree = supervision tree). What remains:

1. **Elision rules** — the implicit "current region" default and where an explicit region becomes
   mandatory (the Layer-1-implicit ↔ Layer-2-explicit reconciliation). The make-or-break ergonomics.
2. **Mailbox-region parentage** — the one genuine policy choice (dies-with-incarnation vs
   survives-restart); expose it, don't bake it.
3. **The region-outlives checker itself** — the actual static analysis (~30% of Rust's lifetime
   complexity, but explicit rather than inferred, so much of the hard inference is gone).
4. **Region representation in the runtime** — nested bump allocators, the reset-on-scope-exit
   mechanism, and how `&Region` handles are passed (likely alongside the existing capability table).

## Implications for today

This is a **multi-quarter epic** — the defining feature of a future "SIGIL with a memory model,"
**not** the next sprint, and it must **not** reshape the current growable-`Vec<T>` work. The
ephemeral-tool target leaks-and-exits correctly; regions buy it nothing now.

It should change exactly **one** cheap thing in the `Vec` design, the same way "`elem_size` is a
field, not a constant" left the density seam open:

> **Give the `Vec` record an allocator/region handle field** — `alloc: i64`, `0` = "global heap."
> `vec_new`/`vec_with_capacity` set it to `0`; `push`'s grow path allocates through `self.alloc`.
> Then `Vec::in_region(r)` later is a *generalization* (set the field to a real region handle), not
> a record-shape-breaking rewrite.

Cost: one `i64`. Benefit: the single most expensive-to-reverse decision — the record's shape, which
ripples through every constructor and every AIR/wasm snapshot fixture — is pre-paid. The YAGNI
caveat is real (we might guess the handle's shape wrong); the lean is to add it anyway, because
retrofitting a record field is annoying out of proportion to its size.

---

*Provenance: synthesized from a design discussion and validated across four stress-test axes
(closures, actor messages, generics, supervision/restart). The arena → region → tracing structure,
the allocation-lifetime-as-capability thesis, and the agent-language framing are the core ideas; the
two-mechanisms reframe, the "annotate decisions, derive consequences" principle, the
`@Frozen`-as-prerequisite and region-tree-is-supervision-tree results, and the one-field
forward-compat residue are the analysis. Originally written before any of it was built; see the
status block at the top for what has since shipped (the default-frozen arc), what is in flight
(persistent aggregate actor state), and what is scoped next (persistent pointer-bearing state).*
