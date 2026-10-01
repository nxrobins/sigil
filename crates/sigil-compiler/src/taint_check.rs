//! Taint checker pass — static information flow tracking.
//!
//! Prevents `@Secret` data from reaching `@Public` sinks without
//! explicit declassification via a consumed `Declassify` capability.
//!
//! Three-level lattice: `Public < Internal < Secret`.
//! - Value flow: `lub(@Secret, @Public) → @Secret` at every operation
//! - Implicit flow: pc-taint stack for control-dependence
//! - Sink checking: grant returns, function returns reject tainted data

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::span::Span;

use crate::{
    ast::TaintLabel,
    diagnostics::{Diagnostic, codes},
    type_check::{
        TypedBlock, TypedExpr, TypedExprKind, TypedFunction, TypedIntrinsicKind, TypedProgram,
        TypedStmt,
    },
};

// ---------------------------------------------------------------------------
// HEAP FLOOR (BUG-2). The shipped rule for heap CONTENTS: every switch below
// is on except S3, and each stays `pub const` so its cost can be measured off.
// Disclosed in `docs/CLAIMS.md` (claim 53; §C HF-1; §D "Rust-only"),
// `docs/SOUNDNESS_MATRIX.md` SND-IFC-001, and `docs/RESIDUAL_RISKS.md`
// (SR-022 Lean silence, SR-023 the I013 message, SR-024 the host premise;
// SR-025 to SR-027 the three open channels, tracked as #764).
//
// ROOT CAUSE. Taint labels ride on VALUES and on a pointer local's alloc-site
// REGION (M6). HEAP CONTENTS are never labeled: a `load8`/`vec_load` result
// takes its POINTER's label, so any byte reachable through an address the
// checker cannot tie to a labeled region is read at the pointer's label —
// usually @Public. Two concrete launders, both verified end-to-end:
//   * FFI: the host writes a result (SHA-256 digest, granted file body, HTTP
//     body) at the guest's own BUMP_PTR. `let p = alloc(1); crypto_sha256(..);
//     load8(p + 1)` reads the digest through `p` (@Public, region untainted)
//     — only a read through the RETURNED pointer is labeled @Internal.
//   * No FFI: `store8(a, secret); let b = alloc(1); load8(b - 1)` reads the
//     secret back through a FRESH region's pointer. The region model taints
//     region `a`, but the address arithmetic escapes it (`b - 1 == a`).
// Both reduce to the same fact: raw memory intrinsics are unchecked, so a
// per-region label is only sound if every access provably stays inside its
// region — which the checker cannot establish without bounds proofs.
//
// THE RULE. `TaintEnv::floors` holds two MONOTONE per-function labels:
//   `raw_load`   — joined into every RAW memory load result (`load8`,
//                  `vec_load`: an address the checker cannot tie to a value).
//   `typed_read` — joined into every TYPED memory read (`a[i]`, `r.f`, a slice,
//                  a `?` unpack, an intrinsic over an aggregate, and any use of
//                  a heap-resident local: bytes the checker DOES tie to a
//                  labeled value, but which an unchecked raw store can have
//                  overwritten since).
// They are raised by the events that put non-@Public bytes into memory at an
// address the checker cannot label precisely:
//   S1 `HEAP_FLOOR_AFTER_FFI`   — an `ExternCall`, a call to a function whose
//                                 effect row carries `FFI`, or an indirect call
//                                 in a program that has any `FFI` function
//                                 (closure types carry no effect row: fail
//                                 closed) raises `raw_load` to @Internal.
//                                 `typed_read` is untouched by S1 because the
//                                 host writes only FRESH bump-pointer cells,
//                                 which no live typed value overlaps. That is a
//                                 property of THIS repo's hosts, not an axiom:
//                                 the ephemeral host has exactly two guest-memory
//                                 writes (`crates/sigil-runtime/src/ephemeral.rs`
//                                 — `write_to_guest`, called from each of the 10
//                                 byte-returning shims, and the tool-input
//                                 write), and
//                                 both take their destination from
//                                 `alloc_from_bump`, which hands out cells at or
//                                 above `BUMP_PTR` and advances it; the actor
//                                 host writes guest memory nowhere. The
//                                 premise is CENSUSED, not trusted:
//                                 `every_host_write_into_guest_memory_lands_in_a_fresh_bump_cell`
//                                 (`crates/sigil-runtime/tests/host_guest_memory_writes.rs`)
//                                 pins every guest-memory write site under
//                                 `crates/*/src` by enclosing function and
//                                 requires each destination to come from
//                                 `alloc_from_bump`, with a planted anti-stub.
//                                 FAILURE DIRECTION: a future shim that writes
//                                 at a CALLER-SUPPLIED address breaks this
//                                 premise and S1 would then be too weak (a
//                                 typed read could see host bytes) — that
//                                 census fails by name first, and
//                                 `ffi_does_not_floor_typed_reads` pins
//                                 today's accept so the arm is revisited
//                                 deliberately (docs/RESIDUAL_RISKS.md SR-024).
//   S2 `HEAP_FLOOR_AFTER_STORE` — a non-@Public value written into linear
//                                 memory raises `raw_load` to that value's
//                                 label ⊔ the effective pc (a store under a
//                                 secret branch leaks the branch through
//                                 memory as well). The writes are: a
//                                 `store8`/`vec_store`, a projected-place
//                                 assignment (`a[i] = s`, `r.f = s`), a
//                                 heap-typed parameter/capture at function
//                                 entry (its bytes were written by the caller),
//                                 and — at ONE choke point on every expression,
//                                 by its static type — any value of a
//                                 heap-resident type (everything `air::lower_type`
//                                 lowers to a pointer: records, arrays, enums,
//                                 `Result`/`Option`, tuples, `str`, `u256`,
//                                 closures, caps, refs) that is not a plain
//                                 re-read of an existing local. Keying on the
//                                 TYPE rather than on constructor arms is what
//                                 makes the rule total: `Ok(s)`, `u256_from_i64(s)`,
//                                 a closure capturing `s`, and a callee that
//                                 RETURNS a secret aggregate all live in memory
//                                 and were each missed by a per-arm list.
//   S4 `HEAP_FLOOR_RAW_STORE_TYPED_READS` — the DUAL channel. Raw stores are the
//                                 only writes at an unchecked address, so a
//                                 `store8`/`vec_store` of a non-@Public value
//                                 can land INSIDE a live typed aggregate
//                                 allocated at a predictable bump address
//                                 (`let b = alloc(1); let a = [0, 0];
//                                 store8(b + k, s); a[0]` reads `s` back as
//                                 @Public — verified end-to-end). Such a store
//                                 raises `typed_read` to the same label ⊔ pc.
//                                 Materializations and FFI do not raise it:
//                                 they only ever initialize FRESH cells.
//   S6 `HEAP_FLOOR_AFTER_STORE` (same switch) — the ADDRESS channel. A raw
//                                 store's floor takes the join over ALL its
//                                 operands, not just the value: `store8(a + (s
//                                 & 1), 9)` writes a @Public byte, but WHICH
//                                 cell changed is the secret, and a later raw
//                                 load reads it back (verified end-to-end:
//                                 `sigil forge` returns 0 bytes for secret 40
//                                 and 9 bytes for 41). Same for `vec_store`'s
//                                 `base`/`index`/`bound`. A @Public value at a
//                                 @Secret address is a @Secret write. The TYPED
//                                 form is covered too: `a[s & 1] = 1` then
//                                 `a[0]` recovered the bit end-to-end (1 byte
//                                 vs 0 bytes of forge output), so an
//                                 assignment's place contributes its index and
//                                 slice-bound labels to BOTH floors
//                                 (`place_address_taint`).
//   S7 `HEAP_FLOOR_TYPED_WRITE_TYPED_READS` — the ALIAS channel (round 3). A
//                                 projected-place write of a non-@Public value
//                                 labels the place's ROOT name, but aggregates
//                                 are reference-semantic, so an alias taken
//                                 BEFORE the write reads it back: `let b = a;
//                                 a[0] = s; b[0]` (and the record form `q = r;
//                                 r.n = s; q.n`) returned the secret as @Public
//                                 end-to-end on main and on round 2. Such a
//                                 write raises `typed_read` (and `raw_load`) to
//                                 the value's label ⊔ pc — alias-blind, so it
//                                 needs no alias analysis. This is also the
//                                 intraprocedural twin of S5's typed-write arm:
//                                 without it, the same write made through a
//                                 callee would be rejected and made inline
//                                 accepted.
//   S5 `HEAP_FLOOR_CALLEE_WRITES` — the interprocedural STORE direction. At a
//                                 call site the caller's floors are raised by
//                                 what the CALLEE can have left in memory:
//                                 a syntactic, transitive call-graph summary
//                                 (`CallSummary`) of whether the callee can
//                                 write memory at all, and the upper bound on
//                                 the label it could have written — its own
//                                 annotations, joined at the call site with the
//                                 ARGUMENT labels and the site's pc (which is
//                                 what makes it sound for a `@Flow` callee and
//                                 precise for one that only moves @Public
//                                 bytes). A writing callee raises BOTH floors:
//                                 raw stores can land anywhere, and a TYPED
//                                 write lands in whatever aggregate the caller
//                                 handed over as `@Mut` (round 3 — round 2
//                                 floored typed reads only for raw-storing
//                                 callees, and `a[0] = s` / `a[s & 1] = 1` /
//                                 `b.n = s` inside a `@Mut` callee were read
//                                 back as @Public, verified with `sigil forge`
//                                 on main and on round 2). Without S5, `fn
//                                 stash(p: i64) { let s: i64 @Secret = 42;
//                                 store8(p, s); }` called on the caller's own
//                                 pointer launders the secret to @Public on
//                                 read-back — the SAME program written in one
//                                 function is rejected. An
//                                 indirect call, a `perform`, and an actor
//                                 `send`/`ask`/`spawn` name no callee, so they
//                                 take the PROGRAM-WIDE bound (fail closed).
//                                 REGION SIDE (round 6): the floors label what
//                                 a READ returns, but the pointer the callee
//                                 wrote THROUGH can reach a sink UNREAD —
//                                 `tool_main` returns `out << 32 | n` and the
//                                 HOST reads the buffer. `fn poke(out: i64) {
//                                 let s: i64 @Secret = 1; store8(out, s & 1);
//                                 }` then `return out << 32 | n` was accepted
//                                 by `sigil check` and printed the bit with
//                                 `sigil forge` on main (the round-6 review's
//                                 seventh channel) because only the inline
//                                 `store8` arm wrote the M6 region taint. The
//                                 summary now also carries WHICH slots (its
//                                 captures, then its parameters) a raw write
//                                 can go through — `writes_through`: the
//                                 roots of every store operand, rooted locals
//                                 followed through `let`/rebind to a monotone
//                                 fixpoint, transitive over the call graph
//                                 through each edge's argument roots, `All`
//                                 for an unnamed callee — and the call site
//                                 taints the matching arguments' regions at
//                                 the label the floors take
//                                 (`taint_written_argument_regions`), exactly
//                                 as the inline arm does. Cost: that label is
//                                 the callee's annotation bound, so a callee
//                                 that MENTIONS a secret and writes a @Public
//                                 byte through the pointer taints it — pinned
//                                 as a counted cost. BOUNDARY, pinned as
//                                 exact accepts and disclosed (HF-1): an
//                                 argument WITHOUT a region is not reached,
//                                 and the M6 model regions only locals
//                                 bound to `alloc`, or to `+`/`-`
//                                 arithmetic over `alloc` calls and
//                                 regioned locals (`alloc(8)`, `alloc(8) +
//                                 k`, `out + i`) — so a raw write through
//                                 ANY other pointer expression (a
//                                 parameter, `tool_main`'s own `input_ptr`
//                                 included; a callee's result; other
//                                 arithmetic; a pointer reloaded from
//                                 memory or read out of an aggregate or a
//                                 state field) is attributed to no region,
//                                 inline or through a callee, and the
//                                 returned-pointer sink does not see it.
//                                 Round 7 made the region facts
//                                 CONTROL-FLOW sound (joined at loop
//                                 back-edges, `if`/`match` arms and block
//                                 shadows — `loop_fixpoint`); round 8 made
//                                 `alloc(8) + k` BOUND DIRECTLY mint its
//                                 region (`regions_of_bound_value`) — each
//                                 was a regioned-in-principle local the
//                                 model mis-filed, a different class, and
//                                 both are closed.
//   S3 `HEAP_FLOOR_PROGRAM_ENTRY` — the remaining INTERPROCEDURAL direction: the
//                                 LOAD side. S1/S2/S4/S6 are flow-sensitive
//                                 within one function and S5 carries a callee's
//                                 WRITES forward to its caller, but a callee
//                                 that LOADS through a pointer after its CALLER
//                                 did FFI / stored a secret is still not covered
//                                 (the M6 model documents the same boundary).
//                                 With S3
//                                 every function starts at the PROGRAM-WIDE
//                                 floor: `raw_load` @Internal if any `FFI`
//                                 function or extern call exists, and both
//                                 floors joined with every taint annotation
//                                 the program carries (params, returns,
//                                 captures, `let` labels, effect-op contracts)
//                                 — the syntactic upper bound on any label a
//                                 stored value can have.
//   S8 `HEAP_FLOOR_CALLEE_READS` — the interprocedural LOAD direction, RESULT
//                                 side (round 4). A callee that can raw-read
//                                 memory returns a value BUILT FROM bytes the
//                                 CALLER's floor labels: the stdlib
//                                 `str_from_bytes(b, 13)` forges a view over
//                                 the cells the caller's `[s, 0]` left behind,
//                                 copies them through `byte_at`, and its own
//                                 floors start clean (S3 off), so nothing rose
//                                 and `sigil forge` emitted 42 / 7 bytes from a
//                                 plain `module tool; use sigil::string;`
//                                 program composed with the real stdlib (the
//                                 round-3 review). The summary carries
//                                 `reads_raw` (transitive), and at the site the
//                                 caller's raw-load floor is an IMPLICIT
//                                 ARGUMENT: it joins the result and the site
//                                 taint the callee's writes are floored at (a
//                                 callee that stores what it read into a `@Mut`
//                                 argument hands it back through a typed read).
//                                 An UNNAMED callee — an indirect call, a
//                                 `grant` of a non-literal — reads everything,
//                                 so its result carries BOTH floors, which is
//                                 what closed the round-3 open pins for a
//                                 closure that RETURNS what it read. What S8
//                                 does NOT cover: a SINK INSIDE the callee
//                                 (`fn peek(p) { pub_sink(load8(p + 1)) }`,
//                                 result discarded) — that is S3's, still open.
//   THE INTRINSIC SET (round 4)  — which intrinsics read or write memory is ONE
//                                 total classification, `intrinsic_memory`
//                                 (no `_` arm; a new variant fails to compile),
//                                 consulted by the intraprocedural arm AND by
//                                 the S5/S8 scan, and pinned name-by-name by
//                                 `intrinsic_memory_census_is_total`. Round 3
//                                 argued "raw loads = load8/vec_load" from a
//                                 list and forgot `str_from_raw`: a forged `str`
//                                 view is a DEFERRED raw read (every later
//                                 `byte_at` through it reads the viewed bytes),
//                                 and it re-opened S1 (227 / 62 digest bytes)
//                                 and S2 (42 / 7 at byte 5) end-to-end on the
//                                 round-3 build. Slot writes are checked-address
//                                 writes (S7-class); everything else reads only
//                                 THROUGH a typed receiver (floored at the
//                                 choke point) or materializes fresh cells.
//   S5 MATERIALIZATION (round 4) — the scan's write fact now includes what the
//                                 intraprocedural S2 choke point always noted:
//                                 a heap-resident value BUILT in the callee.
//                                 `fn mk() { let s @Secret = 42; let a: [i64;
//                                 2] @Secret = [s, 0]; return 0; }` then
//                                 `load8(b + 5)` in the caller dumped `2a` /
//                                 `07` end-to-end on main and round 3. Keyed on
//                                 the same `is_heap_resident` predicate (total
//                                 over `Type`); raises the caller's RAW-load
//                                 floor only, exactly as S2 does inline.
//   S9 `HEAP_FLOOR_CLOSURE_FLOWS_BACK` — a closure body's exit floors flow back
//                                 to its construct site (the body runs no
//                                 EARLIER than there, so floors raised there
//                                 cover every read after any invocation — fail
//                                 closed even if it never runs), a closure
//                                 literal is a call EDGE in the scan (its
//                                 lifted body's summary joins the enclosing
//                                 function's), and a `grant` whose body is a
//                                 local rather than a literal takes the
//                                 program-wide bound. Round 3 checked a
//                                 `grant` body in a `closure_env` whose floors
//                                 died with it and scanned a
//                                 `ClosureConstruct` as inert, so `grant(&f,
//                                 fn(c) { a[0] = s; })` then `a[0]` was
//                                 accepted (static: actors do not `forge`).
//   S10 `HEAP_FLOOR_ACTOR_DISPATCH` — the ACTOR DISPATCH LOOP. `while`/`for`
//                                 carry the floors across iterations; the
//                                 persistent `mut` state re-entered per message
//                                 carried nothing, so one handler's `buf[s & 1]
//                                 = 1` (or `store8(4096, s)`) was read at a
//                                 clean floor by the next dispatch of any
//                                 handler. Every `init`/handler of an actor now
//                                 starts at the least fixpoint of "run each of
//                                 them once more from these floors and join
//                                 what they leave behind"
//                                 (`actor_dispatch_floors`, semantic, not a
//                                 syntactic bound — a handler with a @Secret
//                                 parameter it never writes floors nothing),
//                                 and EVERY state-field read is a typed memory
//                                 read (a scalar `count` is a cell behind the
//                                 state pointer, not a wasm local — a raw store
//                                 in another handler can clobber it). Per
//                                 ACTOR, not per cell: the false positive is
//                                 pinned as a counted cost.
//   S11 `HEAP_FLOOR_STATIC_READS` — SHARED STATIC DATA (round 5). String
//                                 literal bytes are NOT fresh cells:
//                                 `wasm.rs::collect_static_data` places every
//                                 distinct literal ONCE from `STATIC_DATA_BASE`
//                                 (1024) onward, deduped by value, and each USE
//                                 allocates only an 8-byte header pointing at
//                                 the shared bytes — ordinary writable linear
//                                 memory. A raw store at a literal's address
//                                 (`(l.as_output() >> 32) + 3`, or the bare
//                                 constant `1024 + 3`) is therefore read back by
//                                 EVERY function that materializes that
//                                 literal, so S8's premise that a named
//                                 callee's typed reads reach "only its own
//                                 fresh cells or its parameters" was FALSE:
//                                 `fn peek() { let l: str = "AAAAAAAA"; return
//                                 l.byte_at(3); }` returned the caller's secret
//                                 as @Public end-to-end (2a / 07, a plain
//                                 `module tool;`, no FFI — the round-4 review).
//                                 Probing it found the same class in ONE
//                                 function: `"AAAAAAAA" == "AAABAAAA"` after the
//                                 store leaked the bit (neither operand was a
//                                 typed read), and an f-string's chunks are
//                                 literals too (2a through a callee). Two rules,
//                                 fail closed and coarse by choice: (a) a `str`
//                                 literal and an f-string are TYPED READS of
//                                 shared memory (`reads_typed_memory`), floored
//                                 at `typed_read` exactly like `a[i]`; (b) the
//                                 premise is dropped — a named callee is
//                                 `reads_typed` when its body performs ANY
//                                 typed read (every intrinsic, hence every raw
//                                 read; every heap-resident local; every
//                                 projection; and now every literal), and its
//                                 result joins the CALLER's typed-read floor.
//                                 The precise alternative — a floor raised only
//                                 by stores that MAY alias static data — is not
//                                 available: the checker cannot bound a raw
//                                 store's address. A `str` match PATTERN reads
//                                 static bytes the same way; the parser does
//                                 not admit one today (P018), and both the scan
//                                 and the `match` arm treat it as a typed read
//                                 so a parser change cannot re-open the class.
//                                 Cost: a callee that reads its OWN fresh
//                                 aggregate after the caller's secret raw store
//                                 is now rejected — pinned as a counted cost;
//                                 the corpus delta is measured and reported.
// Both floors are threaded through loop fixpoints (a later iteration's FFI or
// store precedes an earlier statement's load) and seeded into closure bodies
// from the enclosing scope at the construct site.
//
// FAILURE DIRECTION: every switch only ever RAISES a label, never lowers one,
// so a switch that is on can only turn an accept into a reject (fail closed).
// A switch that is off leaves the pre-floor behavior — the documented hole —
// in place; the switches exist so each rule's expressiveness cost can be
// measured separately, and they are `pub` so tests can pin which
// configuration they were written against. WHY EACH IS ON: S1/S2/S4/S6/S7 are
// the intraprocedural channels, each reproduced end-to-end; S5/S8 are the two
// interprocedural directions (store, load-result) without which the same
// program is rejected inline and accepted through a helper; S9/S10 are the
// two scopes (closure env, actor dispatch) whose floors otherwise die at a
// boundary; S11 is shared static data, which no other rule can reach. S3 is
// OFF because its measured corpus cost (see the landing decision record) buys
// only the sink-INSIDE-callee form below.
//
// WHAT IS STILL OPEN with the shipped switch configuration — stated here
// because a rule is only as honest as its scope statement, and each is pinned
// by an ACCEPTING test in `tests/taint_heap_floor.rs` so the gap cannot drift
// silently. The same list is `docs/CLAIMS.md` §C HF-1 and the Known
// exclusions of `docs/SOUNDNESS_MATRIX.md` SND-IFC-001; the two genuine
// accepts (the first two items) are residual risks whose register rows carry
// the tracking issue the landing files.
//   * The interprocedural LOAD direction (S3, off), SINK-INSIDE form only: a
//     callee — named helper or closure — that raw-loads (or reads a captured
//     aggregate) after its CALLER did FFI or stored a secret and SINKS the
//     value INSIDE its own body is checked at its own clean floor (a helper) or
//     at its construct site's floors (a closure), and the caller discards the
//     result. S8 floors what comes OUT of such a callee, so the form where the
//     value is returned — including into a plain `let` — is rejected. Pins:
//     `helper_sinking_a_raw_read_inside_itself_after_callers_ffi_is_the_interprocedural_boundary`,
//     `closure_sinking_an_aggregate_read_inside_itself_after_a_secret_write_is_open`.
//     (Handing an aggregate to a named callee is NOT open: passing a
//     heap-resident local is itself a floored typed read.)
//   * The ALLOCATION-SIZE channel: `alloc((s & 1) + 1)` with a @Secret (not
//     @SecretCT) size moves the bump pointer, and a later `alloc` difference
//     reads the bit back. No memory write carries the secret, so no floor
//     rises. Verified end-to-end (2 vs 3 bytes) on this round and on main.
//     Pin: `secret_allocation_size_observed_through_the_bump_pointer_is_open`.
//   * A sink violation written INSIDE an assignment place's index
//     (`a[pub_sink(s)] = 1`) is not reported as a taint diagnostic: the place
//     is walked for its address LABEL only and those diagnostics are discarded
//     (see `place_address_taint`). The formal bridge rejects such a program as
//     an I-class integrity failure instead — a worse message, but not an
//     accept. Pin (and main at ae026aec agrees):
//     `secret_in_an_assignment_place_index_is_an_integrity_error_not_a_taint_one`.
//   * Whatever the host writes at a caller-supplied address, if a future shim
//     ever does (see S1's premise above).
// ---------------------------------------------------------------------------

/// S1 — raise the raw-load floor to @Internal after FFI (see the block comment).
pub const HEAP_FLOOR_AFTER_FFI: bool = true;
/// S2 — raise the raw-load floor by every non-@Public memory write (see above).
pub const HEAP_FLOOR_AFTER_STORE: bool = true;
/// S4 — raise the typed-read floor by every non-@Public RAW store (see above).
pub const HEAP_FLOOR_RAW_STORE_TYPED_READS: bool = true;
/// S3 — start every function at the program-wide floor (see above). OFF as
/// shipped: it closes only the sink-inside-callee form at a measured corpus
/// cost (the landing decision record), so that form is a recorded residual
/// risk instead.
pub const HEAP_FLOOR_PROGRAM_ENTRY: bool = false;
/// S5 — raise the CALLER's floors at a call site by what the callee can have
/// written (see above). This is the interprocedural STORE direction; its cost
/// is measured separately and reported.
pub const HEAP_FLOOR_CALLEE_WRITES: bool = true;
/// S7 — raise the typed-read floor by every non-@Public PROJECTED-place write
/// (`a[i] = s`, `r.f = s`), which an alias of the aggregate reads back (see
/// above). Round 3; its cost is measured separately and reported.
pub const HEAP_FLOOR_TYPED_WRITE_TYPED_READS: bool = true;
/// S8 — the interprocedural LOAD direction, RESULT side: a call to a callee
/// that can raw-read memory returns a value joined with the CALLER's raw-load
/// floor (and an unnamed callee with both floors); see above. Round 4.
pub const HEAP_FLOOR_CALLEE_READS: bool = true;
/// S9 — a closure body's floors flow back to its construct site, and a
/// `grant` whose body is not a closure literal takes the program-wide bound
/// (see above). Round 4.
pub const HEAP_FLOOR_CLOSURE_FLOWS_BACK: bool = true;
/// S10 — every `init`/handler of an actor starts at the fixpoint of what all
/// of them can have left in the persistent state heap (see above). Round 4.
pub const HEAP_FLOOR_ACTOR_DISPATCH: bool = true;
/// S11 — string literals and f-strings are typed reads of SHARED static data,
/// and a named callee that performs any typed read returns the caller's
/// typed-read floor (see above). Round 5. OFF restores the round-4 premise
/// (named callees never `reads_typed`; literals are not reads) — the
/// documented hole, kept only so the rule's cost can be measured.
pub const HEAP_FLOOR_STATIC_READS: bool = true;

/// The two heap floors (see the HEAP FLOOR block comment). `Copy` and totally
/// ordered per field so a loop fixpoint can compare and join them like a binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HeapFloors {
    /// Joined into every raw memory load result (S1/S2/S3).
    raw_load: TaintLabel,
    /// Joined into every typed memory read (S4/S3).
    typed_read: TaintLabel,
}

impl HeapFloors {
    const CLEAN: Self = Self {
        raw_load: TaintLabel::Public,
        typed_read: TaintLabel::Public,
    };

    /// Field-wise least upper bound — never lowers either floor.
    fn lub(self, other: Self) -> Self {
        Self {
            raw_load: self.raw_load.lub(other.raw_load),
            typed_read: self.typed_read.lub(other.typed_read),
        }
    }
}

/// How one intrinsic touches linear memory, for the heap floors. This is the
/// ONE classification both the intraprocedural arm (`compute_expr_taint`) and
/// the interprocedural scan (`scan_expr`) consult, so a read the checker floors
/// inline is the same read a callee summary reports, and vice versa.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntrinsicMemory {
    /// Reads bytes at an address the checker never verified: the result is
    /// joined with the raw-load floor, and a callee using it `reads_raw`.
    RawRead,
    /// Writes bytes at an unchecked address: raises the store floors by the
    /// join of ALL operands (S2/S4/S6), and a callee using it `writes_memory`.
    RawWrite,
    /// Writes a heap cell at an address the checker DID verify (a slot): a
    /// typed write (S7 — which slot changed under a secret pc is an
    /// observation), and a callee using it `writes_memory`.
    CheckedWrite,
    /// Computes on wasm locals, reads only THROUGH a typed receiver (every
    /// intrinsic result already joins the typed-read floor at the choke
    /// point), or materializes a FRESH cell (noted by the S2 choke point on
    /// the result's type). Nothing further to floor here.
    Inert,
}

/// The memory class of every `TypedIntrinsicKind` — TOTAL, no `_` arm, so a
/// new intrinsic is a compile error here rather than a silently un-floored
/// read (the walker-forgot-an-arm class; `str_from_raw` was exactly that in
/// round 3). Pinned name-by-name by `intrinsic_memory_census_is_total` in
/// `tests/taint_heap_floor.rs`, which parses the enum and this match. Keep
/// every arm's justification on the line above it and keep `::`-qualified
/// names OUT of the comments: the census reads this function's text.
pub fn intrinsic_memory(kind: &TypedIntrinsicKind) -> IntrinsicMemory {
    match kind {
        // Load8: loads one byte at a computed address.
        TypedIntrinsicKind::Load8
        // VecLoad: loads an element at base + index; the bound is the caller's claim.
        | TypedIntrinsicKind::VecLoad { .. }
        // StrFromRaw: forges a str VIEW over (ptr, len) — a deferred raw read:
        // every later byte_at/substr through the view reads those bytes, so the
        // forge itself takes the floor.
        | TypedIntrinsicKind::StrFromRaw { .. } => IntrinsicMemory::RawRead,
        // Store8: stores one byte at a computed address.
        TypedIntrinsicKind::Store8
        // VecStore: stores an element at base + index under a caller-claimed bound.
        | TypedIntrinsicKind::VecStore { .. } => IntrinsicMemory::RawWrite,
        // SlotPut: fills a slot cell (traps if full) — a checked-address write.
        TypedIntrinsicKind::SlotPut
        // SlotTake: reads the cap out and CLEARS the slot cell — a checked-address write.
        | TypedIntrinsicKind::SlotTake => IntrinsicMemory::CheckedWrite,
        // Alloc: moves the bump pointer, writes no byte (the size channel is O3).
        TypedIntrinsicKind::Alloc
        // U256FromI64: materializes a fresh 32-byte cell (S2 choke point).
        | TypedIntrinsicKind::U256FromI64 { .. }
        // U256Make: materializes a fresh 32-byte cell from four limbs (S2 choke point).
        | TypedIntrinsicKind::U256Make
        // U256Limb: reads a limb THROUGH the typed u256 receiver.
        | TypedIntrinsicKind::U256Limb { .. }
        // TrapIf: conditional abort, touches no memory.
        | TypedIntrinsicKind::TrapIf
        // Trap: unconditional abort, touches no memory.
        | TypedIntrinsicKind::Trap
        // SlotNew: materializes a fresh empty slot cell (S2 choke point).
        | TypedIntrinsicKind::SlotNew { .. }
        // ArrayLen: reads the length header THROUGH the typed array receiver.
        | TypedIntrinsicKind::ArrayLen { .. }
        // SliceLen: reads the fat-pointer length THROUGH the typed slice receiver.
        | TypedIntrinsicKind::SliceLen
        // ArrayIsEmpty: length header read THROUGH the typed receiver, compared with zero.
        | TypedIntrinsicKind::ArrayIsEmpty { .. }
        // SliceIsEmpty: fat-pointer length read THROUGH the typed receiver, compared with zero.
        | TypedIntrinsicKind::SliceIsEmpty
        // ArrayContains: bounds-checked element scan THROUGH the typed array receiver.
        | TypedIntrinsicKind::ArrayContains { .. }
        // SliceContains: bounds-checked element scan THROUGH the typed slice receiver.
        | TypedIntrinsicKind::SliceContains { .. }
        // SliceFirst: length-guarded element read THROUGH the typed slice receiver.
        | TypedIntrinsicKind::SliceFirst { .. }
        // SliceLast: length-guarded element read THROUGH the typed slice receiver.
        | TypedIntrinsicKind::SliceLast { .. }
        // StrLen: reads the header length THROUGH the typed str receiver.
        | TypedIntrinsicKind::StrLen
        // StrAsOutput: packs the header (ptr, len) read THROUGH the typed str receiver.
        | TypedIntrinsicKind::StrAsOutput
        // StrIsEmpty: header length read THROUGH the typed str receiver, compared with zero.
        | TypedIntrinsicKind::StrIsEmpty
        // StrByteAt: bounds-checked byte read THROUGH the typed str receiver.
        | TypedIntrinsicKind::StrByteAt { .. }
        // IntConvert: a width conversion on a wasm local.
        | TypedIntrinsicKind::IntConvert { .. }
        // StrSubstr: bounds-checked header read THROUGH the receiver, then a fresh
        // header cell (S2 choke point) viewing the SAME bytes.
        | TypedIntrinsicKind::StrSubstr { .. }
        // CtEq: branch-free compare on wasm locals.
        | TypedIntrinsicKind::CtEq
        // CtSelect: branch-free select on wasm locals.
        | TypedIntrinsicKind::CtSelect
        // CtLt: branch-free compare on wasm locals.
        | TypedIntrinsicKind::CtLt => IntrinsicMemory::Inert,
    }
}

/// Per-variable taint binding — scalar or per-field for records.
#[derive(Debug, Clone, PartialEq)]
enum TaintBinding {
    Scalar(TaintLabel),
    Record(HashMap<String, TaintLabel>),
}

impl TaintBinding {
    fn label(&self) -> TaintLabel {
        match self {
            TaintBinding::Scalar(t) => *t,
            TaintBinding::Record(fields) => fields
                .values()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub),
        }
    }
}

/// The M6 regions a pointer local may point into. ONE region along
/// straight-line code; several only after a control-flow MERGE (a loop
/// back-edge, an `if`/`match` join) where the local was rebound to a different
/// region on one path — the join keeps EVERY candidate, so a store through the
/// local taints all of them and a read folds all of them (fail closed: never
/// fewer candidates than any path). A local absent from `RegionMap` is
/// unregioned: a parameter, a callee result, a pointer read out of memory or an
/// aggregate — the open surface `CLAIMS.md` §C HF-1 discloses.
type RegionSet = BTreeSet<u32>;
type RegionMap = HashMap<String, RegionSet>;

/// The env a `break`/`continue` jumps out with: the bindings the loop join
/// folds into the exit / head, and the M6 region map, joined the same way — a
/// pointer rebound before the jump points into a different region on that
/// path, and dropping the map here would attribute the next iteration's store
/// to the pre-loop region only (the round-7 loop back-edge hole).
#[derive(Clone)]
struct ExitSnapshot {
    bindings: HashMap<String, TaintBinding>,
    region_of: RegionMap,
}

/// What a `let` inside a block shadowed, restored at the block's end: the
/// outer binding AND the outer region set. Restoring the binding alone left the
/// shadow's region on the outer name — `let out = alloc(64); store8(out, s);
/// if c { let out = alloc(8); }` then `return out` read the INNER region
/// (clean) and printed the bit on main. With the merges now joining by union
/// the LEAK direction is closed by the join alone (the outer region stays a
/// candidate through the other arm); the restore is what keeps a shadow's
/// own region OFF the outer name — the twin, a secret stored into the inner
/// buffer only, was a false reject on main.
struct Shadow {
    name: String,
    binding: Option<TaintBinding>,
    region: Option<RegionSet>,
}

#[derive(Clone)]
struct TaintEnv {
    bindings: HashMap<String, TaintBinding>,
    pc_taint: TaintLabel,
    /// Taint of reaching the current continuation after a control-dependent early exit. Unlike
    /// `pc_taint`, which is scoped to a branch/arm/loop body, this survives for the remainder of
    /// the enclosing block. Example: after `if secret { break }`, statements on the fall-through
    /// path are control-dependent on `secret` even though the lexical `if` body has ended.
    continuation_taint: TaintLabel,
    /// Taint env captured at each `break` / `continue` reachable in the CURRENT loop (task #252,
    /// root cause 1). A `break` jumps to the loop EXIT and a `continue` to the loop HEAD, so those
    /// envs must be joined into the post-loop / loop-head state — otherwise a secret captured then
    /// `break`/`continue`d is lost when the checker keeps applying the statements the exit skipped.
    /// A loop installs fresh (empty) collectors so nested loops each own their own break/continue.
    break_envs: Vec<ExitSnapshot>,
    continue_envs: Vec<ExitSnapshot>,
    /// Set by `break` / `continue` / `return`: the rest of the enclosing block is UNREACHABLE, so
    /// `check_block`/`check_stmts` stop. Otherwise the checker would apply the (taint-lowering)
    /// strong updates of code the early exit skips, and a leak would vanish. Reset per branch / arm
    /// / loop-body by the construct that owns the control flow.
    diverged: bool,
    // M6 — region-based memory taint (intra-procedural alias analysis).
    // Each `alloc` is a fresh region; a pointer local carries its source's
    // region (`let q = out` / `let q = out + i` copy the region); every raw
    // write (`store8`, `vec_store` — `IntrinsicMemory::RawWrite`) taints the
    // region of EVERY operand with the join of all its operands and the pc
    // (the value, the address — a @Public byte at a @Secret address moves
    // WHICH cell the host sees — and the bound); and `lookup` folds the
    // region's CURRENT taint into every read. So a pointer aliased BEFORE
    // a secret store still sees the taint (the M5b gap), while rebinding a
    // pointer to a fresh alloc correctly drops the old region (no false
    // positive). Across a CALL the region taint is S5's region side
    // (`taint_written_argument_regions`); across a CLOSURE body the captured
    // pointer keeps its region and the body's region taint flows back to the
    // construct site. Across a CONTROL-FLOW MERGE (round 7) the region facts
    // are joined like the bindings and the floors: a local's candidate set is
    // the union over the paths (`join_regions`), the region taint is
    // loop-carried through `loop_fixpoint`, and a block's shadow restores the
    // outer region — until round 7 the loop fixpoint rebuilt its env without
    // regions and the real pass walked the body ONCE with every pointer in
    // its pre-loop region, so `while i < 2 { store8(q, s & 1); q = out; ..
    // }` then `return out` printed the bit on main (the round-6 review's q5),
    // as did the same rebind split across `if` arms, `match` arms and a
    // shadow. Round 8 made the BINDING total over the `+`/`-` chain: every
    // `alloc` in a bound value's chain mints (`regions_of_bound_value`), so
    // `let q = alloc(8) + 0` is a regioned local like `let q = alloc(8)` —
    // until then only a value that WAS the `alloc` call minted, and a store
    // through such a `q` reached the sink unlabeled. The boundary that
    // remains, pinned OPEN as exact accepts and disclosed in HF-1: regions
    // follow locals bound to `alloc`, or to `+`/`-` arithmetic over `alloc`
    // calls and regioned locals, ONLY — so a raw write through ANY other
    // pointer expression — a parameter (`tool_main`'s own `input_ptr`), a
    // callee's result, other arithmetic, a pointer reloaded from memory or
    // read out of an aggregate or a state field — is attributed to no region
    // and the returned-pointer sink does not see it.
    region_of: RegionMap,
    region_taint: HashMap<u32, TaintLabel>,
    next_region: u32,
    /// HEAP FLOOR (BUG-2, see the module-level block comment): the
    /// labels every raw load / typed read result is joined with from this
    /// point on. MONOTONE — only `raise_floors` writes them, and only upward —
    /// so a branch that raises a floor raises it for the whole rest of the
    /// function (a path-insensitive over-approximation, fail closed).
    floors: HeapFloors,
}

impl TaintEnv {
    fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            pc_taint: TaintLabel::Public,
            continuation_taint: TaintLabel::Public,
            break_envs: Vec::new(),
            continue_envs: Vec::new(),
            diverged: false,
            region_of: HashMap::new(),
            region_taint: HashMap::new(),
            next_region: 0,
            floors: HeapFloors::CLEAN,
        }
    }

    /// Raise the heap floors (never lowers either) — see the HEAP FLOOR block
    /// comment for what each label means.
    fn raise_floors(&mut self, floors: HeapFloors) {
        self.floors = self.floors.lub(floors);
    }

    /// S2 — a non-@Public value was written into linear memory. The written
    /// label is joined with the effective pc: a store that only happens under
    /// a secret branch leaks that branch through memory too.
    fn note_memory_write(&mut self, value_label: TaintLabel) {
        if HEAP_FLOOR_AFTER_STORE {
            let written = value_label.lub(self.effective_pc());
            if written > TaintLabel::Public {
                self.raise_floors(HeapFloors {
                    raw_load: written,
                    typed_read: TaintLabel::Public,
                });
            }
        }
    }

    /// S6 (typed side) — a write whose ADDRESS is not @Public: `a[i] = 1` with
    /// a @Secret `i` stores a @Public value, but WHICH element changed is the
    /// secret, and a later read of `a` — typed (`a[0]`) or raw — recovers it
    /// (verified end-to-end: `sigil forge` returns 1 byte for secret 40 and 0
    /// bytes for 41). Both floors rise, because the observation is the memory
    /// image, not the value.
    fn note_secret_address_write(&mut self, address_label: TaintLabel) {
        if HEAP_FLOOR_AFTER_STORE {
            let written = address_label.lub(self.effective_pc());
            if written > TaintLabel::Public {
                self.raise_floors(HeapFloors {
                    raw_load: written,
                    typed_read: written,
                });
            }
        }
    }

    /// S7 — a non-@Public value was written through a PROJECTED place (`a[i] =
    /// s`, `r.f = s`). The checker labels the place's ROOT name, but records
    /// and arrays are reference-semantic: `let b = a; a[0] = s; b[0]` reads the
    /// secret back through `b`, which no rebind reaches (verified end-to-end on
    /// main at ae026aec and on round 2: `sigil forge` returned 42 bytes for
    /// secret 42 and 7 for 7). Raising the typed-read floor is alias-blind,
    /// hence sound without an alias analysis. `value_label` already carries
    /// the pc (the caller joins it), so a @Public write under a secret branch
    /// raises the floor too. FAILURE DIRECTION: fail closed and imprecise —
    /// every LATER typed read in the function is floored, including reads of
    /// aggregates the write provably did not touch.
    fn note_typed_place_write(&mut self, value_label: TaintLabel) {
        if HEAP_FLOOR_TYPED_WRITE_TYPED_READS {
            let written = value_label.lub(self.effective_pc());
            if written > TaintLabel::Public {
                self.raise_floors(HeapFloors {
                    raw_load: written,
                    typed_read: written,
                });
            }
        }
    }

    /// S4 — a non-@Public value was written through a RAW store, whose address
    /// the checker does not verify: it may sit inside a live typed aggregate,
    /// so typed reads are floored too (S2 already floors the raw loads).
    ///
    /// `written_label` is the lub of the store's VALUE **and** ADDRESS operands
    /// (S6, see the block comment): which cell a raw store touched is part of
    /// the memory image a later raw load observes, so a @Public byte written at
    /// a @Secret-derived address is a @Secret write. Callers pass the join over
    /// ALL operands rather than indexing one, so a missing operand cannot
    /// silently drop the floor (fail closed).
    fn note_raw_store(&mut self, written_label: TaintLabel) {
        self.note_memory_write(written_label);
        if HEAP_FLOOR_RAW_STORE_TYPED_READS {
            let written = written_label.lub(self.effective_pc());
            if written > TaintLabel::Public {
                self.raise_floors(HeapFloors {
                    raw_load: written,
                    typed_read: written,
                });
            }
        }
    }

    /// S1 — control passed through a host boundary that writes guest memory
    /// at the bump pointer: an extern call, or a call whose callee may make
    /// one. Everything the host wrote is @Internal at best.
    fn note_ffi_boundary(&mut self) {
        if HEAP_FLOOR_AFTER_FFI {
            self.raise_floors(HeapFloors {
                raw_load: TaintLabel::Internal,
                typed_read: TaintLabel::Public,
            });
        }
    }

    fn lookup(&self, name: &str) -> TaintLabel {
        let value = self
            .bindings
            .get(name)
            .map(|b| b.label())
            .unwrap_or(TaintLabel::Public);
        // M6 — fold the pointed-to regions' current taint. This is what
        // makes an alias see a secret stored through a sibling pointer. Every
        // candidate region counts (a local rebound on one path of a merge
        // has several): fail closed.
        let region = self
            .region_of
            .get(name)
            .map(|regions| {
                regions
                    .iter()
                    .filter_map(|r| self.region_taint.get(r))
                    .copied()
                    .fold(TaintLabel::Public, TaintLabel::lub)
            })
            .unwrap_or(TaintLabel::Public);
        value.lub(region)
    }

    /// Mint a fresh region id for an `alloc` site.
    fn fresh_region(&mut self) -> u32 {
        let r = self.next_region;
        self.next_region += 1;
        r
    }

    /// Record (or clear) the regions a local points into. Clearing on a
    /// non-pointer rebind (an empty set) is essential — otherwise a reused
    /// name keeps a stale region and a later store would taint the wrong value.
    fn set_region(&mut self, name: &str, regions: RegionSet) {
        if regions.is_empty() {
            self.region_of.remove(name);
        } else {
            self.region_of.insert(name.to_owned(), regions);
        }
    }

    /// Raise a region's taint (a store of a tainted value into it).
    fn taint_region(&mut self, region: u32, taint: TaintLabel) {
        let slot = self
            .region_taint
            .entry(region)
            .or_insert(TaintLabel::Public);
        *slot = slot.lub(taint);
    }

    /// The regions a pointer expression USED (stored through, read through,
    /// passed to a callee) may point into: a local's regions, or the union of
    /// both operands' regions through `+`/`-` address arithmetic (a sum of two
    /// regioned pointers is attributed to both — fail closed). EMPTY for an
    /// `alloc` that is not bound to a local (`store8(alloc(8), s)`: that
    /// buffer is attributed to NO region and sits inside the disclosed
    /// unregioned surface — a host can still read it through an over-long
    /// packed length on a neighbouring buffer, so this is a disclosed gap,
    /// not an unreachable one; a BOUND `alloc` is minted by
    /// `regions_of_bound_value`) and for every other expression kind — a
    /// parameter, a callee result, other arithmetic, a load, a field or index
    /// read: the open surface HF-1 discloses, where "empty" means a store
    /// through it is attributed to NO region. The region also bounds neither
    /// the packed LENGTH the host reads nor a `+`/`-` offset that leaves its
    /// buffer (HF-1 discloses both).
    fn region_of_expr(&self, expr: &crate::typed_ast::TypedExpr) -> RegionSet {
        match &expr.kind {
            crate::typed_ast::TypedExprKind::Local(name) => {
                self.region_of.get(name).cloned().unwrap_or_default()
            }
            crate::typed_ast::TypedExprKind::Binary(b)
                if matches!(b.op, crate::ast::BinaryOp::Add | crate::ast::BinaryOp::Sub) =>
            {
                let mut regions = self.region_of_expr(&b.lhs);
                regions.extend(self.region_of_expr(&b.rhs));
                regions
            }
            _ => RegionSet::new(),
        }
    }

    /// The regions a local BOUND to `value` (`let` or a rebind) points into.
    /// Unlike `region_of_expr` this MINTS: every `alloc(..)` leaf of the
    /// value's `+`/`-` chain is a fresh region — `alloc(8)` alone, `alloc(8)
    /// + k`, `(alloc(8) + 4) + 4` — unioned with the regions of every local
    /// leaf (a chain mixing an `alloc` with another regioned local is
    /// attributed to both — fail closed). Until round 8 only a value that WAS
    /// the `alloc` call minted, so `let q = alloc(8) + 0` was unregioned and
    /// a store through `q` reached the returned-pointer sink unlabeled. Every
    /// other leaf contributes nothing, so a value with no `alloc` and no
    /// regioned local yields the EMPTY set and the caller clears the name (a
    /// reused name must not keep a stale region, or a later store would taint
    /// the wrong value). Minting order is the expression's left-to-right walk,
    /// so `loop_fixpoint`'s stable-id rule holds for chains exactly as for a
    /// bare `alloc`.
    fn regions_of_bound_value(&mut self, value: &crate::typed_ast::TypedExpr) -> RegionSet {
        match &value.kind {
            crate::typed_ast::TypedExprKind::Intrinsic(i)
                if matches!(i.kind, TypedIntrinsicKind::Alloc) =>
            {
                RegionSet::from([self.fresh_region()])
            }
            crate::typed_ast::TypedExprKind::Local(name) => {
                self.region_of.get(name).cloned().unwrap_or_default()
            }
            crate::typed_ast::TypedExprKind::Binary(b)
                if matches!(b.op, crate::ast::BinaryOp::Add | crate::ast::BinaryOp::Sub) =>
            {
                let mut regions = self.regions_of_bound_value(&b.lhs);
                regions.extend(self.regions_of_bound_value(&b.rhs));
                regions
            }
            _ => RegionSet::new(),
        }
    }

    fn lookup_field(&self, name: &str, field: &str) -> TaintLabel {
        match self.bindings.get(name) {
            Some(TaintBinding::Record(fields)) => {
                fields.get(field).copied().unwrap_or(TaintLabel::Public)
            }
            Some(TaintBinding::Scalar(t)) => *t,
            None => TaintLabel::Public,
        }
    }

    fn bind(&mut self, name: &str, taint: TaintLabel) {
        self.bindings
            .insert(name.to_owned(), TaintBinding::Scalar(taint));
    }

    fn bind_record(&mut self, name: &str, fields: HashMap<String, TaintLabel>) {
        self.bindings
            .insert(name.to_owned(), TaintBinding::Record(fields));
    }

    fn effective_pc(&self) -> TaintLabel {
        self.pc_taint.lub(self.continuation_taint)
    }

    fn child_scope(&self) -> Self {
        Self {
            bindings: self.bindings.clone(),
            pc_taint: self.pc_taint,
            continuation_taint: self.continuation_taint,
            break_envs: Vec::new(),
            continue_envs: Vec::new(),
            diverged: false,
            // M6 regions are FUNCTION-scoped, not block-scoped: a pointer bound
            // outside a branch keeps its region (and that region's accumulated
            // taint) inside, so a child scope inherits all three. `next_region`
            // carries forward so a fresh `alloc` in the child cannot collide
            // with a region the parent already minted.
            region_of: self.region_of.clone(),
            region_taint: self.region_taint.clone(),
            next_region: self.next_region,
            // The heap floors are function-scoped and monotone: a child scope
            // starts at the parent's floors (bytes written before the scope
            // are still reachable inside it).
            floors: self.floors,
        }
    }
}

/// Join a per-variable binding across two control-flow paths — the least upper bound, so a taint
/// present on EITHER path is preserved at the merge and can never be lowered by the other path
/// (SC-T1). Records join field-by-field; a field absent on one side takes that side's overall
/// label as a sound floor.
fn join_binding(a: &TaintBinding, b: &TaintBinding) -> TaintBinding {
    match (a, b) {
        (TaintBinding::Record(fa), TaintBinding::Record(fb)) => {
            let mut out = HashMap::new();
            for k in fa.keys().chain(fb.keys()) {
                let la = fa.get(k).copied().unwrap_or_else(|| a.label());
                let lb = fb.get(k).copied().unwrap_or_else(|| b.label());
                out.insert(k.clone(), la.lub(lb));
            }
            TaintBinding::Record(out)
        }
        _ => TaintBinding::Scalar(a.label().lub(b.label())),
    }
}

/// Replace `env.bindings` with the join of several branch-result maps, keeping ONLY names that
/// existed in `pre` (bindings introduced inside a branch do not escape it — SC-T2). Each surviving
/// name's taint is the lub over every branch; a branch that never rebound the name contributes its
/// pre-branch value. `branches` must be non-empty.
fn merge_branch_bindings(
    env: &mut TaintEnv,
    pre: &HashMap<String, TaintBinding>,
    branches: &[HashMap<String, TaintBinding>],
) {
    let mut merged = HashMap::with_capacity(pre.len());
    for (name, pre_b) in pre {
        let mut acc = branches[0].get(name).unwrap_or(pre_b).clone();
        for br in &branches[1..] {
            acc = join_binding(&acc, br.get(name).unwrap_or(pre_b));
        }
        merged.insert(name.clone(), acc);
    }
    env.bindings = merged;
}

/// Join `pre`, `base`, and every env in `others` (all restricted to `pre`'s names, SC-T2), returning
/// the lub. `pre` is ALWAYS a floor: for the fixpoint it is the zero-iteration path (the loop body
/// may not run, so the pre-loop state survives — SC-T3); for the break-join `head ⊒ pre` already, so
/// flooring is a harmless no-op there. A name missing from an env contributes its `pre` value.
fn join_envs_into(
    base: &HashMap<String, TaintBinding>,
    others: &[ExitSnapshot],
    pre: &HashMap<String, TaintBinding>,
) -> HashMap<String, TaintBinding> {
    let mut out = HashMap::with_capacity(pre.len());
    for (name, pre_b) in pre {
        let mut acc = join_binding(pre_b, base.get(name).unwrap_or(pre_b));
        for o in others {
            acc = join_binding(&acc, o.bindings.get(name).unwrap_or(pre_b));
        }
        out.insert(name.clone(), acc);
    }
    out
}

/// Join the M6 region map across control-flow paths, restricted to `names` (the
/// bindings live BEFORE the merged construct, SC-T2 — a pointer `let`-bound
/// inside a block does not escape it). A local's candidate set is the UNION
/// over `floor` (the path that skips the merged code: the pre-loop map for a
/// loop head's zero-iteration path and the head itself at the loop exit; EMPTY
/// for an `if`/`match`, whose arms each started from the pre-branch map and so
/// carry it for every name they did not rebind), the fall-through path `base`
/// and every path in `others` (`continue`s at a loop head, `break`s at its
/// exit, the further arms of a branch). So a pointer rebound to another region
/// on ONE path is attributed to every candidate at every later store and read
/// — fail closed: never fewer candidates than any path that reaches the merge.
/// A name absent from a path's map is unregioned on that path and contributes
/// nothing; a name absent from every path is dropped (unregioned).
fn join_regions(
    floor: &RegionMap,
    base: &RegionMap,
    others: &[&RegionMap],
    names: &HashMap<String, TaintBinding>,
) -> RegionMap {
    let mut out = RegionMap::with_capacity(names.len());
    for name in names.keys() {
        let mut acc: RegionSet = floor.get(name).cloned().unwrap_or_default();
        if let Some(regions) = base.get(name) {
            acc.extend(regions.iter().copied());
        }
        for o in others {
            if let Some(regions) = o.get(name) {
                acc.extend(regions.iter().copied());
            }
        }
        if !acc.is_empty() {
            out.insert(name.clone(), acc);
        }
    }
    out
}

/// The region map after an `if`/`match`: the union over the arms that FALL
/// THROUGH to the code after it (each arm's map started from the pre-branch
/// map, so a name no arm rebound keeps its region through them; a name every
/// arm rebound loses the pre-branch region, exactly as its binding does). With
/// no falling-through arm the code after is unreachable and the caller keeps
/// the pre-branch map.
fn merge_branch_regions(arms: &[RegionMap], names: &HashMap<String, TaintBinding>) -> RegionMap {
    match arms.split_first() {
        Some((first, rest)) => {
            let rest: Vec<&RegionMap> = rest.iter().collect();
            join_regions(&RegionMap::new(), first, &rest, names)
        }
        None => RegionMap::new(),
    }
}

/// Pointwise lub of two region-taint maps (a region absent from one side is
/// @Public there). Region taint only ever rises, so this is the join a
/// back-edge needs.
fn join_region_taint(
    a: &HashMap<u32, TaintLabel>,
    b: &HashMap<u32, TaintLabel>,
) -> HashMap<u32, TaintLabel> {
    let mut out = a.clone();
    for (region, taint) in b {
        let slot = out.entry(*region).or_insert(TaintLabel::Public);
        *slot = slot.lub(*taint);
    }
    out
}

fn apply_restore(map: &mut HashMap<String, TaintBinding>, name: &str, old: &Option<TaintBinding>) {
    match old {
        Some(b) => {
            map.insert(name.to_owned(), b.clone());
        }
        None => {
            map.remove(name);
        }
    }
}

/// `apply_restore` for the region map: the outer region set comes back
/// (`Some`), or a name that had none outside is unregioned again (`None`).
fn apply_restore_region(map: &mut RegionMap, name: &str, old: &Option<RegionSet>) {
    match old {
        Some(regions) => {
            map.insert(name.to_owned(), regions.clone());
        }
        None => {
            map.remove(name);
        }
    }
}

/// Restore the outer bindings for names a block lexically shadowed (task #252, root cause 3). A
/// `let x` inside a block shadows any outer `x` and is dropped at block end; because `TaintEnv` is
/// one flat map with no scope stack, the shadow overwrites the outer entry, so a merge would keep
/// the (higher) shadow taint and reject a safe program. Restoring the captured outer value —
/// `Some(b)` for a shadow, `None` for a genuinely new name that must be removed — fixes that.
///
/// The restore also applies to any `break`/`continue` envs CAPTURED DURING this block (the slices
/// from `break_base`/`continue_base`): a shadow is out of scope at the loop exit / head those envs
/// flow to, so the value they carry for a shadowed name must be the OUTER binding, not the shadow.
/// Without this a `while c { y = 0; let y = s; break; }` captures the inner `y = s` and false-rejects
/// on the outer (public) `y`.
///
/// The M6 region set is restored alongside the binding (round 7): the shadow's
/// region on the outer name after the block let a secret stored through the
/// OUTER pointer before the block read back clean at the return.
fn restore_shadowed(
    env: &mut TaintEnv,
    shadowed: Vec<Shadow>,
    break_base: usize,
    continue_base: usize,
) {
    for shadow in shadowed.into_iter().rev() {
        apply_restore(&mut env.bindings, &shadow.name, &shadow.binding);
        apply_restore_region(&mut env.region_of, &shadow.name, &shadow.region);
        for be in env.break_envs[break_base..].iter_mut() {
            apply_restore(&mut be.bindings, &shadow.name, &shadow.binding);
            apply_restore_region(&mut be.region_of, &shadow.name, &shadow.region);
        }
        for ce in env.continue_envs[continue_base..].iter_mut() {
            apply_restore(&mut ce.bindings, &shadow.name, &shadow.binding);
            apply_restore_region(&mut ce.region_of, &shadow.name, &shadow.region);
        }
    }
}

/// The names a pattern binds (for restoring an arm-scoped pattern binding that collides with an
/// outer variable — task #252, root cause 3). Mirrors `bind_pattern_taint`.
fn pattern_bound_names(pattern: &crate::type_check::TypedPattern) -> Vec<String> {
    use crate::type_check::TypedPattern;
    let mut out = Vec::new();
    match pattern {
        TypedPattern::Binding(name) => out.push(name.clone()),
        TypedPattern::EnumVariant { bindings, .. } => {
            for (name, _) in bindings {
                out.push(name.clone());
            }
        }
        TypedPattern::Array {
            elem_binds, rest, ..
        } => {
            for (name, _) in elem_binds {
                if let Some(name) = name {
                    out.push(name.clone());
                }
            }
            if let Some((Some(rest_name), _)) = rest {
                out.push(rest_name.clone());
            }
        }
        TypedPattern::Literal(_) | TypedPattern::Range { .. } | TypedPattern::Wildcard => {}
    }
    out
}

/// Bounded fixpoint for a loop's control-flow join (SC-T3, X-T2). A loop body may run ZERO times, so
/// the state after the loop is the least fixpoint of `I = pre ⊔ body(I) ⊔ continue-paths(I)`: the
/// LUB of the pre-loop (zero-iteration) state, the fall-through effect of every iteration, and the
/// state at each `continue` (which jumps back to the head). The taint lattice is finite, so this
/// converges (for all-@Public code — the whole compiler — the first pass already converges).
///
/// Diagnostics are SUPPRESSED here (a throwaway sink): the body is re-run to propagate second-order
/// taint (`x = y; y = secret` needs a second pass before `x` is seen as secret), and emitting each
/// pass's diagnostics would duplicate them. The CALLER runs one real diagnostic pass from the
/// returned fixpoint head — the soundest point, since every taint that can reach the body across
/// iterations is present there — and separately folds in the `break` paths for the loop EXIT.
///
/// `run_body` runs the loop body against a scratch env (binding the loop variable and, for `while`,
/// re-deriving the guard's pc-taint from the current head). Only names present in `pre` survive into
/// the returned maps — loop-body-local names do not escape (SC-T2). The bound is sized to the state:
/// each non-converging pass raises ≥1 component by ≥1 lattice step, and every component is finite
/// (see the bound at the end of the loop). It fails LOUD in debug and CLOSED in release (top-taint)
/// if convergence is somehow not reached.
///
/// The loop-carried state is everything a back-edge can change that the next iteration observes:
/// the bindings (task #252), the heap floors (BUG-2 — an FFI call or a secret store late in
/// iteration N precedes a load early in iteration N+1) and, since round 7, the M6 region facts.
/// Without the last, each pass rebuilt its env with NO regions and the caller's real pass walked the
/// body ONCE with every pointer local in its PRE-loop region, so `let mut q = alloc(8); while i < 2
/// { store8(q, s & 1); q = out; i = i + 1; }` then `return out << 32 | 1` attributed both stores to
/// the fresh region and `sigil forge` printed the bit (the round-6 review's q5, `00` / `01` on main;
/// the same body inside a callee was already closed by the flow-INsensitive S5 rooted scan).
fn loop_fixpoint(
    pre: &TaintEnv,
    pc_taint: TaintLabel,
    continuation_taint: TaintLabel,
    mut run_body: impl FnMut(&mut TaintEnv, &mut Vec<Diagnostic>),
) -> LoopHead {
    let names = &pre.bindings;
    let mut head = LoopHead {
        bindings: pre.bindings.clone(),
        floors: pre.floors,
        region_of: pre.region_of.clone(),
        region_taint: pre.region_taint.clone(),
        next_region: pre.next_region,
    };
    let mut sink = Vec::new();
    let mut passes: usize = 0;
    loop {
        let mut env = TaintEnv::new();
        env.bindings = head.bindings.clone();
        env.pc_taint = pc_taint;
        env.continuation_taint = continuation_taint;
        env.floors = head.floors;
        env.region_of = head.region_of.clone();
        env.region_taint = head.region_taint.clone();
        // STABLE REGION IDS: every pass — and the caller's real pass, which starts from the same
        // `next_region` — mints a body `alloc`'s region at the SAME id, so all iterations'
        // allocations at one site share one region (the join over iterations: sound, and the one
        // counted cost of this rule — a pointer allocated in the body reads the taint an earlier
        // iteration stored through the same site's pointer). Letting the ids run on would add a
        // fresh `region_taint` key every pass and the fixpoint could never be reached.
        env.next_region = pre.next_region;
        run_body(&mut env, &mut sink);
        // I' = pre ⊔ fall-through(I) ⊔ (⊔ continue paths), restricted to pre's names (SC-T2). The
        // join with `pre` (never dropped) is the zero-iteration path (SC-T3); the continue paths are
        // the iterations that jumped back to the head early via `continue`. The regions join the
        // same way — a local's candidate set is the UNION over the paths — and the region taint is
        // monotone, so the body's end state already holds every store on any path through it.
        let continue_regions: Vec<&RegionMap> =
            env.continue_envs.iter().map(|c| &c.region_of).collect();
        let next = LoopHead {
            bindings: join_envs_into(&env.bindings, &env.continue_envs, names),
            floors: head.floors.lub(env.floors),
            region_of: join_regions(&pre.region_of, &env.region_of, &continue_regions, names),
            region_taint: join_region_taint(&head.region_taint, &env.region_taint),
            next_region: head.next_region.max(env.next_region),
        };
        if next == head {
            return next;
        }
        head = next;
        passes += 1;
        // BOUND, sized to the state. Bindings: ≤ names × 4 levels; floors: 2 × 4; region taint:
        // ≤ regions × 4; region sets: ≤ names × regions elements. `head.next_region` is the number of
        // regions the state can ever name (ids are stable, so one pass mints them all); it is re-read
        // every pass, so a walk that only reaches a further `alloc` later can only widen the bound.
        let names_n = names.len();
        let regions_n = head.next_region as usize;
        let max_iters = names_n
            .saturating_mul(4)
            .saturating_add(8)
            .saturating_add(regions_n.saturating_mul(4))
            .saturating_add(names_n.saturating_mul(regions_n))
            .saturating_add(4);
        if passes >= max_iters {
            break;
        }
    }
    // Unreachable given the size-scaled bound; a hit means a monotonicity bug. Fail LOUD in debug,
    // and fail CLOSED in release: top-taint every pre name, both floors and every region the loop
    // can name, so nothing is under-tainted (X-T2).
    debug_assert!(
        false,
        "taint loop fixpoint did not converge within {passes} iterations"
    );
    LoopHead {
        bindings: names
            .keys()
            .map(|k| (k.clone(), TaintBinding::Scalar(TaintLabel::Secret)))
            .collect(),
        floors: HeapFloors {
            raw_load: TaintLabel::Secret,
            typed_read: TaintLabel::Secret,
        },
        region_taint: (0..head.next_region)
            .map(|r| (r, TaintLabel::Secret))
            .collect(),
        region_of: head.region_of,
        next_region: head.next_region,
    }
}

/// The loop-carried state at a loop head (`loop_fixpoint`): the bindings, the heap floors, the M6
/// region map and region taint, and the region id the body's allocations reached — the caller's
/// real pass restarts minting at the pre-loop id so it names the same regions the passes did, and
/// continues from `next_region` after the loop.
#[derive(Clone, PartialEq)]
struct LoopHead {
    bindings: HashMap<String, TaintBinding>,
    floors: HeapFloors,
    region_of: RegionMap,
    region_taint: HashMap<u32, TaintLabel>,
    next_region: u32,
}

/// Install a loop's fixpoint head as the env the real diagnostic pass over the body starts from:
/// the head's bindings, floors and region facts, minting body regions from the pre-loop id exactly
/// as the passes did (`pre_next_region`).
fn enter_loop_head(env: &mut TaintEnv, head: &LoopHead, pre_next_region: u32) {
    env.bindings = head.bindings.clone();
    env.floors = head.floors;
    env.region_of = head.region_of.clone();
    env.region_taint = head.region_taint.clone();
    env.next_region = pre_next_region;
}

/// The post-loop state: bindings = head ⊔ every `break` env (a `break` jumps to the exit), and the
/// region map = head ∪ the real pass's end state ∪ every `break` path, restricted to the pre-loop
/// names (SC-T2). The region taint is monotone and already in `env`. `next_region` continues past
/// every region the body named so a later `alloc` cannot collide with one.
fn exit_loop(
    env: &mut TaintEnv,
    head: &LoopHead,
    breaks: &[ExitSnapshot],
    pre: &HashMap<String, TaintBinding>,
) {
    env.bindings = join_envs_into(&head.bindings, breaks, pre);
    let body_end = std::mem::take(&mut env.region_of);
    let break_regions: Vec<&RegionMap> = breaks.iter().map(|b| &b.region_of).collect();
    env.region_of = join_regions(&head.region_of, &body_end, &break_regions, pre);
    env.next_region = env.next_region.max(head.next_region);
}

/// One call site to a taint-polymorphic (`@Flow`) callee, keyed by the checking context
/// and the call expression's span. The context is the `@Flow` function instance whose body
/// was being checked (`None` for ordinary functions), so a closure body checked inside an
/// instantiation records under that instantiation.
pub type FlowCallSite = (Option<(String, TaintLabel)>, (usize, usize, u32));

/// The instantiation label every `@Flow` call site resolved to during the per-label body
/// checks: the join of all argument taints, exactly the label the call's result carries.
/// `formal.rs` projects one concrete instance of the callee per label that actually occurs,
/// so the Lean kernel checks the same instantiations the type checker did; a site that is
/// absent here falls back to the `@Secret`-seeded original, which can only over-taint.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FlowCallInstantiations {
    pub sites: BTreeMap<FlowCallSite, TaintLabel>,
}

impl FlowCallInstantiations {
    /// The recorded instantiation for a call at `span` checked under `context`.
    pub fn label(&self, context: Option<(&str, TaintLabel)>, span: Span) -> Option<TaintLabel> {
        let key = (
            context.map(|(name, label)| (name.to_owned(), label)),
            (span.start, span.end, span.source.0),
        );
        self.sites.get(&key).copied()
    }
}

struct FlowRecorder {
    context: Option<(String, TaintLabel)>,
    sites: BTreeMap<FlowCallSite, TaintLabel>,
}

thread_local! {
    /// Active only inside `flow_call_instantiations`; `None` during ordinary checking, so the
    /// diagnostic pass never pays for or depends on recording.
    static FLOW_RECORDER: RefCell<Option<FlowRecorder>> = const { RefCell::new(None) };
}

fn set_flow_context(context: Option<(String, TaintLabel)>) {
    FLOW_RECORDER.with(|recorder| {
        if let Some(recorder) = recorder.borrow_mut().as_mut() {
            recorder.context = context;
        }
    });
}

fn record_flow_call(span: Span, label: TaintLabel) {
    FLOW_RECORDER.with(|recorder| {
        if let Some(recorder) = recorder.borrow_mut().as_mut() {
            let key = (
                recorder.context.clone(),
                (span.start, span.end, span.source.0),
            );
            recorder
                .sites
                .entry(key)
                .and_modify(|existing| *existing = existing.lub(label))
                .or_insert(label);
        }
    });
}

/// Re-run the per-instantiation checks with the call-site recorder armed and return every
/// `@Flow` call site's instantiation label. Diagnostics are discarded: the caller has already
/// run `check_taints`, and a program that fails it never reaches the formal projection.
pub fn flow_call_instantiations(program: &TypedProgram) -> FlowCallInstantiations {
    // HEAP FLOOR (S5): the same summaries this program's diagnostic pass used —
    // the recorded instantiations must come from the identical analysis.
    let _summaries = CallSummaryScope::arm(program);
    FLOW_RECORDER.with(|recorder| {
        *recorder.borrow_mut() = Some(FlowRecorder {
            context: None,
            sites: BTreeMap::new(),
        });
    });
    let mut diagnostics = Vec::new();
    for module in &program.modules {
        for function in &module.functions {
            if matches!(function.kind, crate::typed_ast::TypedFunctionKind::Closure) {
                continue;
            }
            check_function(function, program, &mut diagnostics);
        }
    }
    let sites = FLOW_RECORDER.with(|recorder| {
        recorder
            .borrow_mut()
            .take()
            .map(|recorder| recorder.sites)
            .unwrap_or_default()
    });
    FlowCallInstantiations { sites }
}

pub fn check_taints(program: &TypedProgram) -> Result<(), Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    // HEAP FLOOR (S5): compute the per-callee write summaries once for this
    // program; the guard clears them when this pass returns.
    let _summaries = CallSummaryScope::arm(program);

    for module in &program.modules {
        for function in &module.functions {
            // Closures are checked at their construct site (see
            // `TypedExprKind::ClosureConstruct` in `compute_expr_taint`)
            // with their capture taints propagated from the enclosing
            // scope (spec §3.7, E4). Skipping them here avoids a
            // double-check with all-@Public captures that would miss
            // CT violations inside closure bodies.
            if matches!(function.kind, crate::typed_ast::TypedFunctionKind::Closure) {
                continue;
            }
            check_function(function, program, &mut diagnostics);
        }
    }

    if diagnostics.is_empty() {
        Ok(())
    } else {
        Err(diagnostics)
    }
}

/// The labels a `@Flow` signature quantifies over. `@SecretCT` is deliberately
/// absent: constant-time is a property of the CODE (branching, indexing, and
/// allocation are all restricted under it), so one body cannot satisfy both the
/// CT and non-CT disciplines. A `@SecretCT` argument to a `@Flow` parameter is
/// rejected at the call site (T030) rather than silently checked as `@Secret`.
const FLOW_INSTANTIATIONS: [TaintLabel; 3] =
    [TaintLabel::Public, TaintLabel::Internal, TaintLabel::Secret];

fn check_function(
    function: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Taint polymorphism: a `@Flow` signature promises the body is safe at EVERY
    // admissible label, so check it once per label with the `@Flow` positions
    // (parameters and, if declared, the return) instantiated to that label. This
    // is what earns the right to skip the parameter check at call sites — a body
    // that laundered a `@Flow` value into a `@Public` sink passes the `@Public`
    // instantiation but fails at `@Internal`.
    //
    // Only the FIRST failing instantiation is reported: a genuine leak fails at
    // every label, and emitting it three times would bury the signal. The label
    // is named in the message so the failing instantiation is never a guess.
    if function.ret_flow || function.params.iter().any(|p| p.flow) {
        for label in FLOW_INSTANTIATIONS {
            let mut instance = function.clone();
            for param in &mut instance.params {
                if param.flow {
                    param.taint = label;
                }
            }
            if instance.ret_flow {
                instance.ret_taint = label;
            }

            let mut instance_diagnostics = Vec::new();
            set_flow_context(Some((function.name.clone(), label)));
            check_function_body(&instance, program, &mut instance_diagnostics);
            set_flow_context(None);
            if !instance_diagnostics.is_empty() {
                diagnostics.extend(instance_diagnostics.into_iter().map(|d| {
                    d.with_message_prefix(format!(
                        "in the @{label:?} instantiation of taint-polymorphic `{}`: ",
                        function.name
                    ))
                }));
                return;
            }
        }
        return;
    }

    check_function_body(function, program, diagnostics);
}

fn check_function_body(
    function: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // HEAP FLOOR (S3/S10): the entry floors — see the block comment. With S3
    // off a module function starts with a clean heap, which is exactly the
    // documented intraprocedural boundary; an actor's `init`/handler starts at
    // its actor's dispatch floors.
    let mut env = function_entry_env(function, function_entry_floors(function, program));
    check_block(&function.body, &mut env, function, program, diagnostics);
}

/// The environment a function body is checked in: parameters and captures
/// bound at their declared taints, the heap floors at `floors`. Shared by the
/// diagnostic pass and the S10 fixpoint so both walk the SAME entry state.
fn function_entry_env(function: &TypedFunction, floors: HeapFloors) -> TaintEnv {
    let mut env = TaintEnv::new();
    env.floors = floors;

    // Bind parameters with their declared taints
    for param in &function.params {
        env.bind(&param.name, param.taint);
        // HEAP FLOOR (S2): a heap-typed parameter's bytes are ALREADY in linear
        // memory (the caller wrote them), reachable by a raw load in this body.
        if is_heap_resident(&param.ty) {
            env.note_memory_write(param.taint);
        }
    }
    // Bind captures
    for cap in &function.captures {
        env.bind(&cap.name, cap.taint);
        // HEAP FLOOR (S2): actor state lives in the persistent heap — same rule.
        if is_heap_resident(&cap.ty) {
            env.note_memory_write(cap.taint);
        }
    }
    env
}

fn check_block(
    block: &TypedBlock,
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<TaintLabel> {
    check_stmt_seq(&block.statements, env, current_fn, program, diagnostics)
}

/// Walk a statement sequence (a block body or a for-loop body) with two soundness rules from task
/// #252: STOP at the first diverging statement (`break`/`continue`/`return` make the rest of the
/// sequence unreachable, so their taint-lowering strong updates must not be applied on the exit
/// path — root cause 1), and RESTORE any name a `let` here shadowed to its outer binding on exit
/// (a shadow is lexically scoped and must not corrupt the outer variable at a merge — root cause 3).
fn check_stmt_seq(
    stmts: &[TypedStmt],
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<TaintLabel> {
    let break_base = env.break_envs.len();
    let continue_base = env.continue_envs.len();
    let mut shadowed: Vec<Shadow> = Vec::new();
    let mut tail_taint = None;
    for (index, stmt) in stmts.iter().enumerate() {
        if env.diverged {
            break;
        }
        if let TypedStmt::Let(s) = stmt
            && !shadowed.iter().any(|shadow| shadow.name == s.name)
        {
            shadowed.push(Shadow {
                name: s.name.clone(),
                binding: env.bindings.get(&s.name).cloned(),
                region: env.region_of.get(&s.name).cloned(),
            });
        }
        if let TypedStmt::Expr(s) = stmt {
            let expr_taint = compute_expr_taint(&s.expr, env, current_fn, program, diagnostics);
            // M5b/M6 — storing a tainted value through a pointer taints the
            // pointer's REGION (its `alloc` site), so `store8(out, secret);
            // return out` and its alias `let q = out; store8(out, secret);
            // return q` both surface the secret at the return → T001. That
            // rule used to live HERE as a `Store8`-only arm over the VALUE
            // operand; it is now the `IntrinsicMemory::RawWrite` arm of
            // `compute_expr_taint_unfloored`, total over the write intrinsics
            // and their operands (address and bound too), and its
            // interprocedural side is `taint_written_argument_regions`.
            if index + 1 == stmts.len() {
                tail_taint = Some(expr_taint);
            }
        } else {
            check_stmt(stmt, env, current_fn, program, diagnostics);
        }
    }
    restore_shadowed(env, shadowed, break_base, continue_base);
    tail_taint
}

fn check_stmt(
    stmt: &TypedStmt,
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    match stmt {
        TypedStmt::Let(s) => {
            let expr_taint = compute_expr_taint(&s.value, env, current_fn, program, diagnostics);
            // An unannotated `let` is a @Public DECLARATION in a monomorphic
            // function — that is what makes `let x = <@Internal>;` an error
            // rather than a silent absorb. A taint-POLYMORPHIC body has no
            // fixed label for that default to mean: the same statement is
            // checked at @Public, @Internal and @Secret, and its locals hold
            // whatever the caller's data was. So there, an unannotated local
            // INFERS (binds at `effective` below, which already includes
            // `expr_taint`) and only an explicitly written `@Label` is a sink.
            //
            // This narrows where the early check applies; it does not weaken
            // the guarantee. The local still carries the initializer's taint,
            // so every real sink downstream — the function's own return, an
            // argument to a non-`@Flow` parameter, a store, a grant — still
            // fires. A polymorphic body that leaks is caught there.
            let is_polymorphic = current_fn.ret_flow || current_fn.params.iter().any(|p| p.flow);
            let declared = match s.taint {
                Some(explicit) => explicit,
                None if is_polymorphic => expr_taint,
                None => TaintLabel::Public,
            };

            // CT016 (T030) — source-of-CT (E1): assigning into a @SecretCT
            // binding from @Internal or @Secret is forbidden. Only @Public
            // and @SecretCT sources are permitted in @SecretCT typing position.
            // @Public→@SecretCT is allowed (literals, constants, masks).
            if declared.is_ct()
                && (expr_taint == TaintLabel::Internal || expr_taint == TaintLabel::Secret)
            {
                diagnostics.push(Diagnostic::error(
                    codes::T030,
                    format!(
                        "cannot upcast @{:?} value to @SecretCT binding; source must be @Public or @SecretCT (T030 / CT016)",
                        expr_taint
                    ),
                    Some(s.span),
                ));
            }

            // Check for downgrade violation
            if !expr_taint.can_flow_to(declared) {
                diagnostics.push(Diagnostic::error(
                    codes::T001,
                    format!(
                        "cannot assign @{:?} value to @{:?} binding without declassification (T001)",
                        expr_taint, declared
                    ),
                    Some(s.span),
                ));
            }

            // Bind at effective taint (max of declared and computed)
            let effective = expr_taint.lub(declared).lub(env.effective_pc());
            // Check if value is a record construct — track per-field
            if let TypedExprKind::RecordConstruct(r) = &s.value.kind {
                let mut field_taints = HashMap::new();
                for (fname, fexpr) in &r.fields {
                    let ft = compute_expr_taint(fexpr, env, current_fn, program, diagnostics)
                        .lub(env.effective_pc());
                    field_taints.insert(fname.clone(), ft);
                }
                env.bind_record(&s.name, field_taints);
            } else {
                env.bind(&s.name, effective);
            }
            // M6 — region assignment: every `alloc` in the value's `+`/`-`
            // chain mints a region and every regioned local in it contributes
            // its regions (`regions_of_bound_value`); anything else clears the
            // name (a reused name must not keep a stale region, or a later
            // store would taint the wrong value).
            let regions = env.regions_of_bound_value(&s.value);
            env.set_region(&s.name, regions);
        }
        TypedStmt::Assign(s) => {
            let expr_taint = compute_expr_taint(&s.value, env, current_fn, program, diagnostics);
            let effective = expr_taint.lub(env.effective_pc());
            // Propagate the assigned taint to the place. A bare local is
            // rebound (flow-sensitive overwrite, as before); a field/index
            // place raises its root container's taint — a sound
            // over-approximation that never under-taints a secret written
            // into an aggregate.
            match &s.place.kind {
                crate::typed_ast::TypedExprKind::Local(name) => {
                    env.bind(name, effective);
                    // M6 — rebinding a pointer local updates its regions
                    // (this is what makes rebinding to a fresh alloc — bare
                    // or inside a `+`/`-` chain — drop the old region and
                    // avoid a false positive on aliases).
                    let regions = env.regions_of_bound_value(&s.value);
                    env.set_region(name, regions);
                }
                // Actor-state (M2) anti-laundering: a state field is a declared
                // taint SINK (captures are bound at their declared label; state
                // fields carry no annotation, so @Public). Handlers read it back
                // at that label, so storing a higher-taint value into it in `init`
                // would launder a secret across the immutable-state boundary
                // (F007's sibling). Sink-check the value against the field's
                // declared taint instead of flow-sensitively rebinding it.
                crate::typed_ast::TypedExprKind::StateField(name) => {
                    let declared = env.lookup(name);
                    if !effective.can_flow_to(declared) {
                        diagnostics.push(Diagnostic::error(
                            codes::T001,
                            format!(
                                "cannot store @{effective:?} value into actor state field \
                                 `{name}` declared @{declared:?} without declassification (T001)"
                            ),
                            Some(s.span),
                        ));
                    }
                }
                _ => {
                    // AGG-4 (aggregate-state taint hardening): a PROJECTED write into a
                    // state aggregate — `d.v = s`, `a[i] = s` (root is a StateField, not a
                    // Local) — is the taint-axis twin of the T123 projected-place gate. The
                    // bare-`StateField` arm above sink-checks a scalar `n = s`; without this,
                    // routing an @Secret through an aggregate field's projection silently
                    // DROPPED the taint (`place_root_local` returns None on a StateField
                    // root), laundering it to @Public on read-back. Root the place to its
                    // StateField and apply the SAME sink. Checked BEFORE the local fallback,
                    // so a projected LOCAL write (`localrec.f = x`) still rebinds.
                    // HEAP FLOOR (S2): an aggregate element/field write lands in
                    // linear memory (records and arrays are heap-resident), so a
                    // raw load elsewhere can reach the written value.
                    env.note_memory_write(effective);
                    // HEAP FLOOR (S7): and a TYPED read through any ALIAS of the
                    // written aggregate reads the value back — the root rebind
                    // below labels only the NAME written through.
                    env.note_typed_place_write(effective);
                    // HEAP FLOOR (S6, typed side): and WHICH cell it landed in is
                    // an observation of its own — `a[s & 1] = 1` then `a[0]`
                    // recovers the secret's low bit with no secret VALUE ever
                    // stored (verified end-to-end on main).
                    let address = place_address_taint(&s.place, env, current_fn, program);
                    env.note_secret_address_write(address);
                    if let Some(root) = place_root_statefield(&s.place) {
                        let declared = env.lookup(root);
                        if !effective.can_flow_to(declared) {
                            diagnostics.push(Diagnostic::error(
                                codes::T001,
                                format!(
                                    "cannot store @{effective:?} value through actor state \
                                     field `{root}` declared @{declared:?} without \
                                     declassification (T001)"
                                ),
                                Some(s.span),
                            ));
                        }
                    } else if let Some(root) = place_root_local(&s.place) {
                        let raised = effective.lub(env.lookup(root));
                        env.bind(root, raised);
                    }
                }
            }
        }
        TypedStmt::Expr(_) => unreachable!("expression statements are handled by check_stmt_seq"),
        TypedStmt::If(s) => {
            // M3: Implicit flow — push condition taint onto pc-taint
            let cond_taint =
                compute_expr_taint(&s.condition, env, current_fn, program, diagnostics);
            // CT001 (T020) — secret-dependent branch. Reject before descent so
            // pc-taint never holds SecretCT (spec §3.6 invariant).
            if cond_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T020,
                    "secret-dependent branch: `if` condition has taint @SecretCT (T020 / CT001)"
                        .to_string(),
                    Some(s.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            let branch_pc = outer_pc.lub(cond_taint);

            // CONTROL-FLOW JOIN (task #252, docs/specs/taint-join-soundness.md). Previously both
            // branches ran against the SAME env, so the last branch's strong-update relabels won
            // and a secret assigned on one path vanished at the merge:
            //   `if c { x = s } else { x = 0 }` left x @Public — a T001 fail-open.
            // Snapshot, run each branch from the snapshot, and lub the results so a taint on EITHER
            // path survives. An empty `else_branch` (a bare `if`) leaves its map == `pre`, so the
            // not-taken path correctly contributes the pre-if state.
            let pre = env.bindings.clone();
            // M6 (round 7): the region map is a per-path fact like the bindings — each branch
            // starts from the pre-branch map and the fall-through maps are UNIONED after. Before,
            // both branches wrote one map and the last writer won: `if c { q = out } else { q =
            // alloc(8) }; store8(q, s & 1); return out` attributed the store to the else branch's
            // fresh region only and printed the bit on main.
            let pre_regions = env.region_of.clone();
            env.pc_taint = branch_pc;
            env.continuation_taint = outer_continuation;
            env.diverged = false;
            check_block(&s.then_branch, env, current_fn, program, diagnostics);
            let then_div = env.diverged;
            let then_continuation = env.continuation_taint;
            let then_map = std::mem::replace(&mut env.bindings, pre.clone());
            let then_regions = std::mem::replace(&mut env.region_of, pre_regions.clone());
            env.pc_taint = branch_pc;
            env.continuation_taint = outer_continuation;
            env.diverged = false;
            check_block(&s.else_branch, env, current_fn, program, diagnostics);
            let else_div = env.diverged;
            let else_continuation = env.continuation_taint;
            let else_map = std::mem::replace(&mut env.bindings, pre.clone());
            let else_regions = std::mem::replace(&mut env.region_of, pre_regions);
            // Merge ONLY the branches that fall through to the code after the `if`. A branch that
            // diverges (`return`/`break`/`continue`) does not reach the merge, so its snapshot must
            // NOT be lubbed in — otherwise the common `if c { return err } else { x = <public> }`
            // over-taints x with the diverging branch's stale pre-value (task #252, the divergence
            // false-reject). A break/continue's state is carried by the loop collectors instead.
            let mut fallthrough: Vec<HashMap<String, TaintBinding>> = Vec::with_capacity(2);
            let mut fallthrough_regions: Vec<RegionMap> = Vec::with_capacity(2);
            if !then_div {
                fallthrough.push(then_map);
                fallthrough_regions.push(then_regions);
            }
            if !else_div {
                fallthrough.push(else_map);
                fallthrough_regions.push(else_regions);
            }
            if !fallthrough.is_empty() {
                merge_branch_bindings(env, &pre, &fallthrough);
                env.region_of = merge_branch_regions(&fallthrough_regions, &pre);
            }

            env.pc_taint = outer_pc;
            // A continuation inherits nested early-exit dependence from every branch that can
            // reach it. If exactly one branch exits, reaching the continuation also reveals the
            // condition itself (the secret-guarded break/continue/return channel).
            let mut continuation = outer_continuation;
            if !then_div {
                continuation = continuation.lub(then_continuation);
            }
            if !else_div {
                continuation = continuation.lub(else_continuation);
            }
            if then_div != else_div {
                continuation = continuation.lub(cond_taint);
            }
            env.continuation_taint = continuation;
            // The `if` diverges (the code after it is unreachable) only if BOTH branches do.
            env.diverged = then_div && else_div;
        }
        TypedStmt::While(s) => {
            let cond_taint =
                compute_expr_taint(&s.condition, env, current_fn, program, diagnostics);
            // CT002 (T021) — secret-dependent loop.
            if cond_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T021,
                    "secret-dependent loop: `while` condition has taint @SecretCT (T021 / CT002)"
                        .to_string(),
                    Some(s.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            // CONTROL-FLOW JOIN over the ZERO-ITERATION path (task #252, SC-T3). The body may run
            // zero times, so the post-loop state is the fixpoint of `pre ⊔ body ⊔ continue-paths`,
            // then joined with every `break` for the exit. Without this a variable lowered inside the
            // body (`x = 0`) wrongly reads @Public even when the loop never runs and `x` is still
            // @Secret from before the loop — a T001 fail-open.
            let pre = env.bindings.clone();
            let pre_next_region = env.next_region;
            // A loop OWNS its break/continue: install fresh collectors so a break/continue inside
            // binds to THIS loop and an enclosing loop's collectors are untouched (root cause 1).
            let outer_breaks = std::mem::take(&mut env.break_envs);
            let outer_continues = std::mem::take(&mut env.continue_envs);
            let head = loop_fixpoint(env, outer_pc, outer_continuation, |e, d| {
                // The `while` guard is re-evaluated EVERY iteration, so if a guard variable
                // becomes tainted inside the loop the body is control-dependent on a secret.
                // Re-derive the guard taint from the CURRENT head each pass and fold it into pc
                // (Lens-E implicit flow). `for` loops fix their count at entry, so they snapshot
                // body_pc once instead.
                let ct = compute_expr_taint(&s.condition, e, current_fn, program, d);
                e.pc_taint = outer_pc.lub(ct);
                check_block(&s.body, e, current_fn, program, d);
            });
            // One real diagnostic pass from the fixpoint head — sinks inside the body must see every
            // taint any iteration can bring, the guard's fixpoint pc-taint, the loop-carried heap
            // floor and the loop-carried region facts. The guard's own diagnostics were already
            // emitted at the top of the arm, so re-derive its taint into a throwaway sink to avoid
            // a duplicate.
            enter_loop_head(env, &head, pre_next_region);
            let mut guard_sink = Vec::new();
            let head_cond =
                compute_expr_taint(&s.condition, env, current_fn, program, &mut guard_sink);
            // The guard may start Public and become SecretCT through a loop-carried assignment.
            // The entry check above cannot see that second-iteration state, so reject from the
            // stabilized loop head before analysing the body for real. Restore the enclosing
            // collectors first so this fail-closed exit cannot corrupt an outer loop's analysis.
            if head_cond.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T021,
                    "secret-dependent loop: `while` condition has taint @SecretCT (T021 / CT002)"
                        .to_string(),
                    Some(s.span),
                ));
                // The region facts stay at the head's (a superset of the pre-loop facts — fail
                // closed on a path that is an error anyway), and `next_region` moves past every
                // region the body named.
                env.bindings = pre;
                env.next_region = env.next_region.max(head.next_region);
                env.pc_taint = outer_pc;
                env.continuation_taint = outer_continuation;
                env.break_envs = outer_breaks;
                env.continue_envs = outer_continues;
                env.diverged = false;
                return;
            }
            env.pc_taint = outer_pc.lub(head_cond);
            env.continuation_taint = outer_continuation;
            env.break_envs = Vec::new();
            env.continue_envs = Vec::new();
            env.diverged = false;
            check_block(&s.body, env, current_fn, program, diagnostics);
            // Post-loop state = the loop-head fixpoint ⊔ every `break` env (break jumps to the exit).
            let breaks = std::mem::take(&mut env.break_envs);
            exit_loop(env, &head, &breaks, &pre);
            env.pc_taint = outer_pc;
            env.continuation_taint = outer_continuation;
            // Restore the enclosing loop's collectors; a loop itself does not diverge (code after it
            // is reachable — a `break` exits to there).
            env.break_envs = outer_breaks;
            env.continue_envs = outer_continues;
            env.diverged = false;
        }
        TypedStmt::ForIn(s) => {
            let iter_taint = compute_expr_taint(&s.iterable, env, current_fn, program, diagnostics);
            // CT003 (T022) — secret-dependent iteration count.
            if iter_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T022,
                    "secret-dependent iteration: `for` iterable has taint @SecretCT (T022 / CT003)"
                        .to_string(),
                    Some(s.iterable.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            let body_pc = outer_pc.lub(iter_taint);
            let var_taint = iter_taint.lub(body_pc);
            // CONTROL-FLOW JOIN over the ZERO-ITERATION path (task #252, SC-T3): a `for` over an
            // empty iterable runs the body zero times, so the post-loop state must join the body
            // effect (plus continue/break paths) with the pre-loop state. The loop variable is
            // re-bound each iteration and does not escape (absent from `pre`, so it is dropped —
            // SC-T2). body_pc is fixed for the whole loop: the iteration count is set at entry, so
            // — unlike `while` — the body is NOT control-dependent on a variable that mutates inside.
            let pre = env.bindings.clone();
            let pre_next_region = env.next_region;
            let outer_breaks = std::mem::take(&mut env.break_envs);
            let outer_continues = std::mem::take(&mut env.continue_envs);
            let head = loop_fixpoint(env, body_pc, outer_continuation, |e, d| {
                e.bind(&s.var, var_taint);
                check_stmts(&s.body, e, current_fn, program, d);
            });
            enter_loop_head(env, &head, pre_next_region);
            env.pc_taint = body_pc;
            env.continuation_taint = outer_continuation;
            env.break_envs = Vec::new();
            env.continue_envs = Vec::new();
            env.diverged = false;
            env.bind(&s.var, var_taint);
            check_stmts(&s.body, env, current_fn, program, diagnostics);
            let breaks = std::mem::take(&mut env.break_envs);
            exit_loop(env, &head, &breaks, &pre);
            // The loop variable is scoped to the body: if its name COLLIDES with an outer variable it
            // is a shadow, so restore the outer binding at the loop exit (a non-colliding name is
            // absent from `pre` and already dropped by join_envs_into). Without this,
            // `for x in it { x = s }` over-taints an outer `x` the body never actually writes.
            apply_restore(&mut env.bindings, &s.var, &pre.get(&s.var).cloned());
            env.pc_taint = outer_pc;
            env.continuation_taint = outer_continuation;
            env.break_envs = outer_breaks;
            env.continue_envs = outer_continues;
            env.diverged = false;
        }
        TypedStmt::ForRange(s) => {
            // The bounds ARE the iteration count — the same CT003 (T022) rule as
            // ForIn's iterable applies to `start` ⊔ `end`.
            let start_taint = compute_expr_taint(&s.start, env, current_fn, program, diagnostics);
            let end_taint = compute_expr_taint(&s.end, env, current_fn, program, diagnostics);
            let bound_taint = start_taint.lub(end_taint);
            if bound_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T022,
                    "secret-dependent iteration: `for` range bound has taint @SecretCT (T022 / CT003)"
                        .to_string(),
                    Some(s.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            let body_pc = outer_pc.lub(bound_taint);
            let var_taint = bound_taint.lub(body_pc);
            // CONTROL-FLOW JOIN over the ZERO-ITERATION path (task #252, SC-T3): a `for i in a..b`
            // with `a >= b` runs zero times, so the post-loop state must join the body (plus
            // continue/break paths) with the pre-loop state. Same shape as `ForIn` (fixed body_pc).
            let pre = env.bindings.clone();
            let pre_next_region = env.next_region;
            let outer_breaks = std::mem::take(&mut env.break_envs);
            let outer_continues = std::mem::take(&mut env.continue_envs);
            let head = loop_fixpoint(env, body_pc, outer_continuation, |e, d| {
                e.bind(&s.var, var_taint);
                check_stmts(&s.body, e, current_fn, program, d);
            });
            enter_loop_head(env, &head, pre_next_region);
            env.pc_taint = body_pc;
            env.continuation_taint = outer_continuation;
            env.break_envs = Vec::new();
            env.continue_envs = Vec::new();
            env.diverged = false;
            env.bind(&s.var, var_taint);
            check_stmts(&s.body, env, current_fn, program, diagnostics);
            let breaks = std::mem::take(&mut env.break_envs);
            exit_loop(env, &head, &breaks, &pre);
            // The range-loop variable is body-scoped: restore an outer binding it shadows (see ForIn).
            apply_restore(&mut env.bindings, &s.var, &pre.get(&s.var).cloned());
            env.pc_taint = outer_pc;
            env.continuation_taint = outer_continuation;
            env.break_envs = outer_breaks;
            env.continue_envs = outer_continues;
            env.diverged = false;
        }
        TypedStmt::Match(s) => {
            let mut scrutinee_taint =
                compute_expr_taint(&s.scrutinee, env, current_fn, program, diagnostics);
            // HEAP FLOOR (S11): a `str` literal pattern compares the scrutinee
            // against SHARED static bytes a raw store may have changed, so
            // which arm runs is floored like any typed read. Unreachable from
            // source today (the parser rejects a `str` pattern); fail closed.
            if HEAP_FLOOR_STATIC_READS
                && s.arms.iter().any(|arm| pattern_reads_static(&arm.pattern))
            {
                scrutinee_taint = scrutinee_taint.lub(env.floors.typed_read);
            }
            // CT004 (T023) — secret-dependent dispatch.
            if scrutinee_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T023,
                    "secret-dependent dispatch: `match` scrutinee has taint @SecretCT (T023 / CT004)"
                        .to_string(),
                    Some(s.span),
                ));
                return;
            }
            let outer_pc = env.pc_taint;
            let outer_continuation = env.continuation_taint;
            // Reaching a later guarded arm depends on every earlier guard being false, so the
            // selection pc accumulates guard taints in source order.
            let mut selection_pc = outer_pc.lub(scrutinee_taint);

            // CONTROL-FLOW JOIN across arms (task #252, SC-T4). Previously every arm ran against the
            // SAME env, so the last arm's strong-update relabels won and a secret bound in an earlier
            // arm vanished at the merge. Snapshot, run each arm from the snapshot, and lub the arm
            // results. Match exhaustiveness (T087, verified before taint check) guarantees SOME arm
            // always runs, so — exactly like `If`'s then/else — the merge is the lub over arms with
            // NO separate fall-through (`pre`) path; adding one would over-taint the common
            // `match c { A => x = 0, B => x = 0 }` and wrongly reject it.
            let pre = env.bindings.clone();
            // M6 (round 7): each arm starts from the pre-match region map and the falling-through
            // arms' maps are unioned after, exactly as `If` does — before, the last arm's map won.
            let pre_regions = env.region_of.clone();
            let mut arm_maps: Vec<HashMap<String, TaintBinding>> = Vec::with_capacity(s.arms.len());
            let mut arm_regions: Vec<RegionMap> = Vec::with_capacity(s.arms.len());
            let mut all_diverge = !s.arms.is_empty();
            let mut continuation = outer_continuation;
            let mut divergence_taint = TaintLabel::Public;
            for arm in &s.arms {
                env.bindings = pre.clone();
                env.region_of = pre_regions.clone();
                env.pc_taint = selection_pc;
                env.continuation_taint = outer_continuation;
                env.diverged = false;
                let break_base = env.break_envs.len();
                let continue_base = env.continue_envs.len();
                // A pattern binding whose name COLLIDES with an outer variable would otherwise
                // overwrite it in the flat env and survive the merge (root cause 3). Restore those
                // names to their outer (`pre`) value after the arm so only genuine assignments to an
                // outer variable are merged; the pattern binding itself is arm-scoped.
                let pat_names = pattern_bound_names(&arm.pattern);
                bind_pattern_taint(&arm.pattern, scrutinee_taint.lub(env.effective_pc()), env);
                if let Some(g) = &arm.guard {
                    let guard_taint = compute_expr_taint(g, env, current_fn, program, diagnostics);
                    // A SecretCT guard is secret-dependent dispatch just like a SecretCT
                    // scrutinee. Reject before descending to avoid a cascade under a CT pc.
                    if guard_taint.is_ct() {
                        diagnostics.push(Diagnostic::error(
                            codes::T023,
                            "secret-dependent dispatch: `match` guard has taint @SecretCT (T023 / CT004)"
                                .to_string(),
                            Some(g.span),
                        ));
                        env.bindings = pre;
                        env.region_of = pre_regions;
                        env.pc_taint = outer_pc;
                        env.continuation_taint = outer_continuation;
                        env.diverged = false;
                        return;
                    }
                    selection_pc = selection_pc.lub(guard_taint);
                    env.pc_taint = selection_pc;
                }
                check_block(&arm.body, env, current_fn, program, diagnostics);
                let arm_div = env.diverged;
                let arm_control = env.effective_pc();
                all_diverge = all_diverge && arm_div;
                // Restore the collided pattern names in env.bindings AND in any break/continue env
                // captured during this arm — a `break`/`continue` inside a colliding-pattern arm
                // captures the arm-scoped (scrutinee-tainted) binding, which is out of scope at the
                // loop exit/head those envs flow to (the same fix `restore_shadowed` applies to
                // `let` shadows; the pattern channel needed it too).
                for n in &pat_names {
                    let old = pre.get(n).cloned();
                    apply_restore(&mut env.bindings, n, &old);
                    for be in env.break_envs[break_base..].iter_mut() {
                        apply_restore(&mut be.bindings, n, &old);
                    }
                    for ce in env.continue_envs[continue_base..].iter_mut() {
                        apply_restore(&mut ce.bindings, n, &old);
                    }
                }
                let arm_map = std::mem::replace(&mut env.bindings, pre.clone());
                let arm_region_map = std::mem::replace(&mut env.region_of, pre_regions.clone());
                // Only arms that FALL THROUGH reach the code after the match; a diverging arm
                // (`return`/`break`/`continue`) must not be lubbed in, else its stale pre-value
                // over-taints a variable a falling-through arm lowered (the divergence false-reject).
                if !arm_div {
                    arm_maps.push(arm_map);
                    arm_regions.push(arm_region_map);
                    continuation = continuation.lub(env.continuation_taint);
                } else {
                    divergence_taint = divergence_taint.lub(arm_control);
                }
            }
            if !arm_maps.is_empty() {
                merge_branch_bindings(env, &pre, &arm_maps);
                env.region_of = merge_branch_regions(&arm_regions, &pre);
            }
            env.pc_taint = outer_pc;
            env.continuation_taint = if all_diverge {
                outer_continuation
            } else {
                continuation.lub(divergence_taint)
            };
            // The match diverges (code after it is unreachable) only if EVERY arm diverges.
            env.diverged = all_diverge;
        }
        TypedStmt::Break(_) => {
            // `break` jumps to the loop EXIT with the current env; capture it (bindings and M6
            // region map) for the post-loop join and mark the rest of this block unreachable (task
            // #252, root cause 1).
            let snap = ExitSnapshot {
                bindings: env.bindings.clone(),
                region_of: env.region_of.clone(),
            };
            env.break_envs.push(snap);
            env.diverged = true;
        }
        TypedStmt::Continue(_) => {
            // `continue` jumps to the loop HEAD with the current env; the fixpoint folds it in.
            let snap = ExitSnapshot {
                bindings: env.bindings.clone(),
                region_of: env.region_of.clone(),
            };
            env.continue_envs.push(snap);
            env.diverged = true;
        }
        TypedStmt::Return(s) => {
            // M4: Sink checking — return value must satisfy declared ret_taint
            if let Some(v) = &s.value {
                let return_taint = compute_expr_taint(v, env, current_fn, program, diagnostics);
                // Forge tools intentionally bridge @Internal FFI results back to the host
                // via `tool_main`'s packed ptr/len return. Keep Secret->Public blocked,
                // but allow Internal tool output without forcing an explicit capability.
                let declared = current_fn.effective_return_taint();

                // CT016 (T030) — source-of-CT (E1) at return position.
                if declared.is_ct()
                    && (return_taint == TaintLabel::Internal || return_taint == TaintLabel::Secret)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::T030,
                        format!(
                            "cannot return @{:?} value from @SecretCT function; source must be @Public or @SecretCT (T030 / CT016)",
                            return_taint
                        ),
                        Some(s.span),
                    ));
                }

                if !return_taint.can_flow_to(declared) {
                    diagnostics.push(Diagnostic::error(
                        codes::T001,
                        format!(
                            "returning @{:?} value from function declared @{:?} (T001)",
                            return_taint, declared
                        ),
                        Some(s.span),
                    ));
                }
            }
            // `return` leaves the function; the rest of the enclosing block is unreachable, so its
            // taint updates must not be applied on this path (task #252, root cause 1).
            env.diverged = true;
        }
    }
}

fn check_stmts(
    stmts: &[TypedStmt],
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let _ = check_stmt_seq(stmts, env, current_fn, program, diagnostics);
}

/// The innermost local a place expression writes through (`x` for `x`,
/// `a` for `a.b.c` or `a.b[i]`). Returns `None` for a non-place expr,
/// which the type checker has already rejected (T243). Used to propagate
/// assignment taint to the root container of a field/index write.
fn place_root_local(place: &crate::typed_ast::TypedExpr) -> Option<&str> {
    match &place.kind {
        crate::typed_ast::TypedExprKind::Local(name) => Some(name.as_str()),
        crate::typed_ast::TypedExprKind::FieldAccess(fa) => place_root_local(&fa.object),
        crate::typed_ast::TypedExprKind::Index(ix) => place_root_local(&ix.array),
        _ => None,
    }
}

/// The state field a place writes THROUGH (`d` for `d.f`, `a` for `a[i]`), or
/// `None` for a place not rooted in a state field. The taint-axis twin of
/// `place_root_local`, used to sink-check a projected write into an aggregate
/// state field (AGG-4). Mirrors `type_check::statements::place_root_statefield`
/// (re-added locally — that copy is `pub(super)` and unreachable from here).
fn place_root_statefield(place: &crate::typed_ast::TypedExpr) -> Option<&str> {
    match &place.kind {
        crate::typed_ast::TypedExprKind::StateField(name) => Some(name.as_str()),
        crate::typed_ast::TypedExprKind::FieldAccess(fa) => place_root_statefield(&fa.object),
        crate::typed_ast::TypedExprKind::Index(ix) => place_root_statefield(&ix.array),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// HEAP FLOOR helpers (BUG-2; see the block comment at the top).
// ---------------------------------------------------------------------------

/// Whether `callee`'s declared effect row carries `FFI`. Extern declarations
/// must declare `FFI` (T160) and a caller's row must cover its callees', so a
/// function that can reach the host boundary carries `FFI` here.
fn callee_has_ffi(callee: &TypedFunction, program: &TypedProgram) -> bool {
    program
        .effect_registry
        .lookup("FFI")
        .is_some_and(|id| callee.effects.effects.contains(&id))
}

/// Whether ANY function in the program carries `FFI` in its row or makes an
/// extern call directly. Used where the callee is unknown (indirect calls).
fn program_has_ffi(program: &TypedProgram) -> bool {
    let scan = scan_program(program);
    scan.has_extern_call
        || program
            .modules
            .iter()
            .flat_map(|m| m.functions.iter())
            .any(|f| callee_has_ffi(f, program))
}

/// S3 — the program-wide heap floors every function starts at. Clean unless
/// `HEAP_FLOOR_PROGRAM_ENTRY` is on; then both floors carry the syntactic
/// upper bound on any label a value in this program can carry (every taint
/// annotation), and `raw_load` is additionally @Internal if the program can
/// reach the host boundary at all. A program with no FFI and no non-@Public
/// annotation stays clean.
fn program_entry_floors(program: &TypedProgram) -> HeapFloors {
    if !HEAP_FLOOR_PROGRAM_ENTRY {
        return HeapFloors::CLEAN;
    }
    let scan = scan_program(program);
    let mut raw_load = scan.max_annotation;
    if scan.has_extern_call || program_has_ffi(program) {
        raw_load = raw_load.lub(TaintLabel::Internal);
    }
    HeapFloors {
        raw_load,
        typed_read: scan.max_annotation,
    }
}

/// S5 (region side) — a set of a function's SLOTS: its captures first (an
/// actor's state fields, a lifted closure's captured locals), then its
/// parameters, in declaration order. `Known(mask)` names slots by bit;
/// `All` is the fail-closed top, taken wherever the set cannot be named — a
/// slot past the 64-bit mask, an unnamed callee, a scan that did not converge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SlotSet {
    Known(u64),
    All,
}

impl SlotSet {
    const NONE: Self = Self::Known(0);

    /// The singleton set of one slot; `All` past the mask (fail closed).
    fn slot(index: usize) -> Self {
        if index < 64 {
            Self::Known(1 << index)
        } else {
            Self::All
        }
    }

    fn covers(self, index: usize) -> bool {
        match self {
            Self::All => true,
            Self::Known(mask) => index < 64 && mask & (1 << index) != 0,
        }
    }

    /// Set union — the join; `All` absorbs.
    fn lub(self, other: Self) -> Self {
        match (self, other) {
            (Self::Known(a), Self::Known(b)) => Self::Known(a | b),
            _ => Self::All,
        }
    }
}

/// S5 (region side) — one call edge in a function body: which callee, and for
/// each argument position the slots of THIS function the argument's pointer is
/// rooted in. `params` says which of the callee's slots the vector fills: a
/// named call's arguments fill its PARAMETER slots (numbered after its
/// captures), a closure literal's vector holds its CAPTURE slots directly.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CallEdge {
    callee: String,
    arg_roots: Vec<SlotSet>,
    params: bool,
}

/// S5 — what a CALL to one function can leave behind in linear memory (see the
/// block comment). Syntactic and transitive over the call graph: no attempt is
/// made to prove WHICH value was stored, only an upper bound on its label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CallSummary {
    /// Some write into linear memory at an EXISTING address is reachable from
    /// this callee: a raw store, a projected-place assignment (`a[i] = v`,
    /// `r.f = v`, an actor state field), or a slot write. Round 3 made this
    /// the ONLY write fact gating the typed-read floor — a separate raw-store
    /// flag used to gate it and left typed writes through `@Mut` open (see
    /// `CallSummary::floors`).
    writes_memory: bool,
    /// Round 4 — some heap-resident value is BUILT into fresh cells by this
    /// callee (`HeapScan::materializes`). Raises the caller's raw-load floor
    /// only, exactly as the intraprocedural S2 note does.
    materializes: bool,
    /// S8 — a raw memory read is reachable from this callee, so its RESULT
    /// (and anything it wrote) may carry bytes the CALLER's raw-load floor
    /// labels: the interprocedural LOAD direction, result side.
    reads_raw: bool,
    /// S8/S11 — the callee may read TYPED memory the CALLER's typed-read
    /// floor labels, so its RESULT joins that floor. Round 4 set this false
    /// for every NAMED callee on the premise that its typed reads reach only
    /// its own fresh cells or its parameters; that premise was FALSE — string
    /// literal bytes are SHARED static data (S11), so a callee's
    /// `"AAAAAAAA".byte_at(3)` reads the bytes the caller's raw store put
    /// there (2a / 07 end-to-end, the round-4 review). Now true for a named
    /// callee whose body performs ANY typed read — every intrinsic (hence
    /// every raw read), every heap-resident local, every projection, every
    /// `str` literal or f-string (`HeapScan::reads_typed`, transitive over the
    /// call graph) — and for the program-wide bound (a closure reads its
    /// captures with no argument at all). Fail closed and address-blind: a
    /// callee reading its OWN fresh aggregate is floored too (counted cost).
    reads_typed: bool,
    /// Upper bound on the label of anything this callee can have written from
    /// its OWN sources: every taint annotation reachable from it, plus
    /// @Internal if it can reach the host (an FFI result is @Internal by rule,
    /// not by annotation). Values that arrived as ARGUMENTS are not in here —
    /// the call site joins those in, where they are known exactly
    /// (`CallSummary::floors`).
    annotation: TaintLabel,
    /// S5 (region side) — the slots (captures first, then parameters) whose
    /// POINTER a raw write reachable from this callee can go THROUGH, so the
    /// call site can taint the corresponding argument's M6 region — the
    /// returned-pointer sink the floors do not see (a caller that never READS
    /// the byte but hands the buffer to the host). Transitive over the call
    /// graph through each edge's argument roots (`CallEdge`). `All` for the
    /// program-wide bound: every pointer handed over may have been written
    /// through (fail closed).
    writes_through: SlotSet,
}

impl CallSummary {
    /// Nothing observed — the bottom of the lattice the S5 closure ascends.
    const CLEAN: Self = Self {
        writes_memory: false,
        materializes: false,
        reads_raw: false,
        reads_typed: false,
        annotation: TaintLabel::Public,
        writes_through: SlotSet::NONE,
    };

    /// The summary of a callee this pass cannot name (an indirect call, a
    /// `perform`, an actor message, a name missing from the map): writes
    /// everything, reads everything, at the program-wide annotation bound.
    /// Fail closed.
    fn program_bound(program: &TypedProgram) -> Self {
        Self {
            writes_memory: true,
            materializes: true,
            reads_raw: true,
            reads_typed: true,
            annotation: scan_program(program).max_annotation,
            writes_through: SlotSet::All,
        }
    }

    /// Field-wise join — monotone, so the closure below terminates.
    fn lub(self, other: Self) -> Self {
        Self {
            writes_memory: self.writes_memory || other.writes_memory,
            materializes: self.materializes || other.materializes,
            reads_raw: self.reads_raw || other.reads_raw,
            reads_typed: self.reads_typed || other.reads_typed,
            annotation: self.annotation.lub(other.annotation),
            writes_through: self.writes_through.lub(other.writes_through),
        }
    }

    /// What a CALLER inherits from a callee it can reach: everything but
    /// `writes_through` — those are the CALLEE's slots, and which of the
    /// caller's own slots they map to is decided per edge through the call's
    /// argument roots in `call_summaries`, never by a bitwise union.
    fn absorb(self, callee: Self) -> Self {
        Self {
            writes_through: self.writes_through,
            ..self.lub(callee)
        }
    }

    /// S8 — the label of the CALLER's memory this callee can have read: the
    /// caller's raw-load floor if the callee raw-reads, its typed-read floor
    /// if the callee reads typed memory (S11: any typed read, since string
    /// literals are shared static data) or is unnamed. Joined into the call's
    /// result and into the site taint its writes are floored at (a callee that
    /// reads a floored cell and stores it into a `@Mut` argument hands the
    /// caller the same bytes through a typed read). @Public when S8 is off —
    /// the documented LOAD-direction gap.
    fn read_floor(self, floors: HeapFloors) -> TaintLabel {
        if !HEAP_FLOOR_CALLEE_READS {
            return TaintLabel::Public;
        }
        let mut label = TaintLabel::Public;
        if self.reads_raw {
            label = label.lub(floors.raw_load);
        }
        if self.reads_typed {
            label = label.lub(floors.typed_read);
        }
        label
    }

    /// The floors a CALL SITE raises. `site_taint` is the join over the
    /// arguments AND the call site's effective pc: a callee that writes memory
    /// can have written any label that reached it — as a VALUE, as an INDEX or
    /// field ADDRESS (`a[s & 1] = 1` with `s` an argument), or simply by being
    /// called under a secret branch — and those labels are known exactly here,
    /// which is what makes this sound for a `@Flow` callee (whose own
    /// annotations are placeholders) and precise for a callee that only moves
    /// @Public bytes. What the callee MINTS itself (`let s: i64 @Secret` it
    /// then writes, as a value or as an index) is covered by `annotation`.
    ///
    /// BOTH floors rise on `writes_memory`. Round 2 raised `typed_read` only
    /// for a callee that could RAW-store, on the reasoning that a typed write
    /// is bounds-checked into its own aggregate — true, but that aggregate can
    /// be the CALLER's, handed over as a `@Mut` parameter: `fn poke(a: [i64; 2]
    /// @Mut) { let s: i64 @Secret = 42; a[0] = s; }`, then `a[0]` in the caller
    /// read the secret back as @Public (verified end-to-end with `sigil forge`
    /// on the round-2 branch AND on main at ae026aec: 42 bytes of output for
    /// secret 42 and 7 for 7; the `a[s & 1] = 1` index form leaked the bit as
    /// 0 vs 1 byte).
    ///
    /// FAILURE DIRECTION: fail closed, and imprecise in two measured ways. The
    /// floor is not tied to the aggregate the callee wrote, so EVERY typed read
    /// after such a call is floored, not only reads of the `@Mut` argument; and
    /// `annotation` is a syntactic bound, so a callee that mentions a secret it
    /// never writes still raises the floor. The second cost is pinned by
    /// `callee_that_mentions_a_secret_but_writes_public_is_a_counted_false_positive`.
    ///
    /// Round 4: a callee that only MATERIALIZES (builds a fresh aggregate and
    /// stores nothing at an existing address) raises the raw-load floor alone,
    /// mirroring the intraprocedural S2 note — fresh cells overlap no live
    /// typed value, so the typed-read floor is untouched.
    fn floors(self, site_taint: TaintLabel) -> HeapFloors {
        let written = self.annotation.lub(site_taint);
        HeapFloors {
            raw_load: if self.writes_memory || self.materializes {
                written
            } else {
                TaintLabel::Public
            },
            typed_read: if self.writes_memory {
                written
            } else {
                TaintLabel::Public
            },
        }
    }
}

/// S6 (typed side) — the taint of the ADDRESS an assignment writes through:
/// the index and slice-bound expressions in the place chain, which choose WHICH
/// cell changes. The place's leaf object is NOT walked — its label is the
/// container's, which the root rules above already handle — and the diagnostics
/// the index expressions would raise are DISCARDED into a local sink.
///
/// FAILURE DIRECTION, twice over. (1) Discarding: this pass has never walked an
/// assignment's place at all, so emitting those diagnostics here would be a new
/// diagnostic surface rather than a floor fix; the consequence is that a sink
/// violation written inside an assignment place's index never becomes a taint
/// diagnostic — the formal bridge rejects such a program as an I-class
/// integrity failure instead, on main as much as here (pinned by
/// `secret_in_an_assignment_place_index_is_an_integrity_error_not_a_taint_one`).
/// (2) The `_` arm: a place form not listed contributes no address taint, so a
/// future place kind with an index-like operand would not raise the floor —
/// `Local`/`StateField` are the only leaves the assignment arms above admit.
fn place_address_taint(
    place: &TypedExpr,
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
) -> TaintLabel {
    let mut sink = Vec::new();
    match &place.kind {
        TypedExprKind::Index(i) => place_address_taint(&i.array, env, current_fn, program).lub(
            compute_expr_taint(&i.index, env, current_fn, program, &mut sink),
        ),
        TypedExprKind::FieldAccess(f) => place_address_taint(&f.object, env, current_fn, program),
        TypedExprKind::Slice(s) => {
            let mut acc = place_address_taint(&s.array, env, current_fn, program);
            for bound in [s.start.as_ref(), s.end.as_ref()].into_iter().flatten() {
                acc = acc.lub(compute_expr_taint(
                    bound, env, current_fn, program, &mut sink,
                ));
            }
            acc
        }
        _ => TaintLabel::Public,
    }
}

/// One function's own syntactic facts (S5), before the call-graph closure.
/// `@Flow` positions are skipped for the same reason `scan_program` skips them
/// — an instantiation placeholder is not a source — and the label that
/// instantiates them reaches the floor through `args_taint` at the call site.
fn scan_function(f: &TypedFunction) -> HeapScan {
    let mut acc = HeapScan::empty();
    for p in f.params.iter().chain(f.captures.iter()) {
        if !p.flow {
            acc.max_annotation = acc.max_annotation.lub(p.taint);
        }
    }
    if !f.ret_flow {
        acc.max_annotation = acc.max_annotation.lub(f.ret_taint);
    }
    // S5 (region side): the SLOTS a raw write can go through — captures first
    // (an actor's state fields, a lifted closure's captured locals), then the
    // parameters — seed the rooted set. A slot past the 64-bit mask is `All`
    // (fail closed).
    for (slot, p) in f.captures.iter().chain(f.params.iter()).enumerate() {
        acc.rooted.insert(p.name.clone(), SlotSet::slot(slot));
    }
    // `rooted` is a fixpoint, not a single pass: a local bound BEFORE a loop
    // whose back-edge rebinds it (`let q = alloc(1); while c { store8(q, s);
    // q = p; }`) is unrooted when the store is first scanned, so the write
    // would be attributed to nothing. Re-scan until no name gains a slot and
    // take every attribution from the LAST pass, whose rooted set is complete.
    // Every changed pass adds at least one slot bit (or `All`) to one of the
    // names present after the first pass, so 65 × names + 2 passes suffice.
    // FAILURE DIRECTION: a body that runs out of that bound is one this scan
    // does not understand — every slot is written through (`All`), never fewer.
    let mut passes = 0usize;
    loop {
        let before = acc.rooted.clone();
        acc.restart_pass();
        scan_stmts(&f.body.statements, &mut acc);
        if acc.rooted == before {
            break;
        }
        passes += 1;
        if passes > 65 * acc.rooted.len() + 2 {
            acc.writes_through = SlotSet::All;
            break;
        }
    }
    acc
}

/// The height of one `CallSummary` in its lattice: four flags, three label
/// steps, and 64 slot bits plus `All`. Times the number of functions, it
/// bounds the closure below.
const CALL_SUMMARY_HEIGHT: usize = 4 + 3 + 65;

/// S5 — the call-graph closure: every function's summary joined with those of
/// everything it can reach. Monotone over a lattice of height
/// `CALL_SUMMARY_HEIGHT` per function, so the bounded loop below converges;
/// the bound is a guard, not a hope.
fn call_summaries(program: &TypedProgram) -> HashMap<String, CallSummary> {
    let program_bound = CallSummary::program_bound(program);
    let direct: HashMap<String, HeapScan> = program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .map(|f| (f.name.clone(), scan_function(f)))
        .collect();
    // S5 (region side): a named callee's PARAMETER slots start after its
    // capture slots, so an edge's argument index maps to slot
    // `captures + index`.
    let capture_slots: HashMap<&str, usize> = program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .map(|f| (f.name.as_str(), f.captures.len()))
        .collect();

    let mut out: HashMap<String, CallSummary> = direct
        .iter()
        .map(|(name, scan)| {
            let mut summary = CallSummary {
                writes_memory: scan.writes_memory,
                materializes: scan.materializes,
                reads_raw: scan.reads_raw,
                // S11: any typed read in the body reads memory the caller's
                // floor may label (shared static data at the least). With the
                // switch off this is round 4's false premise — the hole.
                reads_typed: HEAP_FLOOR_STATIC_READS && scan.reads_typed,
                // An FFI result is @Internal by RULE, not by annotation, so a
                // callee that calls the host can store a label no annotation in
                // it mentions. S1 already floors the caller's raw loads for such
                // a callee; this is what floors its TYPED reads when the callee
                // raw-stores host bytes at an address the caller handed it.
                annotation: if scan.has_extern_call {
                    scan.max_annotation.lub(TaintLabel::Internal)
                } else {
                    scan.max_annotation
                },
                writes_through: scan.writes_through,
            };
            if scan.unknown_call {
                // The unnamed callee's WRITES and READS take the program-wide
                // bound. WHICH of this function's slots it can write through is
                // already the join of every pointer handed to it (the scan's
                // unknown-call arms), so that field keeps the per-site answer:
                // the bound at the level the scan can see, not `All` — which
                // would name slots the callee never received.
                let writes_through = summary.writes_through;
                summary = summary.lub(program_bound);
                summary.writes_through = writes_through;
            }
            (name.clone(), summary)
        })
        .collect();

    let rounds = direct
        .len()
        .saturating_mul(CALL_SUMMARY_HEIGHT)
        .saturating_add(4);
    for _ in 0..rounds {
        let mut changed = false;
        for (name, scan) in &direct {
            let mut acc = out.get(name).copied().unwrap_or(CallSummary::CLEAN);
            for callee in &scan.calls {
                // A callee with no entry here is a name this pass cannot
                // resolve — fail closed with the program-wide bound.
                acc = acc.absorb(out.get(callee).copied().unwrap_or(program_bound));
            }
            // S5 (region side): a slot of THIS function is written through if
            // some callee writes through the slot one of its arguments fills —
            // then through that argument's own roots. `All` on the callee
            // covers every position, so every rooted argument is taken.
            for edge in &scan.call_arg_roots {
                let callee = out.get(&edge.callee).copied().unwrap_or(program_bound);
                let base = if edge.params {
                    capture_slots
                        .get(edge.callee.as_str())
                        .copied()
                        .unwrap_or(0)
                } else {
                    0
                };
                for (index, roots) in edge.arg_roots.iter().enumerate() {
                    if callee.writes_through.covers(base + index) {
                        acc.writes_through = acc.writes_through.lub(*roots);
                    }
                }
            }
            if out.get(name) != Some(&acc) {
                out.insert(name.clone(), acc);
                changed = true;
            }
        }
        if !changed {
            return out;
        }
    }
    // FAILURE DIRECTION: a closure that did not converge inside its own bound
    // means this pass does not understand the call graph, so every function
    // takes the program-wide bound — fail closed, never cheaper.
    out.into_keys().map(|k| (k, program_bound)).collect()
}

thread_local! {
    /// S5 — the call summaries of the program currently being checked, armed by
    /// `CallSummaryScope` at the two entry points. `None` means NOT armed.
    static CALL_SUMMARIES: RefCell<Option<HashMap<String, CallSummary>>> =
        const { RefCell::new(None) };
}

/// Arms `CALL_SUMMARIES` for one program and clears it on drop, so a map from
/// another program can never outlive its pass (an early return, a `?`, or a
/// panic all clear it). Nesting clears on the INNER drop: the outer pass then
/// falls back to the program-wide bound — fail closed, never cheaper.
struct CallSummaryScope;

impl CallSummaryScope {
    fn arm(program: &TypedProgram) -> Self {
        if HEAP_FLOOR_CALLEE_WRITES {
            let summaries = call_summaries(program);
            CALL_SUMMARIES.with(|cell| *cell.borrow_mut() = Some(summaries));
        }
        // S10 runs handler bodies, whose call sites read the summaries above,
        // so it is armed second and cleared with them.
        if HEAP_FLOOR_ACTOR_DISPATCH {
            let floors = actor_dispatch_floors(program);
            ACTOR_FLOORS.with(|cell| *cell.borrow_mut() = Some(floors));
        }
        Self
    }
}

impl Drop for CallSummaryScope {
    fn drop(&mut self) {
        CALL_SUMMARIES.with(|cell| *cell.borrow_mut() = None);
        ACTOR_FLOORS.with(|cell| *cell.borrow_mut() = None);
    }
}

thread_local! {
    /// S10 — the dispatch floors of every actor in the program being checked,
    /// armed by `CallSummaryScope` after the call summaries. `None` = NOT armed.
    static ACTOR_FLOORS: RefCell<Option<HashMap<String, HeapFloors>>> =
        const { RefCell::new(None) };
}

/// The actor a function belongs to, if it is that actor's `init` or one of
/// its message handlers. Total over `TypedFunctionKind` (no `_` arm).
fn actor_of(function: &TypedFunction) -> Option<&str> {
    use crate::typed_ast::TypedFunctionKind;
    match &function.kind {
        TypedFunctionKind::ActorInit { actor, .. }
        | TypedFunctionKind::ActorHandler { actor, .. } => Some(actor),
        TypedFunctionKind::ModuleInit
        | TypedFunctionKind::ModuleFunction
        | TypedFunctionKind::Closure => None,
    }
}

/// S10 — the floors every `init`/handler of each actor starts at: the least
/// fixpoint of "run every one of them once more from the current floors and
/// join what they leave behind". The `while`/`for` fixpoints carry the floors
/// across ITERATIONS; the actor dispatch loop — persistent `mut` state
/// re-entered per message, in an order the checker does not track — carried
/// nothing, so a handler that wrote `buf[s & 1] = 1` under a condition and a
/// handler that read `buf[0]` first (or another handler entirely) read the
/// secret's bit back at a clean floor (round-3 review; the two-handler forms
/// `buf[s & 1] = 1` / `store8(4096, s)` then `buf[0]` / `load8(4096)` too).
/// Bodies are walked with a discarded diagnostic sink — the real diagnostics
/// are emitted by `check_function` from the converged entry — and `@Flow`
/// positions are instantiated at @Secret (fail closed: the label that
/// instantiates them is a message payload this pass does not see).
///
/// FAILURE DIRECTION: fail closed, and imprecise the same way S7 is — the
/// floors are per ACTOR, not per state cell, so one handler's secret write
/// floors every state read in every handler of that actor. The corpus cost
/// is measured (2 tool actors carry state at all). A fixpoint that does not
/// converge inside its bound means the floors are not monotone — a bug —
/// and that actor takes the top floors rather than the last iterate.
fn actor_dispatch_floors(program: &TypedProgram) -> HashMap<String, HeapFloors> {
    let mut by_actor: BTreeMap<&str, Vec<&TypedFunction>> = BTreeMap::new();
    for function in program.modules.iter().flat_map(|m| m.functions.iter()) {
        if let Some(actor) = actor_of(function) {
            by_actor.entry(actor).or_default().push(function);
        }
    }
    let entry = program_entry_floors(program);
    by_actor
        .into_iter()
        .map(|(actor, functions)| {
            let mut floors = entry;
            // Two floors, each raised at most three times (the lattice has four
            // labels): six non-converging rounds at most, so eight suffice.
            for _ in 0..8 {
                let mut next = floors;
                for function in &functions {
                    next = next.lub(function_exit_floors(function, program, floors));
                }
                if next == floors {
                    return (actor.to_owned(), floors);
                }
                floors = next;
            }
            (
                actor.to_owned(),
                HeapFloors {
                    raw_load: TaintLabel::Secret,
                    typed_read: TaintLabel::Secret,
                },
            )
        })
        .collect()
}

/// S10 — the floors one `init`/handler body leaves behind when entered at
/// `entry`: the same walk `check_function_body` makes, into a discarded sink.
fn function_exit_floors(
    function: &TypedFunction,
    program: &TypedProgram,
    entry: HeapFloors,
) -> HeapFloors {
    let mut instance = function.clone();
    for param in &mut instance.params {
        if param.flow {
            param.taint = TaintLabel::Secret;
        }
    }
    if instance.ret_flow {
        instance.ret_taint = TaintLabel::Secret;
    }
    let mut env = function_entry_env(&instance, entry);
    let mut sink = Vec::new();
    check_block(&instance.body, &mut env, &instance, program, &mut sink);
    env.floors
}

/// S10 — the entry floors of `function`: its actor's dispatch floors if it is
/// an `init` or a handler, else the program-wide entry floors (S3). FAILURE
/// DIRECTION: an actor missing from an armed map, or a map that is not armed
/// at all, is a bug in this pass, and the function then starts at the TOP
/// floors — every state read is rejected rather than any accepted.
fn function_entry_floors(function: &TypedFunction, program: &TypedProgram) -> HeapFloors {
    let Some(actor) = actor_of(function) else {
        return program_entry_floors(program);
    };
    if !HEAP_FLOOR_ACTOR_DISPATCH {
        return program_entry_floors(program);
    }
    ACTOR_FLOORS
        .with(|cell| cell.borrow().as_ref().and_then(|m| m.get(actor).copied()))
        .unwrap_or(HeapFloors {
            raw_load: TaintLabel::Secret,
            typed_read: TaintLabel::Secret,
        })
}

/// S5 (region side) — a callee that can raw-write THROUGH a pointer it was
/// handed has written into that pointer's M6 REGION, exactly as the inline
/// `RawWrite` arm records for the caller's own stores. The floors cover every
/// READ of those bytes; this covers the pointer itself REACHING a sink unread:
/// `tool_main` returning `out << 32 | n` hands the host the buffer a callee
/// filled with a @Secret it minted (`sigil check` accepted it and `sigil forge`
/// printed the bit on main — the round-6 review's seventh channel). `written`
/// is the label the floors take: the callee's annotation bound joined with the
/// site taint (arguments, pc, and what the callee may have read). Slots are
/// numbered captures-first, so a named callee's arguments start at
/// `slot_base` = its capture count. FAILURE DIRECTION: `All` (an unnamed
/// callee, an oversized slot index, a scan that did not converge) taints EVERY
/// argument that has a region — fail closed. An argument WITHOUT a region is
/// not reached, and that is the OPEN surface `CLAIMS.md` §C HF-1 discloses,
/// not a decision that it is clean: the M6 model regions only locals bound to
/// `alloc`, or to `+`/`-` arithmetic over `alloc` calls and regioned locals
/// (`regions_of_bound_value`), so a write through ANY other pointer expression —
/// a parameter of the caller (including `tool_main`'s own `input_ptr`, the
/// host's buffer), a callee's result, other arithmetic, a constant, a pointer
/// reloaded from memory or read out of an aggregate or a state field — is
/// attributed to no region here, exactly as the inline arm attributes it to
/// none. An argument with SEVERAL candidate regions (rebound on one path of a
/// merge) taints every candidate.
fn taint_written_argument_regions(
    env: &mut TaintEnv,
    summary: CallSummary,
    slot_base: usize,
    args: &[TypedExpr],
    written: TaintLabel,
) {
    if written <= TaintLabel::Public {
        return;
    }
    for (index, arg) in args.iter().enumerate() {
        if summary.writes_through.covers(slot_base + index) {
            for region in env.region_of_expr(arg) {
                env.taint_region(region, written);
            }
        }
    }
}

/// The S5 summary of `name`. FAILURE DIRECTION: with no map armed, or with the
/// name absent from it, the caller takes the program-wide bound — fail closed,
/// never cheaper than the computed summary.
fn call_summary(name: &str, program: &TypedProgram) -> CallSummary {
    CALL_SUMMARIES
        .with(|cell| cell.borrow().as_ref().and_then(|m| m.get(name).copied()))
        .unwrap_or_else(|| CallSummary::program_bound(program))
}

/// Whether a value of static type `ty` lives in linear memory — EXACTLY the
/// types `air::lower_type` lowers to `AirType::Ptr` (a pointer local whose
/// payload is a heap cell). Total over `Type` (no `_` arm): a new variant must
/// be classified here or this fails to compile. Check-time-only variants that
/// `lower_type` ICEs on (`Generic`, HKT, markers, `Never`) are classified as
/// heap-resident — fail closed — since an unerased one cannot be proven scalar.
fn is_heap_resident(ty: &crate::type_check::Type) -> bool {
    use crate::type_check::Type;
    match ty {
        Type::Unit
        | Type::Error
        | Type::Bool
        | Type::I32
        | Type::U32
        | Type::I64
        | Type::U64
        | Type::F64
        | Type::IntLit(_)
        | Type::Region => false,
        Type::U256
        | Type::I256
        | Type::Str
        | Type::Named(_, _)
        | Type::Cap(_, _)
        | Type::ActorRef(_)
        | Type::Generic(_)
        | Type::Array { .. }
        | Type::Tuple(_)
        | Type::Fn(_, _, _, _)
        | Type::Ref(_, _)
        | Type::Slice(_)
        | Type::Ptr(_)
        | Type::MutPtr(_)
        | Type::HktVar { .. }
        | Type::HktApp { .. }
        | Type::TypeCtor(_)
        | Type::StateMarker(_)
        | Type::Never => true,
    }
}

/// S4 — whether evaluating `expr` READS bytes of a live typed value out of
/// linear memory, i.e. bytes a raw store could have overwritten: an element /
/// field / slice / `?` projection, any intrinsic (they operate over aggregates
/// and their results are extracted from memory), a plain use of a
/// heap-resident local (the whole value is its bytes), ANY state field read
/// (S10 — a state cell is a cell of the persistent heap whatever its type: a
/// scalar `count` lives behind the state pointer, not in a wasm local, so a
/// raw store in another handler can clobber it), and — S11 — a `str` literal
/// or an f-string: its bytes are SHARED static data placed once at
/// `STATIC_DATA_BASE` and never re-initialized, so `"AAAAAAAA" ==
/// "AAABAAAA"` after a raw store into them observes the store (verified
/// end-to-end on main). Every other kind either computes on wasm locals or
/// MATERIALIZES a fresh cell, which no earlier store can have touched. Total
/// over `TypedExprKind` and over `Literal` (an `Int256` literal builds a
/// fresh 32-byte cell from immediates; only `Str` points into static data).
fn reads_typed_memory(expr: &TypedExpr) -> bool {
    match &expr.kind {
        TypedExprKind::Index(_)
        | TypedExprKind::FieldAccess(_)
        | TypedExprKind::Slice(_)
        | TypedExprKind::Try(_)
        | TypedExprKind::Intrinsic(_)
        | TypedExprKind::StateField(_) => true,
        TypedExprKind::Local(_) => is_heap_resident(&expr.ty),
        // S11: with the switch off, a literal is not a read — round 4's hole.
        TypedExprKind::Literal(lit) => HEAP_FLOOR_STATIC_READS && literal_reads_static(lit),
        TypedExprKind::FString(_) => HEAP_FLOOR_STATIC_READS,
        TypedExprKind::Binary(_)
        | TypedExprKind::Call(_)
        | TypedExprKind::ArrayLit(_)
        | TypedExprKind::RecordConstruct(_)
        | TypedExprKind::EnumConstruct(_)
        | TypedExprKind::ClosureConstruct(_)
        | TypedExprKind::Borrow(_)
        | TypedExprKind::Grant(_)
        | TypedExprKind::Handle(_)
        | TypedExprKind::Perform(_)
        | TypedExprKind::ClauseHandle(_)
        | TypedExprKind::Resume(_)
        | TypedExprKind::Declassify(_)
        | TypedExprKind::DeclassifyCt(_)
        | TypedExprKind::ResultCtor(_)
        | TypedExprKind::Send(_)
        | TypedExprKind::Ask(_)
        | TypedExprKind::Spawn(_)
        | TypedExprKind::CapSplit(_)
        | TypedExprKind::CapDraw(_)
        | TypedExprKind::CapRestrict(_)
        | TypedExprKind::Mint(_)
        | TypedExprKind::ExternCall(_)
        | TypedExprKind::IndirectCall(_)
        | TypedExprKind::Region(_) => false,
    }
}

/// S11 — whether a literal's VALUE lives in the shared static-data segment
/// (`wasm.rs::collect_static_data` interns exactly `AirValue::StrLit`). Total
/// over `Literal` (no `_` arm).
fn literal_reads_static(lit: &crate::ast::Literal) -> bool {
    use crate::ast::Literal;
    match lit {
        Literal::Str(_) => true,
        Literal::Int(_) | Literal::Int256(_) | Literal::Float(_) | Literal::Bool(_) => false,
    }
}

/// S11 — whether matching `pattern` reads static bytes: a `str` literal
/// pattern compares the scrutinee against the interned literal
/// (`emit_str_bytes_eq_parts` over `AirValue::StrLit`, no header). The parser
/// does not admit a `str` pattern today (P018 at the arm), so this is a
/// fail-closed fence against a parser change, not a live arm. Total over
/// `TypedPattern` (no `_` arm).
fn pattern_reads_static(pattern: &crate::type_check::TypedPattern) -> bool {
    use crate::type_check::TypedPattern;
    match pattern {
        TypedPattern::Literal(lit) => literal_reads_static(lit),
        TypedPattern::Range { lo, hi } => literal_reads_static(lo) || literal_reads_static(hi),
        TypedPattern::Wildcard
        | TypedPattern::Binding(_)
        | TypedPattern::EnumVariant { .. }
        | TypedPattern::Array { .. } => false,
    }
}

/// Syntactic facts the S3 and S5 floors are built from. `scan_program`
/// accumulates them over a whole program; `scan_function` over one function's
/// own body (S5's per-callee summary, before the call-graph closure).
struct HeapScan {
    /// The lub of every taint annotation in the program: parameters, returns,
    /// captures (actor state), `let` labels, and effect-operation contracts.
    max_annotation: TaintLabel,
    has_extern_call: bool,
    /// S5 — a write into linear memory at an EXISTING address: a raw store, a
    /// slot write, or an assignment through a PROJECTED place (`a[i] = v`,
    /// `r.f = v`, both heap cells — possibly the CALLER's, handed over as a
    /// `@Mut` parameter). Raises BOTH caller floors.
    writes_memory: bool,
    /// S5 (round 4) — a heap-resident value is BUILT here: a record, array,
    /// enum, `Result`/`Option`, tuple, `str`, `u256`, closure, cap or ref
    /// materialized into FRESH cells. The intraprocedural S2 rule notes every
    /// such value at the choke point; this is its interprocedural twin, keyed
    /// on the same `is_heap_resident` predicate. A callee that only builds
    /// `[s, 0]` and returns 0 leaves `s` in memory for the caller's next raw
    /// load (verified end-to-end on main and round 3: 42 / 7 at byte 5 of a
    /// dump). Raises the caller's RAW-load floor only — fresh cells overlap no
    /// live typed value, exactly S2's argument.
    materializes: bool,
    /// S8 — a raw memory read (`IntrinsicMemory::RawRead`) is reachable from
    /// this callee: its result may carry bytes the CALLER's floor labels.
    reads_raw: bool,
    /// S11 — a TYPED memory read (`reads_typed_memory`: a projection, an
    /// intrinsic, a heap-resident local, a state field, a `str` literal or an
    /// f-string, or a `str` match pattern) is reachable from this callee. Its
    /// result may carry bytes the CALLER's typed-read floor labels: a string
    /// literal is SHARED static data, so a raw store in the caller lands in
    /// bytes the callee's `"…".byte_at(k)` reads back (round-4 review, 2a /
    /// 07 end-to-end). Coarse by choice — any typed read, not only literals.
    reads_typed: bool,
    /// S5 — a call whose target this scan cannot name: an indirect call, an
    /// effect `perform`, an actor `send`/`ask`/`spawn`, a `grant` of a closure
    /// that is not a literal. Fail closed: a summary with this set takes the
    /// PROGRAM-WIDE bound instead of a callee's.
    unknown_call: bool,
    /// S5 — the direct callees named in this body, for the call-graph closure.
    /// A closure LITERAL is an edge to its lifted body (S9): the body runs
    /// whenever the value is invoked, which this scan cannot place, so its
    /// construct site is where the edge lives (fail closed).
    calls: Vec<String>,
    /// S5 (region side) — the slots whose pointer a raw write IN THIS BODY
    /// goes through (the join of the roots of every operand of every raw
    /// write), plus every pointer handed to a callee this scan cannot name.
    /// The call-graph closure adds what named callees write through.
    writes_through: SlotSet,
    /// S5 (region side) — every call edge with its per-argument roots.
    call_arg_roots: Vec<CallEdge>,
    /// S5 (region side) — the slots each local is rooted in: seeded with the
    /// function's captures and parameters, grown (never shrunk) by every
    /// `let` / rebind whose value MENTIONS a rooted local anywhere. Every name
    /// a `let` binds is present (at `NONE` if unrooted), so `rooted.len()`
    /// bounds the fixpoint in `scan_function`.
    rooted: BTreeMap<String, SlotSet>,
    /// S5 (region side) — the running join of the rooted locals mentioned
    /// since `scan_roots` last reset it.
    mentioned: SlotSet,
}

impl HeapScan {
    /// A scan that has observed nothing. `max_annotation` @Public and every
    /// flag false is the BOTTOM of the lattice the S5 fixpoint ascends.
    fn empty() -> Self {
        Self {
            max_annotation: TaintLabel::Public,
            has_extern_call: false,
            writes_memory: false,
            materializes: false,
            reads_raw: false,
            reads_typed: false,
            unknown_call: false,
            calls: Vec::new(),
            writes_through: SlotSet::NONE,
            call_arg_roots: Vec::new(),
            rooted: BTreeMap::new(),
            mentioned: SlotSet::NONE,
        }
    }

    /// Clear what one pass of `scan_function` rebuilds from scratch (the
    /// edges and the attributions), keeping `rooted` — the fixpoint variable —
    /// and the idempotent flags.
    fn restart_pass(&mut self) {
        self.calls.clear();
        self.call_arg_roots.clear();
        self.writes_through = SlotSet::NONE;
        self.mentioned = SlotSet::NONE;
    }

    /// The slots a local is rooted in (`NONE` for a name never rooted).
    fn roots_of(&self, name: &str) -> SlotSet {
        self.rooted.get(name).copied().unwrap_or(SlotSet::NONE)
    }

    /// Root `name` in `roots` (a `let` or a rebind). Monotone: a later rebind
    /// to a fresh `alloc` does NOT clear an earlier root — the scan is
    /// flow-insensitive by choice, so a pointer that ever derived from a slot
    /// stays attributed to it (fail closed; the M6 env is the precise one).
    fn root(&mut self, name: &str, roots: SlotSet) {
        let slot = self.rooted.entry(name.to_owned()).or_insert(SlotSet::NONE);
        *slot = slot.lub(roots);
    }
}

/// S5 (region side) — the slots the locals mentioned ANYWHERE inside `expr`
/// are rooted in: `let q = p`, `let q = p + 8`, `let q = f(p)` and
/// `store8(p + i, v)` all mention `p`. Coarse and fail closed — a mention is
/// enough; no attempt is made to decide that a derived value is not a pointer
/// into the same region. The outer running join keeps what was mentioned so
/// far, so a nested `let` inside `expr` cannot lose an outer mention.
fn scan_roots(expr: &TypedExpr, acc: &mut HeapScan) -> SlotSet {
    let outer = std::mem::replace(&mut acc.mentioned, SlotSet::NONE);
    scan_expr(expr, acc);
    let roots = acc.mentioned;
    acc.mentioned = outer.lub(roots);
    roots
}

fn scan_program(program: &TypedProgram) -> HeapScan {
    let mut acc = HeapScan::empty();
    for module in &program.modules {
        for f in &module.functions {
            for p in f.params.iter().chain(f.captures.iter()) {
                // A `@Flow` parameter's label is an instantiation placeholder,
                // not a source: the real label must originate elsewhere.
                if !p.flow {
                    acc.max_annotation = acc.max_annotation.lub(p.taint);
                }
            }
            if !f.ret_flow {
                acc.max_annotation = acc.max_annotation.lub(f.ret_taint);
            }
            scan_stmts(&f.body.statements, &mut acc);
        }
    }
    for sigs in program.effect_ops.values() {
        for sig in sigs {
            for t in &sig.param_taints {
                acc.max_annotation = acc.max_annotation.lub(*t);
            }
        }
    }
    acc
}

/// Total over `TypedStmt` (no `_` arm): a forgotten statement kind is a
/// compile error, not a silently unscanned `let` annotation.
fn scan_stmts(stmts: &[TypedStmt], acc: &mut HeapScan) {
    for stmt in stmts {
        match stmt {
            TypedStmt::Let(s) => {
                if let Some(t) = s.taint {
                    acc.max_annotation = acc.max_annotation.lub(t);
                }
                // S5 (region side): the bound name is rooted wherever its value
                // mentions a rooted local (`let q = p + 8`).
                let roots = scan_roots(&s.value, acc);
                acc.root(&s.name, roots);
            }
            TypedStmt::Assign(s) => {
                // S5: a bare `x = v` rebinds a local (a wasm local or a scalar
                // stack slot); ANY other place — `a[i] = v`, `r.f = v`, an actor
                // state field — writes a cell in linear memory. Fail closed: the
                // default arm is the memory-writing one.
                if !matches!(s.place.kind, TypedExprKind::Local(_)) {
                    acc.writes_memory = true;
                }
                scan_expr(&s.place, acc);
                let roots = scan_roots(&s.value, acc);
                // S5 (region side): a rebind roots the local like a `let`. A
                // pointer stored INTO memory (`a[0] = p`) is not tracked by any
                // slot — the unregioned-pointer boundary the block comment
                // discloses (HF-1).
                if let TypedExprKind::Local(name) = &s.place.kind {
                    acc.root(name, roots);
                }
            }
            TypedStmt::Expr(s) => scan_expr(&s.expr, acc),
            TypedStmt::If(s) => {
                scan_expr(&s.condition, acc);
                scan_stmts(&s.then_branch.statements, acc);
                scan_stmts(&s.else_branch.statements, acc);
            }
            TypedStmt::Match(s) => {
                scan_expr(&s.scrutinee, acc);
                for arm in &s.arms {
                    // S11: a `str` literal pattern reads the interned literal.
                    if pattern_reads_static(&arm.pattern) {
                        acc.reads_typed = true;
                    }
                    if let Some(g) = &arm.guard {
                        scan_expr(g, acc);
                    }
                    scan_stmts(&arm.body.statements, acc);
                }
            }
            TypedStmt::While(s) => {
                scan_expr(&s.condition, acc);
                scan_stmts(&s.body.statements, acc);
            }
            TypedStmt::ForIn(s) => {
                scan_expr(&s.iterable, acc);
                scan_stmts(&s.body, acc);
            }
            TypedStmt::ForRange(s) => {
                scan_expr(&s.start, acc);
                scan_expr(&s.end, acc);
                scan_stmts(&s.body, acc);
            }
            TypedStmt::Return(s) => {
                if let Some(v) = &s.value {
                    scan_expr(v, acc);
                }
            }
            TypedStmt::Break(_) | TypedStmt::Continue(_) => {}
        }
    }
}

/// Total over `TypedExprKind` (no `_` arm), descending into every nested
/// block so a `let` annotation inside a `handle`/`region`/`grant` body and an
/// extern call anywhere are both seen. Closure BODIES are separate lifted
/// functions in `module.functions`, scanned by `scan_program` directly and
/// reached from their construct site as a call edge (S9).
fn scan_expr(expr: &TypedExpr, acc: &mut HeapScan) {
    // S11: the interprocedural twin of the S4 choke point, keyed on the same
    // predicate — a typed read here is a read of memory the CALLER's floor may
    // label (shared static data at the least), so the result carries it.
    if reads_typed_memory(expr) {
        acc.reads_typed = true;
    }
    // S5 (round 4): the interprocedural twin of the S2 choke point, keyed on
    // the same predicate — any heap-resident value that is not a plain re-read
    // of a local or state field was BUILT into fresh cells here.
    if is_heap_resident(&expr.ty)
        && !matches!(
            expr.kind,
            TypedExprKind::Local(_) | TypedExprKind::StateField(_)
        )
    {
        acc.materializes = true;
    }
    match &expr.kind {
        TypedExprKind::Literal(_)
        | TypedExprKind::StateField(_)
        | TypedExprKind::CapRestrict(_) => {}
        TypedExprKind::Local(name) => {
            // S5 (region side): a mention of a rooted local — what `scan_roots`
            // collects for the enclosing `let`, argument or store operand.
            acc.mentioned = acc.mentioned.lub(acc.roots_of(name));
        }
        TypedExprKind::ClosureConstruct(c) => {
            // S9: the lifted body is a callee this scan CAN name; it runs
            // whenever the closure is invoked (here, for a `grant`; anywhere
            // later, for a stored closure), so its writes and reads are this
            // function's. Fail closed: the edge is taken even if the closure is
            // never called.
            acc.calls.push(c.synthesized_name.clone());
            // S5 (region side): the lifted body's CAPTURE slots (numbered first
            // in its own scan) are filled by these locals, so a write through a
            // captured pointer is a write through whatever these are rooted in.
            // The closure VALUE mentions its captures too: a local holding it
            // (`let f = fn..`, later `grant`ed or called indirectly) inherits
            // their roots.
            let roots: Vec<SlotSet> = c
                .captures
                .iter()
                .map(|cap| acc.roots_of(&cap.name))
                .collect();
            for r in &roots {
                acc.mentioned = acc.mentioned.lub(*r);
            }
            acc.call_arg_roots.push(CallEdge {
                callee: c.synthesized_name.clone(),
                arg_roots: roots,
                params: false,
            });
        }
        TypedExprKind::Call(c) => {
            // S5: a named callee — the edge the call-graph closure walks, with
            // each argument's roots for the region side.
            acc.calls.push(c.callee.clone());
            let roots: Vec<SlotSet> = c.args.iter().map(|a| scan_roots(a, acc)).collect();
            acc.call_arg_roots.push(CallEdge {
                callee: c.callee.clone(),
                arg_roots: roots,
                params: true,
            });
        }
        TypedExprKind::Intrinsic(i) => {
            // S5/S8: the ONE classification the intraprocedural arm also uses
            // (`intrinsic_memory`, total over the enum). A raw or checked write
            // raises both caller floors (`CallSummary::floors`); a raw read
            // marks the result as carrying the caller's raw-load floor.
            let mut operands = SlotSet::NONE;
            for a in &i.args {
                operands = operands.lub(scan_roots(a, acc));
            }
            match intrinsic_memory(&i.kind) {
                IntrinsicMemory::RawRead => acc.reads_raw = true,
                IntrinsicMemory::RawWrite => {
                    acc.writes_memory = true;
                    // S5 (region side): the write goes THROUGH the pointer that
                    // roots its address. WHICH operand is the address is not
                    // consulted — the join over every operand keeps this total
                    // over the operand list, exactly as the floors do; a pointer
                    // passed as the VALUE is over-attributed (fail closed).
                    acc.writes_through = acc.writes_through.lub(operands);
                }
                IntrinsicMemory::CheckedWrite => acc.writes_memory = true,
                IntrinsicMemory::Inert => {}
            }
        }
        TypedExprKind::ResultCtor(r) => scan_expr(&r.value, acc),
        TypedExprKind::EnumConstruct(e) => {
            for f in &e.fields {
                scan_expr(f, acc);
            }
        }
        TypedExprKind::Try(t) => scan_expr(&t.value, acc),
        TypedExprKind::Send(s) => {
            // S5: an actor handler is not a named callee here — fail closed.
            // Region side: it may write through every pointer handed to it.
            acc.unknown_call = true;
            for a in &s.args {
                let handed = scan_roots(a, acc);
                acc.writes_through = acc.writes_through.lub(handed);
            }
        }
        TypedExprKind::Ask(a) => {
            acc.unknown_call = true;
            for x in &a.args {
                let handed = scan_roots(x, acc);
                acc.writes_through = acc.writes_through.lub(handed);
            }
            scan_expr(&a.timeout, acc);
        }
        TypedExprKind::Spawn(s) => {
            acc.unknown_call = true;
            for a in &s.args {
                let handed = scan_roots(a, acc);
                acc.writes_through = acc.writes_through.lub(handed);
            }
        }
        TypedExprKind::Binary(b) => {
            scan_expr(&b.lhs, acc);
            scan_expr(&b.rhs, acc);
        }
        TypedExprKind::RecordConstruct(r) => {
            for (_, e) in &r.fields {
                scan_expr(e, acc);
            }
        }
        TypedExprKind::FieldAccess(f) => scan_expr(&f.object, acc),
        TypedExprKind::CapSplit(s) => scan_expr(&s.amount, acc),
        TypedExprKind::CapDraw(d) => scan_expr(&d.amount, acc),
        TypedExprKind::Mint(m) => scan_expr(&m.target, acc),
        TypedExprKind::ArrayLit(a) => {
            for e in &a.elements {
                scan_expr(e, acc);
            }
        }
        TypedExprKind::Index(i) => {
            scan_expr(&i.array, acc);
            scan_expr(&i.index, acc);
        }
        TypedExprKind::Slice(s) => {
            scan_expr(&s.array, acc);
            if let Some(e) = &s.start {
                scan_expr(e, acc);
            }
            if let Some(e) = &s.end {
                scan_expr(e, acc);
            }
        }
        TypedExprKind::Borrow(b) => scan_expr(&b.inner, acc),
        TypedExprKind::Grant(g) => {
            scan_expr(&g.cap, acc);
            // S9: a closure LITERAL body is reached as a call edge by the
            // `ClosureConstruct` arm above; any other body (a local holding a
            // closure) names no target this scan can follow — fail closed.
            // Region side: that local's roots are its captures' (the construct
            // arm mentions them), and the body may write through them all.
            let handed = scan_roots(&g.body, acc);
            if !matches!(g.body.kind, TypedExprKind::ClosureConstruct(_)) {
                acc.unknown_call = true;
                acc.writes_through = acc.writes_through.lub(handed);
            }
        }
        TypedExprKind::Handle(h) => scan_stmts(&h.body.statements, acc),
        TypedExprKind::Perform(p) => {
            // S5: the handler clause that runs this operation is chosen
            // dynamically — not a named callee. Fail closed, and on the region
            // side it may write through every pointer handed to it.
            acc.unknown_call = true;
            for a in &p.args {
                let handed = scan_roots(a, acc);
                acc.writes_through = acc.writes_through.lub(handed);
            }
        }
        TypedExprKind::ClauseHandle(c) => {
            scan_expr(&c.scrutinee, acc);
            for clause in &c.clauses {
                scan_stmts(&clause.body.statements, acc);
            }
        }
        TypedExprKind::Resume(r) => scan_expr(&r.value, acc),
        TypedExprKind::Declassify(d) => {
            scan_expr(&d.value, acc);
            scan_expr(&d.cap, acc);
        }
        TypedExprKind::DeclassifyCt(d) => {
            scan_expr(&d.value, acc);
            scan_expr(&d.cap, acc);
        }
        TypedExprKind::ExternCall(e) => {
            acc.has_extern_call = true;
            for a in &e.args {
                scan_expr(a, acc);
            }
        }
        TypedExprKind::Region(r) => {
            scan_expr(&r.limit, acc);
            scan_stmts(&r.body.statements, acc);
        }
        TypedExprKind::IndirectCall(c) => {
            // S5: `Type::Fn` names no target — fail closed, exactly as S1 does
            // for the FFI question at an indirect call. Region side: the body
            // may write through every argument AND through the captures the
            // closure local is rooted in.
            acc.unknown_call = true;
            let mut handed = acc.roots_of(&c.callee_local);
            for a in &c.args {
                handed = handed.lub(scan_roots(a, acc));
            }
            acc.writes_through = acc.writes_through.lub(handed);
        }
        TypedExprKind::FString(fs) => {
            for p in &fs.parts {
                if let crate::typed_ast::TypedFStringPart::Hole(h) = p {
                    scan_expr(h, acc);
                }
            }
        }
    }
}

fn bind_pattern_taint(
    pattern: &crate::type_check::TypedPattern,
    taint: TaintLabel,
    env: &mut TaintEnv,
) {
    use crate::type_check::TypedPattern;
    match pattern {
        TypedPattern::Binding(name) => {
            env.bind(name, taint);
        }
        TypedPattern::EnumVariant { bindings, .. } => {
            for (name, _) in bindings {
                env.bind(name, taint);
            }
        }
        // Array/slice destructuring (Phase 5): each named element and the named
        // rest slice inherit the scrutinee's taint (they are values read out of it).
        TypedPattern::Array {
            elem_binds, rest, ..
        } => {
            for (name, _) in elem_binds {
                if let Some(name) = name {
                    env.bind(name, taint);
                }
            }
            if let Some((Some(rest_name), _)) = rest {
                env.bind(rest_name, taint);
            }
        }
        TypedPattern::Literal(_) | TypedPattern::Range { .. } | TypedPattern::Wildcard => {}
    }
}

/// Compute the taint of an expression. Folds in pc_taint via lub.
/// CT enforcement (CT005–CT007, CT010, CT014, CT015, CT017) emits
/// diagnostics at the point of detection. See `docs/specs/secret-ct.md`
/// §3.2 and §10.
///
/// HEAP FLOOR choke point (BUG-2): every expression passes through
/// here exactly once, so the two type-keyed rules live here and nowhere else —
/// S4 floors the result of a typed memory read, and S2 notes a heap-resident
/// value as a memory write. The per-kind logic is in
/// `compute_expr_taint_unfloored`; keeping the floors out of it means an arm
/// with an early `return` cannot skip them.
fn compute_expr_taint(
    expr: &TypedExpr,
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) -> TaintLabel {
    let mut taint = compute_expr_taint_unfloored(expr, env, current_fn, program, diagnostics);
    // S4: the bytes this read returns may have been overwritten by an earlier
    // raw store at an address the checker never verified (fail closed).
    if reads_typed_memory(expr) {
        taint = taint.lub(env.floors.typed_read);
    }
    // S2: a heap-resident value is bytes in linear memory a later raw load can
    // reach. A plain re-read of a local/state field allocates nothing (its bytes
    // were noted when it was created, bound at entry, or assigned), so it is
    // exempt — otherwise every use of a public record under a secret branch
    // would raise the floor through the pc join for no write.
    if is_heap_resident(&expr.ty)
        && !matches!(
            expr.kind,
            TypedExprKind::Local(_) | TypedExprKind::StateField(_)
        )
    {
        env.note_memory_write(taint);
    }
    taint
}

fn compute_expr_taint_unfloored(
    expr: &TypedExpr,
    env: &mut TaintEnv,
    current_fn: &TypedFunction,
    program: &TypedProgram,
    diagnostics: &mut Vec<Diagnostic>,
) -> TaintLabel {
    let base = match &expr.kind {
        TypedExprKind::Literal(_) => TaintLabel::Public,

        TypedExprKind::Local(name) => env.lookup(name),

        // A state READ carries the field's declared taint (bound in `env` from
        // the actor captures). The anti-laundering guard is on the WRITE side:
        // an `init` assignment into a state field is taint-sink-checked against
        // the field's declared label (see the Assign handling), so a @Secret
        // value cannot be stored into a @Public state field and read back clean.
        TypedExprKind::StateField(name) => env.lookup(name),

        TypedExprKind::Binary(b) => {
            let l = compute_expr_taint(&b.lhs, env, current_fn, program, diagnostics);
            let r = if matches!(
                b.op,
                crate::ast::BinaryOp::LogicalAnd | crate::ast::BinaryOp::LogicalOr
            ) {
                if l.is_ct() {
                    diagnostics.push(Diagnostic::error(
                        codes::T020,
                        "secret-dependent short-circuit branch: left operand has taint @SecretCT (T020 / CT001)"
                            .to_string(),
                        Some(expr.span),
                    ));
                }
                let mut rhs_env = env.clone();
                rhs_env.pc_taint = rhs_env.pc_taint.lub(l);
                compute_expr_taint(&b.rhs, &mut rhs_env, current_fn, program, diagnostics)
            } else {
                compute_expr_taint(&b.rhs, env, current_fn, program, diagnostics)
            };
            // CT007 (T026) — variable-time division. Reject if either operand
            // has taint @SecretCT (division micro-ops on most CPUs are
            // data-dependent). Only `/` is checked HERE. `%` (Mod) exists and
            // is not: a @SecretCT remainder is refused by the formal gate's
            // DivRem policy (`formal.rs`, `Div | Mod`) and surfaces as I013,
            // not T026 (pinned by
            // `ct007_rem_with_secret_ct_operand_rejected_only_by_formal_gate`).
            // `<<`/`>>` (Shl/Shr) are the CT008 arm just below (T034).
            if b.op == crate::ast::BinaryOp::Div && (l.is_ct() || r.is_ct()) {
                diagnostics.push(Diagnostic::error(
                    codes::T026,
                    "variable-time division: operand has taint @SecretCT (T026 / CT007)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // CT008 (T034) — variable-time shift AMOUNT. A shift by a
            // data-dependent count is variable-time on cores without a barrel
            // shifter and on microcoded shift paths, so the count leaks through
            // timing. Only the RIGHT operand (the amount) is checked: the VALUE
            // being shifted is exempt because a shift by a @Public count has a
            // latency that depends on the count alone, never on the bits moved
            // — that is exactly how constant-time code masks and rotates a
            // secret, so rejecting it would ban the sound idiom. The check is
            // on the operand's LABEL, not its syntactic form, so a `let`-copied
            // or arithmetic-derived @SecretCT amount is rejected the same way.
            // Fails CLOSED: a @SecretCT amount is refused outright; there is no
            // constant-time shift-by-secret lowering to fall back to. Compound
            // `<<=`/`>>=` desugar to this same `Binary` node (parser
            // `compound_assign_op`), so they are covered here too. Before this
            // arm the program compiled with an empty diagnostic set (measured
            // 2026-09-20 on main ae026aec; closed 2026-09-30, `tests/attack/
            // KNOWN_GAPS.md` §CT008).
            if matches!(b.op, crate::ast::BinaryOp::Shl | crate::ast::BinaryOp::Shr) && r.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T034,
                    "variable-time shift: shift amount has taint @SecretCT (T034 / CT008)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // CT018 (T033) — secret-dependent string content comparison.
            // `str` `==`/`!=` lowers to an early-exit byte loop
            // (`AirStmt::StrBytesEq`), so both its trip count AND the fuel it
            // burns reveal the length of the common prefix.
            //
            // This has to be caught HERE: taint runs on the typed AST, strictly
            // before `air::lower`, so by the time the loop exists the labels are
            // gone. And it has to be a rejection rather than a constant-time
            // lowering — taint results are not carried into lowering, a
            // branch-free compare still leaks `min(len_a, len_b)` through trip
            // count and fuel, and `ct_eq`/`ct_select`/`ct_lt` are integer-only
            // so there is nothing to build one from.
            //
            // KEEP THIS PREDICATE IN STEP WITH `is_str_eq` in `air.rs` — it must
            // gate exactly the expressions that take that lowering. Widening one
            // without the other silently un-guards the loop.
            if matches!(b.op, crate::ast::BinaryOp::Eq | crate::ast::BinaryOp::NotEq)
                && matches!(b.lhs.ty, crate::type_check::Type::Str)
                && matches!(b.rhs.ty, crate::type_check::Type::Str)
                && (l.is_ct() || r.is_ct())
            {
                diagnostics.push(Diagnostic::error(
                    codes::T033,
                    "secret-dependent string content comparison: `str` `==`/`!=` operand has \
                     taint @SecretCT (T033 / CT018)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            l.lub(r)
        }

        TypedExprKind::Call(c) => {
            // Return taint = lub(callee ret_taint, arg taints)
            let arg_taints: Vec<TaintLabel> = c
                .args
                .iter()
                .map(|a| compute_expr_taint(a, env, current_fn, program, diagnostics))
                .collect();
            let args_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            let Some(callee) = find_function(program, &c.callee) else {
                internal_taint_error(
                    format!(
                        "taint checker: typed call target `{}` was not found",
                        c.callee
                    ),
                    expr.span,
                    diagnostics,
                );
                return args_taint.lub(env.effective_pc());
            };
            // HEAP FLOOR (S1): a callee whose effect row carries `FFI` may have
            // made the host write guest memory before returning to us.
            if callee_has_ffi(callee, program) {
                env.note_ffi_boundary();
            }
            // HEAP FLOOR (S5): whatever the CALLEE wrote into linear memory is
            // reachable from HERE the moment it returns — including a @Secret it
            // minted itself and stored through a pointer we handed it, which no
            // intraprocedural rule can see. Raising the caller's floors by the
            // callee's summary is the interprocedural STORE direction (the LOAD
            // direction — a callee reading memory its caller dirtied — is S3's,
            // still off). Fail closed: an unresolved callee takes the
            // program-wide bound.
            // The callee's writes happen under THIS site's pc, so the pc joins
            // the arguments: a `@Mut` write made only under `if secret { .. }`
            // leaks the branch, exactly as the intraprocedural S2 rule says.
            // HEAP FLOOR (S8): and a callee that raw-reads memory reads it at
            // THIS site's floors — `str_from_bytes(b, 13)` in the stdlib forges
            // a view over bytes the caller's `[s, 0]` left behind — so the
            // caller's floor is an implicit argument: it joins the site taint
            // (the callee may store what it read) and the result below.
            let summary = call_summary(&c.callee, program);
            let read_floor = summary.read_floor(env.floors);
            if HEAP_FLOOR_CALLEE_WRITES {
                let site_taint = args_taint.lub(env.effective_pc()).lub(read_floor);
                env.raise_floors(summary.floors(site_taint));
                // HEAP FLOOR (S5, region side): the floors cover every READ of
                // what the callee wrote; the pointer it wrote THROUGH can reach
                // a sink unread (`return out << 32 | n` hands the host the
                // buffer). Taint that argument's M6 region as the inline store
                // arm would have.
                taint_written_argument_regions(
                    env,
                    summary,
                    callee.captures.len(),
                    &c.args,
                    summary.annotation.lub(site_taint),
                );
            }
            check_typed_arity(
                &format!("typed call `{}`", c.callee),
                arg_taints.len(),
                callee.params.len(),
                expr.span,
                diagnostics,
            );
            if callee.ret_flow || callee.params.iter().any(|p| p.flow) {
                record_flow_call(expr.span, args_taint);
            }
            for ((arg, arg_taint), param) in c.args.iter().zip(&arg_taints).zip(&callee.params) {
                // Taint polymorphism: a `@Flow` parameter has no fixed label to
                // check against — it accepts any of `FLOW_INSTANTIATIONS`, and
                // the callee's body has been verified at each of them. The
                // argument's label is not discarded: it joins into `args_taint`
                // below, so the result carries it forward. `@SecretCT` is the
                // one label a `@Flow` body was NOT checked at (its CT discipline
                // constrains the code itself), so it is rejected here.
                if param.flow {
                    if arg_taint.is_ct() {
                        diagnostics.push(Diagnostic::error(
                            codes::T030,
                            format!(
                                "cannot pass @SecretCT value to taint-polymorphic function `{}` \
                                 parameter `{}`: `@Flow` does not quantify over @SecretCT, whose \
                                 constant-time discipline constrains the callee's body (T030)",
                                c.callee, param.name
                            ),
                            Some(arg.span),
                        ));
                    }
                    continue;
                }
                check_argument_taint(
                    *arg_taint,
                    param.taint,
                    &format!("function `{}` parameter `{}`", c.callee, param.name),
                    arg.span,
                    diagnostics,
                );
            }
            // AGG2b-4 (HOLE-TAINT): a `push` into a `mut Vec<scalar>` actor-state
            // field routes to a `$state`-suffixed monomorph instance (AGG2b-2). The
            // pushed element lands in the field's PERSISTENT heap and is read back at
            // the field's DECLARED taint, so a higher-taint value pushed in launders
            // to @Public on read-back (the Vec sibling of the F007 message-boundary
            // and the projected-place state-write sinks). The `$state` suffix —
            // reserved from user paths (T271) — marks EXACTLY this store; `args[0]`
            // is the receiver (rooted at the state field), `args[1..]` the pushed
            // value(s). Sink-check each pushed value against the rooted field's
            // declared taint, mirroring the `Assign`-into-`StateField` sink. A bare
            // `v.push(@Secret);` (an `Expr` statement whose value taint is otherwise
            // discarded) is now caught, not just the `let n = v.push(@Secret)` form.
            if c.callee.ends_with(crate::air::STATE_VEC_MONO_SUFFIX)
                && let Some(root) = c.args.first().and_then(place_root_statefield)
            {
                let declared = env.lookup(root);
                for stored in arg_taints.iter().skip(1) {
                    if !stored.can_flow_to(declared) {
                        diagnostics.push(Diagnostic::error(
                            codes::T001,
                            format!(
                                "cannot push @{stored:?} value into actor state Vec `{root}` \
                                 declared @{declared:?} without declassification (T001)"
                            ),
                            Some(expr.span),
                        ));
                    }
                }
            }
            // `-> T @Flow`: the result's label is the one that flowed in. The
            // join over ALL arguments (not just the `@Flow` ones) is the same
            // conservative rule the non-polymorphic path uses — a value the
            // callee could have derived its result from cannot be dropped.
            // S8: nor can the memory it read (`read_floor`, @Public unless the
            // callee raw-reads).
            if callee.ret_flow {
                args_taint.lub(read_floor)
            } else {
                callee.ret_taint.lub(args_taint).lub(read_floor)
            }
        }

        TypedExprKind::Intrinsic(intrinsic) => {
            // Compute per-arg taints once so CT checks and the join share work.
            let arg_taints: Vec<TaintLabel> = intrinsic
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            let args_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            // The per-kind arms below carry the CT rules only; the heap-floor
            // behavior is applied ONCE after the match, from the total
            // `intrinsic_memory` classification, so no arm can forget it.
            let base = match &intrinsic.kind {
                TypedIntrinsicKind::Alloc => {
                    // CT015 (T029) — allocation size must not depend on
                    // @SecretCT data (heap layout is observable).
                    if let Some(size_taint) = arg_taints.first()
                        && size_taint.is_ct()
                    {
                        diagnostics.push(Diagnostic::error(
                            codes::T029,
                            "secret-dependent allocation size: alloc(n) with n @SecretCT (T029 / CT015)"
                                .to_string(),
                            Some(expr.span),
                        ));
                    }
                    args_taint
                }
                TypedIntrinsicKind::Load8 | TypedIntrinsicKind::Store8 => {
                    // CT006 (T025) — secret-dependent address. First arg is
                    // the pointer; cache state leaks the access pattern.
                    if let Some(ptr_taint) = arg_taints.first()
                        && ptr_taint.is_ct()
                    {
                        diagnostics.push(Diagnostic::error(
                            codes::T025,
                            "secret-dependent memory address: load8/store8 with ptr @SecretCT (T025 / CT006)"
                                .to_string(),
                            Some(expr.span),
                        ));
                    }
                    args_taint
                }
                // Slot intrinsics inherit lub of inputs, identical to other
                // intrinsics. Future PRs can refine to propagate per-slot
                // stored taint if the use case arises.
                TypedIntrinsicKind::SlotNew { .. } => args_taint,
                TypedIntrinsicKind::SlotPut | TypedIntrinsicKind::SlotTake => args_taint,
                // CT006 (T025) — `vec_load`/`vec_store` are indexed memory
                // access, so a secret-dependent element ADDRESS leaks the
                // access pattern (which slot is touched is cache-observable),
                // exactly like load8/store8. The address is `base` (arg 0) +
                // `index` (arg 1); the bound and the stored value do not affect
                // it. The result inherits the conservative lub of inputs (heap
                // contents are not precisely taint-tracked — same limitation as
                // a load8 from a buffer a secret was stored into).
                TypedIntrinsicKind::VecStore { .. } | TypedIntrinsicKind::VecLoad { .. } => {
                    if arg_taints.iter().take(2).any(|t| t.is_ct()) {
                        diagnostics.push(Diagnostic::error(
                            codes::T025,
                            "secret-dependent memory address: vec_load/vec_store with a @SecretCT base or index (T025 / CT006)"
                                .to_string(),
                            Some(expr.span),
                        ));
                    }
                    args_taint
                }
                // PR AF / N20-AF: array/slice length and is_empty
                // results inherit the receiver's taint via the lub
                // of args. A `.len()` on a `@Secret` array yields a
                // `@Secret` u32. (`.is_empty()` similarly.) This is
                // the conservative join; future PR can downgrade if
                // a `pub fn` boundary needs to declassify.
                TypedIntrinsicKind::ArrayLen { .. }
                | TypedIntrinsicKind::SliceLen
                | TypedIntrinsicKind::ArrayIsEmpty { .. }
                | TypedIntrinsicKind::SliceIsEmpty
                // Phase-1 completion: `.contains(x)` (bool result) and slice
                // `.first()`/`.last()` (`Option<T>`) inherit the receiver's
                // (and needle's) taint via the lub — a `.contains` over a
                // `@Secret` array, or an element pulled from one, is `@Secret`.
                // Same conservative-join policy as `.len()`/`.is_empty()`.
                | TypedIntrinsicKind::ArrayContains { .. }
                | TypedIntrinsicKind::SliceContains { .. }
                | TypedIntrinsicKind::SliceFirst { .. }
                | TypedIntrinsicKind::SliceLast { .. } => args_taint,
                // PR S1 / N20-S1 inheritance: Str intrinsics inherit
                // the receiver's taint via lub. `.len()` /
                // `.is_empty()` / `.byte_at(i)` on a `@Secret` Str
                // yields a `@Secret` U32. Identical policy to
                // Array/Slice intrinsics; PR S2 may declassify at
                // `pub fn` boundaries.
                TypedIntrinsicKind::StrLen
                // N-LEX: `as_output()` packs the header to an i64; the result
                // inherits the receiver's taint, identical policy to `len`.
                | TypedIntrinsicKind::StrAsOutput
                | TypedIntrinsicKind::StrIsEmpty
                | TypedIntrinsicKind::StrByteAt { .. }
                // Phase-3 integer width conversion (`.as_i32()`/etc.) inherits
                // the receiver's taint via lub — narrowing/widening an
                // `@Secret` int keeps it `@Secret`.
                | TypedIntrinsicKind::IntConvert { .. }
                // A substring inherits the receiver's taint (a view of a
                // `@Secret` Str is `@Secret`), identical policy to `byte_at`.
                | TypedIntrinsicKind::StrSubstr { .. }
                // Owned-strings PR-1: `str_from_raw(ptr, len)` taint = lub(ptr,
                // len). The header carries no BYTE taint; owned-string secrecy is
                // preserved at the OUTER builder-call boundary (a call's result
                // taint is lub(callee_ret, args) — taint_check call rule), so
                // `str_concat(@SecretCT a, _)` stays `@SecretCT` regardless.
                | TypedIntrinsicKind::StrFromRaw { .. }
                // u256 PR-U0/U1: u256 intrinsics inherit the lub of their inputs
                // (a u256/limb built from `@Secret` data is `@Secret`). Same
                // conservative-join policy as the other constructors/readers.
                | TypedIntrinsicKind::U256FromI64 { .. }
                | TypedIntrinsicKind::U256Make
                | TypedIntrinsicKind::U256Limb { .. }
                | TypedIntrinsicKind::TrapIf
                | TypedIntrinsicKind::Trap => args_taint,
                // Phase 2H §3.5: CT intrinsics are branch-free constant-time
                // primitives — the output taint is the lub of inputs (standard
                // flow). No CT-rejection rule applies because these are
                // exactly the constructs CT discipline PERMITS over @SecretCT.
                TypedIntrinsicKind::CtEq
                | TypedIntrinsicKind::CtSelect
                | TypedIntrinsicKind::CtLt => args_taint,
            };
            match intrinsic_memory(&intrinsic.kind) {
                // HEAP FLOOR: a raw read returns WHATEVER is at the address —
                // host-written bytes, a secret stored through another pointer,
                // or (for a forged `str` view) whatever every later `byte_at`
                // through it will find — so the result is floored (fail closed).
                IntrinsicMemory::RawRead => base.lub(env.floors.raw_load),
                // HEAP FLOOR (S2/S4/S6): the stored bytes are now in memory at an
                // UNCHECKED address any later raw load — or a typed read of
                // whatever aggregate the address landed in — can reach. The
                // floor takes `args_taint`, the join over EVERY operand: the
                // address (`store8(a + (s & 1), 9)` writes a @Public byte but
                // leaves `s`'s low bit in WHICH cell changed — S6, verified
                // end-to-end), the value, and for `vec_store` the caller-claimed
                // bound that decides whether the write happened at all. Joining,
                // not indexing, keeps this total over the operand list.
                IntrinsicMemory::RawWrite => {
                    env.note_raw_store(args_taint);
                    // M6 — the store taints the REGION of the pointer it goes
                    // through, so a pointer that reaches a sink UNREAD (`return
                    // out << 32 | n`: the host reads the buffer) carries what
                    // was written into it. Total over the write intrinsics and
                    // over their operands: the label is the join of EVERY
                    // operand (value, address, bound) and the pc — a @Public
                    // byte at a @Secret-derived address changes WHICH cell the
                    // host sees (S6, `0900` / `0009` end-to-end on main), and
                    // `vec_store` is a raw write like `store8` (`00` / `01` on
                    // main) — and every operand with a region is tainted, so
                    // which operand is the address is never consulted (a
                    // pointer passed as the value is over-tainted: fail closed).
                    // An operand with several candidate regions (rebound on
                    // one path of a merge) taints every candidate; an operand
                    // with NONE — not a regioned local — taints nothing: the
                    // open surface HF-1 discloses.
                    let written = args_taint.lub(env.effective_pc());
                    if written > TaintLabel::Public {
                        for operand in &intrinsic.args {
                            for region in env.region_of_expr(operand) {
                                env.taint_region(region, written);
                            }
                        }
                    }
                    base
                }
                // HEAP FLOOR (S7): a slot write lands at a CHECKED address, but
                // which slot changed — and under which pc — is an observation a
                // typed read of the slot recovers, exactly like `a[i] = v`.
                IntrinsicMemory::CheckedWrite => {
                    env.note_typed_place_write(args_taint);
                    base
                }
                IntrinsicMemory::Inert => base,
            }
        }

        TypedExprKind::FieldAccess(f) => {
            // Try per-field tracking if object is a local
            if let TypedExprKind::Local(name) = &f.object.kind {
                env.lookup_field(name, &f.field)
            } else {
                compute_expr_taint(&f.object, env, current_fn, program, diagnostics)
            }
        }

        TypedExprKind::Index(i) => {
            let arr = compute_expr_taint(&i.array, env, current_fn, program, diagnostics);
            let idx = compute_expr_taint(&i.index, env, current_fn, program, diagnostics);
            // CT005 (T024) — secret-dependent index. The loaded address is
            // observable via cache state; reject any @SecretCT-tainted index.
            if idx.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T024,
                    "secret-dependent index: arr[i] with i @SecretCT (T024 / CT005)".to_string(),
                    Some(expr.span),
                ));
            }
            arr.lub(idx)
        }

        // PR AF / N20-AF: slice taint is the lub of the receiver's
        // taint and the bound expressions' taints (`start`, `end`).
        // Public bounds against a `@Secret` array → result is
        // `@Secret`. Verified at commit #6 by fixture
        // `af_secret_array_slice_stays_secret`.
        TypedExprKind::Slice(s) => {
            let arr = compute_expr_taint(&s.array, env, current_fn, program, diagnostics);
            let start = s
                .start
                .as_ref()
                .map(|e| compute_expr_taint(e, env, current_fn, program, diagnostics))
                .unwrap_or(TaintLabel::Public);
            let end = s
                .end
                .as_ref()
                .map(|e| compute_expr_taint(e, env, current_fn, program, diagnostics))
                .unwrap_or(TaintLabel::Public);
            arr.lub(start).lub(end)
        }

        // (HEAP FLOOR S2 for every materialized aggregate — record / array /
        // enum / f-string / `str` — is applied by TYPE at the `compute_expr_taint`
        // choke point, not per arm here.)
        TypedExprKind::ArrayLit(a) => a
            .elements
            .iter()
            .map(|e| compute_expr_taint(e, env, current_fn, program, diagnostics))
            .fold(TaintLabel::Public, TaintLabel::lub),

        // PR-E3: an f-string's taint is the lub of its hole taints (chunks Public).
        TypedExprKind::FString(fs) => fs
            .parts
            .iter()
            .filter_map(|p| match p {
                crate::typed_ast::TypedFStringPart::Hole(h) => {
                    Some(compute_expr_taint(h, env, current_fn, program, diagnostics))
                }
                crate::typed_ast::TypedFStringPart::Literal(_) => None,
            })
            .fold(TaintLabel::Public, TaintLabel::lub),

        TypedExprKind::RecordConstruct(r) => {
            // Per-field taints are tracked at let-binding time.
            // When used as an expression value, collapse to lub.
            r.fields
                .iter()
                .map(|(_, e)| compute_expr_taint(e, env, current_fn, program, diagnostics))
                .fold(TaintLabel::Public, TaintLabel::lub)
        }

        TypedExprKind::EnumConstruct(e) => e
            .fields
            .iter()
            .map(|f| compute_expr_taint(f, env, current_fn, program, diagnostics))
            .fold(TaintLabel::Public, TaintLabel::lub),

        TypedExprKind::ClosureConstruct(c) => {
            // E4 / §3.7 — Closure capture CT propagation. Look up each
            // capture's source taint from the enclosing TaintEnv and
            // type-check the synthesized closure body under that env.
            // Non-optional: omitting the propagation silently disables CT
            // for closure-using code, which crypto code routinely is.
            let capture_taints: Vec<TaintLabel> =
                c.captures.iter().map(|cap| env.lookup(&cap.name)).collect();

            // Find the lambda-lifted function by synthesized_name.
            let closure_fn = program
                .modules
                .iter()
                .flat_map(|m| m.functions.iter())
                .find(|f| f.name == c.synthesized_name);

            // A missing synthesized function must reject, but malformed or
            // recovered input must not abort the compiler process. I013 keeps
            // this CT boundary fail-closed while preserving diagnostics.
            let Some(closure_fn) = closure_fn else {
                internal_taint_error(
                    format!(
                        "CT closure propagation: synthesized closure `{}` not found in TypedProgram",
                        c.synthesized_name
                    ),
                    expr.span,
                    diagnostics,
                );
                return capture_taints
                    .into_iter()
                    .fold(TaintLabel::Public, TaintLabel::lub)
                    .lub(env.effective_pc());
            };

            // Build a fresh TaintEnv: lifted params bound at their own
            // declared taint; captures bound at the source taints from the
            // enclosing scope.
            let mut closure_env = TaintEnv::new();
            // HEAP FLOOR: the body runs no earlier than its construct site, so
            // everything reachable in memory HERE is reachable there. (It may
            // run later still, after more FFI/stores — the interprocedural
            // boundary S3 closes; S1/S2/S4 alone leave that gap, documented.)
            closure_env.floors = env.floors;
            // M6 (closure side): a captured POINTER keeps its region inside the
            // body, so a store through it there taints the same region the
            // enclosing scope reads at its sinks — `let c = fn(x) { let s
            // @Secret = 1; store8(out, s & 1); return x; }` then `return out
            // << 32 | n` printed the bit on main (the closure VALUE carries only
            // its captures' labels, and `out` is @Public). Only the captures'
            // regions are copied — a closure parameter that shadows an outer
            // pointer name must start unregioned — and `next_region` carries
            // forward so a fresh `alloc` in the body cannot collide with one
            // minted later in the enclosing scope.
            for cap in &closure_fn.captures {
                if let Some(regions) = env.region_of.get(&cap.name) {
                    closure_env
                        .region_of
                        .insert(cap.name.clone(), regions.clone());
                }
            }
            closure_env.region_taint = env.region_taint.clone();
            closure_env.next_region = env.next_region;
            for p in &closure_fn.params {
                closure_env.bind(&p.name, p.taint);
            }
            check_typed_arity(
                &format!("closure `{}` capture list", c.synthesized_name),
                capture_taints.len(),
                closure_fn.captures.len(),
                expr.span,
                diagnostics,
            );
            for (cap, taint) in closure_fn.captures.iter().zip(capture_taints.iter()) {
                closure_env.bind(&cap.name, *taint);
            }

            // Type-check the closure body with propagated taints. Any CT
            // violation inside the body (CT001-CT017) is emitted with the
            // violating statement's span.
            check_block(
                &closure_fn.body,
                &mut closure_env,
                closure_fn,
                program,
                diagnostics,
            );
            // HEAP FLOOR (S9): whatever the body writes — a projected secret
            // write into a captured aggregate inside a `grant`, say — is in
            // memory once the closure runs, and it runs no EARLIER than here.
            // Raising the construct site's floors floors every later read in
            // this function, a superset of the reads after the invocation
            // (fail closed even for a closure that never runs). Without this
            // the body's floors died with `closure_env` and `grant(&f, fn(c)
            // { a[0] = s; })` then `a[0]` was accepted (round-3 review).
            if HEAP_FLOOR_CLOSURE_FLOWS_BACK {
                env.raise_floors(closure_env.floors);
            }
            // M6 (closure side): what the body stored through a captured
            // pointer is in that pointer's region from here on — the body runs
            // no earlier than its construct site (fail closed even for a
            // closure that never runs, exactly as S9 treats the floors).
            for (region, taint) in &closure_env.region_taint {
                env.taint_region(*region, *taint);
            }
            env.next_region = closure_env.next_region;

            // The closure expression's own taint = lub of capture taints
            // (the closure is an opaque fat pointer carrying those values).
            capture_taints
                .into_iter()
                .fold(TaintLabel::Public, TaintLabel::lub)
        }

        TypedExprKind::Borrow(b) => {
            compute_expr_taint(&b.inner, env, current_fn, program, diagnostics)
        }

        TypedExprKind::Grant(g) => {
            // M4: Grant return crosses ring boundary — must be @Public
            let body_taint = compute_expr_taint(&g.body, env, current_fn, program, diagnostics);
            // Note: actual sink check is done at the return-statement level
            // inside the closure body, not here. Here we just propagate.
            let cap_taint = compute_expr_taint(&g.cap, env, current_fn, program, diagnostics);
            // HEAP FLOOR (S9): a `grant` INVOKES its body right here. A closure
            // LITERAL was just checked by the `ClosureConstruct` arm, which
            // flowed its floors back; any other body (a local holding a
            // closure) is a callee this pass cannot name, so — like an indirect
            // call — it takes the program-wide bound for what it wrote and
            // read (fail closed).
            let read_floor = if HEAP_FLOOR_CLOSURE_FLOWS_BACK
                && !matches!(g.body.kind, TypedExprKind::ClosureConstruct(_))
            {
                let bound = CallSummary::program_bound(program);
                let read_floor = bound.read_floor(env.floors);
                let site_taint = body_taint
                    .lub(cap_taint)
                    .lub(env.effective_pc())
                    .lub(read_floor);
                env.raise_floors(bound.floors(site_taint));
                read_floor
            } else {
                TaintLabel::Public
            };
            body_taint.lub(cap_taint).lub(read_floor)
        }

        TypedExprKind::Handle(h) => {
            // A handler body is an ordinary lexical block: every statement
            // participates in taint checking and the expression result, when
            // present, determines the handle expression's value taint.
            check_block(&h.body, env, current_fn, program, diagnostics)
                .unwrap_or(TaintLabel::Public)
        }

        // Effect Handlers (EH3, C-VIS): operation parameters are taint boundaries,
        // just like ordinary function parameters. A perform result conservatively
        // carries every argument's taint; clause binders retain their operation
        // parameter contracts, and resume/abort values flow into the handle result.
        TypedExprKind::Perform(p) => {
            let arg_taints: Vec<TaintLabel> = p
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            let result = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            let Some(op) = find_effect_op(program, &p.effect, &p.op) else {
                internal_taint_error(
                    format!(
                        "taint checker: typed effect operation `{}.{}` was not found",
                        p.effect, p.op
                    ),
                    expr.span,
                    diagnostics,
                );
                return result.lub(env.effective_pc());
            };
            check_typed_arity(
                &format!("typed perform `{}.{}`", p.effect, p.op),
                p.args.len(),
                op.param_taints.len(),
                expr.span,
                diagnostics,
            );
            for (index, ((arg, arg_taint), declared)) in p
                .args
                .iter()
                .zip(&arg_taints)
                .zip(&op.param_taints)
                .enumerate()
            {
                check_argument_taint(
                    *arg_taint,
                    *declared,
                    &format!("effect operation `{}.{}` argument {index}", p.effect, p.op),
                    arg.span,
                    diagnostics,
                );
            }
            result
        }
        TypedExprKind::ClauseHandle(c) => {
            let mut result =
                compute_expr_taint(&c.scrutinee, env, current_fn, program, diagnostics);
            for clause in &c.clauses {
                let declared_taints =
                    if let Some(op) = find_effect_op(program, &clause.effect, &clause.op) {
                        check_typed_arity(
                            &format!("typed clause `{}.{}`", clause.effect, clause.op),
                            clause.binders.len(),
                            op.param_taints.len(),
                            expr.span,
                            diagnostics,
                        );
                        op.param_taints.clone()
                    } else {
                        internal_taint_error(
                            format!(
                                "taint checker: typed effect operation `{}.{}` was not found",
                                clause.effect, clause.op
                            ),
                            expr.span,
                            diagnostics,
                        );
                        // Continue the rejected body's analysis at top taint so
                        // recovery never creates an under-tainted traversal.
                        vec![TaintLabel::Secret; clause.binders.len()]
                    };
                let mut clause_env = env.child_scope();
                for (binder, taint) in clause.binders.iter().zip(&declared_taints) {
                    clause_env.bind(binder, *taint);
                }
                if let Some(clause_taint) = check_block(
                    &clause.body,
                    &mut clause_env,
                    current_fn,
                    program,
                    diagnostics,
                ) {
                    result = result.lub(clause_taint);
                }
                // HEAP FLOOR: a clause body that did FFI or stored a secret
                // raised ITS scope's floors; the code after the handle reads
                // the same memory, so the raise flows back out (fail closed).
                env.raise_floors(clause_env.floors);
            }
            result
        }
        TypedExprKind::Resume(r) => {
            compute_expr_taint(&r.value, env, current_fn, program, diagnostics)
        }

        TypedExprKind::Declassify(d) => {
            // CT017 (T031) — declassify input contract (E2): the existing
            // `declassify` accepts only @Public/@Internal/@Secret. @SecretCT
            // inputs require `declassify_ct` first (two-step ladder).
            let value_taint = compute_expr_taint(&d.value, env, current_fn, program, diagnostics);
            // Also evaluate the cap expression for side-effect taint tracking.
            let _ = compute_expr_taint(&d.cap, env, current_fn, program, diagnostics);
            if value_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T031,
                    "cannot declassify a @SecretCT value directly; use `declassify_ct(value, ct_cap)` first (T031 / CT017)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // Declassification lowers taint to the target level (default: Public)
            // The actual target is stored on the AST DeclassifyExpr, but in the
            // typed AST we default to Public since that's the common case.
            TaintLabel::Public
        }

        TypedExprKind::DeclassifyCt(d) => {
            // declassify_ct lowers @SecretCT → @Secret. Per spec §3.4.1, the
            // input MUST be @SecretCT; @Public/@Internal/@Secret inputs are a
            // user error (they don't need a CT capability to begin with).
            let value_taint = compute_expr_taint(&d.value, env, current_fn, program, diagnostics);
            let _ = compute_expr_taint(&d.cap, env, current_fn, program, diagnostics);
            if !value_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T032,
                    format!(
                        "declassify_ct input must be @SecretCT, found @{:?}; use `declassify(value, cap)` for non-CT data (T032)",
                        value_taint
                    ),
                    Some(expr.span),
                ));
            }
            // Lower @SecretCT → @Secret. Caller still needs `declassify` to
            // reach @Public (two-step chain).
            TaintLabel::Secret
        }

        TypedExprKind::ResultCtor(r) => {
            compute_expr_taint(&r.value, env, current_fn, program, diagnostics)
        }
        TypedExprKind::Try(t) => {
            compute_expr_taint(&t.value, env, current_fn, program, diagnostics)
        }

        TypedExprKind::Send(s) => {
            let arg_taints: Vec<TaintLabel> = s
                .args
                .iter()
                .map(|a| compute_expr_taint(a, env, current_fn, program, diagnostics))
                .collect();
            let payload_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            // CT014 (T028) — @SecretCT payload across actor boundary.
            // Inter-actor CT analysis is anti-goal §9.9; first-cut reject.
            if payload_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T028,
                    "cannot send @SecretCT payload across actor boundary (T028 / CT014)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // F007 (T001) — plain @Secret/@Internal data-flow across the actor
            // boundary. The receiving handler binds each param at its DECLARED
            // taint (default @Public), so a tainted payload sent to a lower-taint
            // param is silently laundered. Check each arg against the handler's
            // declared param taint, mirroring the assignment/return sink checks.
            check_message_payload_taint(
                &s.actor,
                &s.handler,
                &arg_taints,
                program,
                expr.span,
                diagnostics,
            );
            payload_taint
        }

        TypedExprKind::Ask(a) => {
            let arg_taints: Vec<TaintLabel> = a
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            let args_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            let timeout_taint =
                compute_expr_taint(&a.timeout, env, current_fn, program, diagnostics);
            // CT014 (T028) — @SecretCT payload across actor boundary.
            if args_taint.is_ct() || timeout_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T028,
                    "cannot ask with @SecretCT payload or timeout across actor boundary (T028 / CT014)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            // F007 (T001) — same payload-launder check as `send` on the request
            // path. `ask` delivers `args` to the handler's params identically;
            // the reply flows back through the handler's `ret_taint` (already
            // enforced by the M4 return sink in the handler body), so only the
            // request payload needs a boundary check here.
            check_message_payload_taint(
                &a.actor,
                &a.handler,
                &arg_taints,
                program,
                expr.span,
                diagnostics,
            );
            args_taint.lub(timeout_taint)
        }

        TypedExprKind::Spawn(s) => {
            let arg_taints: Vec<TaintLabel> = s
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            let payload_taint = arg_taints
                .iter()
                .copied()
                .fold(TaintLabel::Public, TaintLabel::lub);
            // Spawn is the third actor message boundary alongside send/ask. SecretCT values cannot
            // cross it because the child executes independently of the parent's CT discipline.
            if payload_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T028,
                    "cannot spawn actor with @SecretCT init payload (T028 / CT014)".to_string(),
                    Some(expr.span),
                ));
            }
            // Plain taint must be preserved by the child init signature. Without this sink check a
            // Secret arg delivered to a default-Public init param is rebound as Public in the child.
            check_actor_init_payload_taint(&s.actor, &arg_taints, program, expr.span, diagnostics);
            // The ActorRef itself carries authority, not the data used to initialize the actor.
            TaintLabel::Public
        }

        TypedExprKind::CapSplit(split) => {
            let amount = compute_expr_taint(&split.amount, env, current_fn, program, diagnostics);
            if amount.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T027,
                    "cannot use @SecretCT data as a capability split amount; the host call, trap, and child fuel are observable (T027 / CT010)"
                        .to_string(),
                    Some(split.amount.span),
                ));
            } else if amount != TaintLabel::Public {
                diagnostics.push(Diagnostic::error(
                    codes::T001,
                    format!(
                        "capability split amount must be @Public, found @{amount:?}; the host call, trap, and child fuel are observable (T001)"
                    ),
                    Some(split.amount.span),
                ));
            }
            TaintLabel::Public
        }

        TypedExprKind::CapDraw(draw) => {
            let amount = compute_expr_taint(&draw.amount, env, current_fn, program, diagnostics);
            if amount.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T027,
                    "cannot use @SecretCT data as a capability draw amount; the host call, trap, and child fuel are observable (T027 / CT010)"
                        .to_string(),
                    Some(draw.amount.span),
                ));
            } else if amount != TaintLabel::Public {
                diagnostics.push(Diagnostic::error(
                    codes::T001,
                    format!(
                        "capability draw amount must be @Public, found @{amount:?}; the host call, trap, and child fuel are observable (T001)"
                    ),
                    Some(draw.amount.span),
                ));
            }
            TaintLabel::Public
        }

        TypedExprKind::CapRestrict(_) | TypedExprKind::Mint(_) => {
            // Capabilities-as-values: a minted capability is authority, not
            // data — always @Public-clean (the resource it authorizes is named
            // by `for <target>`, not embedded in the cap value).
            TaintLabel::Public
        }

        TypedExprKind::ExternCall(e) => {
            // CT010 (T027) — @SecretCT passed to FFI. Sigil cannot verify
            // the C side's timing properties; any @SecretCT arg crossing the
            // boundary is rejected. The value boundary itself is @Internal,
            // so ordinary @Secret arguments are rejected with T001 as well.
            let arg_taints: Vec<TaintLabel> = e
                .args
                .iter()
                .map(|arg| compute_expr_taint(arg, env, current_fn, program, diagnostics))
                .collect();
            if arg_taints.iter().any(|taint| taint.is_ct()) {
                diagnostics.push(Diagnostic::error(
                    codes::T027,
                    format!(
                        "cannot pass @SecretCT value to extern fn `{}` (T027 / CT010)",
                        e.extern_name
                    ),
                    Some(expr.span),
                ));
            }
            for (arg, taint) in e.args.iter().zip(&arg_taints) {
                if !taint.is_ct() {
                    check_argument_taint(
                        *taint,
                        TaintLabel::Internal,
                        &format!("extern function `{}` argument", e.extern_name),
                        arg.span,
                        diagnostics,
                    );
                }
            }
            // HEAP FLOOR (S1): the host wrote its result at the guest's bump
            // pointer. The RETURNED packed pointer is @Internal already; the
            // bytes it points at are reachable through any other pointer too.
            env.note_ffi_boundary();
            TaintLabel::Internal
        }

        // HOF / N19-HOF: general closure-call dispatch propagates
        // taint as lub(callee_local taint, args taints). The
        // closure body's ret_taint is opaque from the call site
        // (closures don't carry per-fn return-taint annotations
        // at the type level), so we conservatively use the local's
        // taint as a proxy for whatever the closure body returns.
        // Per N9-HOF this arm is explicit (no wildcard).
        TypedExprKind::IndirectCall(call) => {
            let callee_taint = env.lookup(&call.callee_local);
            // HEAP FLOOR (S1): `Type::Fn` carries no effect row, so the closure
            // behind this local cannot be proven FFI-free. Fail closed: if the
            // program has ANY `FFI` function, assume the closure reached one.
            if program_has_ffi(program) {
                env.note_ffi_boundary();
            }
            let arg_taints: Vec<TaintLabel> = call
                .args
                .iter()
                .map(|a| compute_expr_taint(a, env, current_fn, program, diagnostics))
                .collect();
            // `Type::Fn` carries machine types but no taint labels. Until that
            // contract is represented, accepting a non-public argument would let
            // the closure body relabel it through a public parameter. Fail closed.
            for (arg, taint) in call.args.iter().zip(&arg_taints) {
                check_argument_taint(
                    *taint,
                    TaintLabel::Public,
                    &format!(
                        "indirect-call parameter of closure `{}` (function types do not carry taint contracts)",
                        call.callee_local
                    ),
                    arg.span,
                    diagnostics,
                );
            }
            let args_taint = arg_taints
                .into_iter()
                .fold(TaintLabel::Public, TaintLabel::lub);
            // HEAP FLOOR (S5/S8): the closure behind this local is not a name
            // this pass can summarize, so it takes the program-wide bound — the
            // same fail-closed treatment S1 gives the FFI question here. The
            // bound READS everything too: a closure built before a secret
            // write and invoked after it returns the caller's floored bytes
            // (`let f = fn(x) { return a[0]; }; a[0] = s; f(0)` — 42 / 7 bytes
            // end-to-end on main and round 3), so the result carries both of
            // this site's floors.
            let bound = CallSummary::program_bound(program);
            let read_floor = bound.read_floor(env.floors);
            if HEAP_FLOOR_CALLEE_WRITES {
                let site_taint = args_taint.lub(env.effective_pc()).lub(read_floor);
                env.raise_floors(bound.floors(site_taint));
                // HEAP FLOOR (S5, region side): the bound writes through EVERY
                // pointer handed over (`All`), so each argument with a region is
                // tainted — fail closed.
                taint_written_argument_regions(
                    env,
                    bound,
                    0,
                    &call.args,
                    bound.annotation.lub(site_taint),
                );
            }
            callee_taint.lub(args_taint).lub(read_floor)
        }

        TypedExprKind::Region(r) => {
            // CT015 (T029) — region(n) { ... } with n @SecretCT. Allocation
            // size is observable via heap layout; reject.
            let limit_taint = compute_expr_taint(&r.limit, env, current_fn, program, diagnostics);
            if limit_taint.is_ct() {
                diagnostics.push(Diagnostic::error(
                    codes::T029,
                    "secret-dependent region size: region(n) with n @SecretCT (T029 / CT015)"
                        .to_string(),
                    Some(expr.span),
                ));
            }
            check_block(&r.body, env, current_fn, program, diagnostics)
                .unwrap_or(TaintLabel::Public)
        }
    };

    // Fold in lexical pc-taint and any control dependence that survives an early exit.
    base.lub(env.effective_pc())
}

fn find_function<'a>(program: &'a TypedProgram, name: &str) -> Option<&'a TypedFunction> {
    program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .find(|f| f.name == name)
}

fn find_effect_op<'a>(
    program: &'a TypedProgram,
    effect: &str,
    op: &str,
) -> Option<&'a crate::typed_ast::EffectOpSig> {
    program
        .effect_ops
        .get(effect)
        .and_then(|ops| ops.iter().find(|candidate| candidate.name == op))
}

/// Reject a malformed typed-AST invariant without aborting the compiler.
/// Source-owned arity diagnostics (T070/E007/T094/T115) should have stopped
/// production first; reaching this helper is therefore an integrity failure.
fn internal_taint_error(
    message: String,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    diagnostics.push(Diagnostic::error(codes::I013, message, Some(span)));
}

fn check_typed_arity(
    boundary: &str,
    actual: usize,
    expected: usize,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if actual != expected {
        internal_taint_error(
            format!(
                "taint checker: {boundary} has {actual} values but target has {expected} parameters"
            ),
            span,
            diagnostics,
        );
    }
}

fn check_argument_taint(
    source: TaintLabel,
    declared: TaintLabel,
    boundary: &str,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if declared.is_ct() && matches!(source, TaintLabel::Internal | TaintLabel::Secret) {
        diagnostics.push(Diagnostic::error(
            codes::T030,
            format!(
                "cannot pass @{source:?} value to @SecretCT {boundary}; source must be @Public or @SecretCT (T030 / CT016)"
            ),
            Some(span),
        ));
    }
    if !source.can_flow_to(declared) {
        diagnostics.push(Diagnostic::error(
            codes::T001,
            format!(
                "cannot pass @{source:?} value to {boundary} declared @{declared:?} without declassification (T001)"
            ),
            Some(span),
        ));
    }
}

/// Resolve the declared parameter taints of an actor handler `(actor, handler)`.
///
/// Handlers are lowered to `TypedFunction`s tagged
/// `TypedFunctionKind::ActorHandler`, whose `params` are exactly the message
/// payload parameters (in declaration order), each carrying its source-declared
/// taint (default @Public). A missing match after type checking is an internal
/// pipeline inconsistency; callers fail closed rather than skipping the boundary.
fn find_handler_param_taints<'a>(
    program: &'a TypedProgram,
    actor: &str,
    handler: &str,
) -> Option<&'a [crate::typed_ast::TypedParam]> {
    program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .find(|f| {
            matches!(
                &f.kind,
                crate::typed_ast::TypedFunctionKind::ActorHandler { actor: a, handler: h, .. }
                    if a == actor && h == handler
            )
        })
        .map(|f| f.params.as_slice())
}

/// Resolve the declared parameter taints of an actor's init block. A spawn with arguments has
/// already been checked against that init signature by type checking, so a miss here is an internal
/// pipeline inconsistency and must not silently bypass the taint boundary.
fn find_actor_init_param_taints<'a>(
    program: &'a TypedProgram,
    actor: &str,
) -> Option<&'a [crate::typed_ast::TypedParam]> {
    program
        .modules
        .iter()
        .flat_map(|m| m.functions.iter())
        .find(|f| {
            matches!(
                &f.kind,
                crate::typed_ast::TypedFunctionKind::ActorInit { actor: a, .. } if a == actor
            )
        })
        .map(|f| f.params.as_slice())
}

fn check_actor_init_payload_taint(
    actor: &str,
    arg_taints: &[TaintLabel],
    program: &TypedProgram,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Some(params) = find_actor_init_param_taints(program, actor) else {
        // Actors without an explicit init legitimately accept no arguments.
        if arg_taints.is_empty() {
            return;
        }
        internal_taint_error(
            format!(
                "taint checker: spawn target `{actor}` has arguments but no typed actor-init function"
            ),
            span,
            diagnostics,
        );
        return;
    };
    check_typed_arity(
        &format!("spawn target `{actor}` argument list"),
        arg_taints.len(),
        params.len(),
        span,
        diagnostics,
    );
    for (arg_taint, param) in arg_taints.iter().zip(params.iter()) {
        // SecretCT is rejected by T028 at the boundary; avoid a redundant T001 at the same site.
        if arg_taint.is_ct() {
            continue;
        }
        if !arg_taint.can_flow_to(param.taint) {
            diagnostics.push(Diagnostic::error(
                codes::T001,
                format!(
                    "cannot spawn @{arg_taint:?} value into actor `{actor}` init parameter `{}` declared @{:?} without declassification (T001)",
                    param.name, param.taint
                ),
                Some(span),
            ));
        }
    }
}

/// F007 sink: reject a message payload arg whose computed taint cannot flow to
/// the receiving handler's declared parameter taint.
///
/// Without this check a `@Secret` value sent to a handler with the default
/// `@Public` param is silently laundered to `@Public` inside the receiver
/// (the handler binds params at their declared taint), defeating every
/// downstream taint sink. This mirrors the assignment/return `can_flow_to`
/// checks at the actor message boundary.
fn check_message_payload_taint(
    actor: &str,
    handler: &str,
    arg_taints: &[TaintLabel],
    program: &TypedProgram,
    span: crate::span::Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let Some(params) = find_handler_param_taints(program, actor, handler) else {
        internal_taint_error(
            format!("taint checker: typed actor handler `{actor}::{handler}` was not found"),
            span,
            diagnostics,
        );
        return;
    };
    check_typed_arity(
        &format!("message target `{actor}::{handler}` argument list"),
        arg_taints.len(),
        params.len(),
        span,
        diagnostics,
    );
    for (arg_taint, param) in arg_taints.iter().zip(params.iter()) {
        // @SecretCT payloads are already rejected wholesale by the T028 check
        // above (inter-actor CT is anti-goal §9.9); skip them here so a CT arg
        // yields a single T028 diagnostic rather than a redundant T001 too.
        if arg_taint.is_ct() {
            continue;
        }
        if !arg_taint.can_flow_to(param.taint) {
            diagnostics.push(Diagnostic::error(
                codes::T001,
                format!(
                    "cannot send @{:?} value to actor handler `{}::{}` parameter `{}` declared @{:?} without declassification (T001)",
                    arg_taint, actor, handler, param.name, param.taint
                ),
                Some(span),
            ));
        }
    }
}
