# Self-Hosted Backend Parity — the self-compiled compiler as a verified mirror of production

**Status:** IN PROGRESS — SHP-P0, SHP-0 and SHP-1 SHIPPED (2026-10-02); SHP-2 SHIPPED
(2026-10-04): SHP-2a, the extern front end, and SHP-2b, two-ring emission; SHP-3 SHIPPED
(2026-10-04): the seed is handed the program production compiled; SHP-5a SHIPPED (2026-10-06):
the taint shadow's control-flow join and region models; SHP-5b SHIPPED (2026-10-06): the
emitter's security-release, borrow and capability arms; SHP-5c-1 SHIPPED (2026-10-07): the
taint shadow's capability quantities and intraprocedural heap floors; SHP-5c-2 SHIPPED
(2026-10-07): the taint shadow's call-site summaries; SHP-5c-3 SHIPPED (2026-10-08): slots and
regions end to end. SR-028 records SHP-P0's state. This is the planning artifact for taking the self-hosted
compiler from "byte-identical on its own source" to "byte-identical or refusing on every program
production accepts in the gated corpora".
**Depends on:** the self-hosting completion record
([self-hosting-completion-ladder.md](self-hosting-completion-ladder.md)) — SATISFIED: the composed
`sh_compile` pipeline, the committed seed and its succession ritual, and the exact-or-poison
emission contract of [sh-air.md](sh-air.md) and [sh-wasm.md](sh-wasm.md) are in-tree; every slice
below builds on them.
**Authors:** Nigel Robinson · Claude

---

## 1. Problem statement

The self-hosted compiler (`selfhost/*.sigil`, committed as `seed/sigil-seed.wasm`) is certified
on two kinds of input: its own source, byte for byte through the gated driver (claims 1–3 and
36–38 of [CLAIMS.md](../CLAIMS.md)), and the curated corpora of the per-stage differential
suites. [SOUNDNESS_MATRIX.md](../SOUNDNESS_MATRIX.md) SND-SELFHOST-001 says as much: these are
curated relations, not full-language equivalence. Nothing measured the compiler on the rest of the
language, and the contract it must keep there — "unsupported forms must be explicit poison; they
must never produce plausible divergent bytes" ([sh-air.md](sh-air.md)) — was enforced only on the
fence registry (claim 9).

The first measurement, taken with the SHP-0 gate on 2026-10-02 (main at `6e56791`), over every
program production accepts:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F**, parity-manifest roots and the Z3 corpus | 217 | 31 | 41 | 131 | 0 | 9 | 5 |
| **T**, agent tools | 183 | 5 | 58 | 120 | 0 | 0 | 0 |
| **X**, programs embedded in test sources | 638 | 201 | 99 | 262 | 1 | 22 | 53 |

Production itself panicked on three more programs, all extracted from one test file: a module
that calls a closure-typed parameter but never builds a closure of that signature crashes
production's Wasm emitter (pinned in `SHP_ORACLE_PANICS`). These figures are history; the pins in
[CLAIMS.md](../CLAIMS.md) §A are current.

A refusal is the designed failure. A divergence is not: it is a plausible module that is not the
program production certifies. The divergences in the corpora, and the targeted probes written to
confirm them, share a handful of causes, and three of them change what the program computes:

| Cause | Effect |
|---|---|
| Signed `i32` comparison and division are routed to the unsigned opcode row (`wa_op_byte`) | wrong result: `-1 < 0` is false |
| Record fields are written at their initializer's width but read at the declared type's | wrong result: a later field reads the high half of an earlier one |
| `u256` is lowered as a plain scalar, not a four-limb cell | wrong result, or a module that fails validation where a scalar is returned through a 4-byte signature |
| An outer-ring module is merged into the single module the self-hosted compiler emits; production emits two | wrong module |
| Type aliases and narrow-integer literal arguments get the wrong width | the module fails validation |
| A call to a method that returns nothing stores a result that does not exist | the module fails validation |
| A `Region` parameter is typed `i32` where production uses `i64` | wrong ABI |
| An inline `module name { … }` block is mis-parsed | wrong module |
| `substr` range-checks `i32` bounds without widening them | the module fails validation |
| A qualified unit-variant last arm drops its tag test and the match falls through to `unreachable`, a byte store of a 4-byte value is encoded differently, and a match arm that binds one name twice gets two locals | same results, different bytes |

One higher-kinded-type test program traps the self-hosted compiler instead of being refused.

The cause is drift, not one bug. Between 22 July and the measurement, `selfhost/air.sigil` took one
commit while production's backend kept growing, and no check tied the two together outside the
certified source. Each production change the self-hosted emitter did not mirror widened the gap
without a signal.

Measuring also surfaced a reproducibility bug in production: closure captures were laid out in
`HashSet` iteration order, so a closure with two or more captures compiled to different bytes from
one compile to the next. That is SR-028 in [RESIDUAL_RISKS.md](../RESIDUAL_RISKS.md), closed by
SHP-P0.

## 2. Design center

**The goal is a verified mirror.** Production (`crates/sigil-compiler`) stays the production
compiler and the oracle. On every program production accepts in the gated corpora, the
self-hosted compiler emits a byte-identical module or refuses, and never emits a different
module. At the end, the programs it still refuses are a short written exclusion list (§5).
Replacing production, or making the self-hosted compiler independent of it, is not a goal of this
epic.

**The gate** is `crates/sigil-runtime/tests/selfhost_backend_parity.rs`. It runs in the default
`test` lane, which is a required check: the whole sweep takes seconds (about half the programs
stop at the seed's own gate chain), so it needs no lane of its own.

- *Compiler under test:* the committed seed. It is the self-compiled compiler the lineage claims
  (38–40) are about, and `seed_is_the_oracle_emit_of_the_certified_source` already holds it equal
  to the oracle's build of the current certified source on every green commit, so the gate needs
  no test-time build of `selfhost/`.
- *Oracle:* production `compile_module`, including everything production applies on the way
  (ambient stdlib includes, the effect desugar, the formal gate).
- *Input:* both compilers compile one program (SHP-3). The seed is handed every file of
  production's source map, in its order: the source, then each ambient stdlib module production
  added. On every program production expanded, production's stages (the stage chain the seed
  mirrors, plus the effect desugar) are shown compiling that text to production's exact modules,
  so a divergence there is the seed's.
- *Corpora:* **F** is the parity-manifest roots, read from `parity_manifest.rs`'s own `ROOTS` so
  the two cannot drift, plus `crates/sigil-compiler/tests/z3_corpus`. **T** is the agent tools in
  `tools/`. **X** is the SIGIL programs extracted from string literals in `crates/*/tests`, except
  the self-hosted differential suites (curated to the self-hosted surface, they would inflate the
  result) and the gate's own planted programs. An X program is labelled with its file and the first
  four bytes of its SHA-256, so a label survives edits elsewhere in the file. A program several
  files hold takes the first in walk order, unless a pin already names another file that holds
  it: the pin keeps its label, so a copy of a pinned program added elsewhere relabels nothing.
  Rust's own tokenizer reads the test sources, and a file it cannot read stops the gate. A
  program added to F, T or X is in scope the moment it lands.
- *Verdicts,* one per program production accepts: **Identical** (the module is byte-equal),
  **Poison** (`OK:!!`), **Refused** (`REJECT:{stage}:{codes}`), **Trap** (the self-hosted compiler
  trapped or ran out of budget), and **Diverge**, which is every other answer: a different
  module, a single module where production emits two, or malformed output. A refusal counts only
  in the exact form the pipeline writes: the poison marker alone, or one of its seven stages and
  a well-formed code stream. Programs production rejects are out of scope; a program production
  panics on is out of scope too, but pinned, because a panic is a production bug. Until SHP-3 a
  further class, **Ingestion**, set apart the programs production compiled with ambient stdlib
  modules the seed was not given; SHP-3 retired it by giving the seed those modules.
- *Pins,* mirrored in [CLAIMS.md](../CLAIMS.md) §A and cited by name: `SHP_KNOWN_DIVERGENCES`
  with its exact label set `SHP_KNOWN_DIVERGENT`, which may only shrink; `SHP_TRAPS` and
  `SHP_ORACLE_PANICS`, exact; `SHP_IDENTICAL_FLOOR_F`, `_T` and `_X`, which rise; and
  `SHP_CORPUS_FLOOR_F`, `_T` and `_X` and `SHP_EXPANDED_FLOOR`, which keep the gate and its
  expanded path from going vacuous.
- *Anti-stubs* (SC-P4, in the same file): the classifier is fed a flipped byte, both refusal forms,
  one module against a two-module production output, malformed hex, an empty and an invalid
  module, every malformed refusal form and a trap; the expansion check is fed a text that drops
  one of production's modules and one that holds them in another order; the extractor is fed
  every literal form the test sources use, plus comments, a doc comment and char literals
  that must yield nothing; and a copy of a pinned program in a file that sorts earlier must leave
  the pin's label alone.

**Keep-up policy,** binding from SHP-0 on:

1. Diverge stays at zero. A change that creates a divergence fails the gate.
2. A production change that alters the bytes of a program the gate counts Identical must, in the
   same PR, either mirror the change in `selfhost/` (with a seed succession) or fence it: make the
   self-hosted compiler refuse the construct, lower the floor with the reason in the commit
   message, and add a row to §7.
3. Floors rise freely. Lowering one is a reviewed act with a named cause.

**Rejected alternatives.**

- *Fix divergences one at a time, without a gate.* That is how the gap opened; without a gate the
  next production change reopens it unseen.
- *Test `selfhost/` built at test time instead of the seed.* It would cost a full self-compile per
  run to test an artifact the seed is already held equal to, and it would leave the committed
  seed, the artifact the lineage claims rest on, unmeasured.
- *Count refusals as failures.* Refusal is the contract. A gate that punished it would reward
  guessing, which is where divergences come from.

## 3. Slice ladder

Exits are gate metrics, named by pin. Sizes are in PRs.

| Slice | Scope | Exit | Depends on | Size |
|---|---|---|---|---|
| SHP-P0 | Production: closure captures sorted by name | a three-capture closure compiles to the same bytes sixteen times; parity row added; SR-028 Closed | — | S, 1 |
| SHP-0 | The gate (0a), then every divergence made exact or a refusal (0b); no new coverage | `SHP_KNOWN_DIVERGENCES` = 0 over F, T and X | — | L, 2 |
| SHP-1 | Inner-ring tools: lower `load8`, with the `i32.wrap_i64` an 8-byte address takes, and the `ct_*` intrinsics | `SHP_IDENTICAL_FLOOR_T` reaches every inner-ring tool the seed's gate chain accepts, but one capability restriction (SHP-5) | SHP-0 | S |
| SHP-2 | Two rings: the `OK:{inner}\|{outer}` protocol superset, reduced imports, per-ring import indices, `extern "C"` (self-hosted signatures and call-site FFI imports), and the extern-effect and ring checks production applies to two-ring programs | `SHP_IDENTICAL_FLOOR_T` covers every tool the seed's gate chain accepts; an anti-stub shows an outer module calling an inner-ring index detected | SHP-1 | M–L, 2 |
| SHP-3 | Ingestion: prove production's module equals the stage chain's on the ambient-expanded text, then have the host hand the self-hosted compiler that text in production's module order | the Ingestion class is retired: no program is answered for another input than production compiled | SHP-0 | M, 2 (took 1) |
| SHP-4 | `&&` and `\|\|`, range, wildcard and multi-binder arms, string patterns and `str ==`, match guards, `?`, the `.as_*` integer conversions (`SignExtendI32`), explicit generic arguments | the CLAIMS §E rows measure byte-equal; `PIN4_UNVERIFIED_FIXTURES` is empty | SHP-3 | M, 3–4 |
| SHP-5a | The taint shadow's control-flow join model and M6 region model, so non-public bindings under control flow are checked rather than refused | every tool the shadow refused for control flow alone leaves the taint stage; `SHP_IDENTICAL_FLOOR_T` rises to what the emitter already encodes (see "SHP-5a as built") | SHP-0 | M, 1 (took 1) |
| SHP-5b | Security release, borrows and the capability operations in the self-hosted emitter, and capability types as pointer locals; regions, slots, grants and `mint` wait on the stages before it (below) | `SHP_IDENTICAL_KINDS_COUNT`, the production AIR statement kinds Identical modules carry, grows from 18 to 23 (see "SHP-5b as built") | SHP-5a | M, 2–3 (took 1) |
| SHP-5c-1 | The shadow's `split`/`draw` quantity rule and production's intraprocedural heap floors (S1, S2, S4, S6, S7, S11) on a syntactic typing that refuses what it cannot classify at a non-public label | the floor half of the lag `sh_taint_heap_lag_is_subset_safe` pinned closes and the quantity programs read exactly; no Identical program lost (see "SHP-5c-1 as built") | SHP-5b | M, 1 (took 1) |
| SHP-5c-2 | The call-site summaries: S5, the floors and regions a callee's writes raise at the call site; S8, the floors a callee's reads bring into its result | the lag `sh_taint_heap_lag_is_subset_safe` pinned closes and the pin retires; no Identical program lost (see "SHP-5c-2 as built") | SHP-5c-1 | M, 1 (took 1) |
| SHP-5c-3 | The slot, region and grant taint rules and the type check's slot intrinsics; then the region, slot and grant statements in the emitter, which no gated program reaches while a stage before it refuses them (the kind census under "SHP-5b as built") | the kind set grows again; no capability, slot or region program reads clean where production rejects it | SHP-5c-2 | M, 1–2 (took 1) |
| SHP-6 | `u256` and the wide integers (wide literals need lexer support) | programs using `u256` come out Identical | SHP-3 | M–L, 4 |
| SHP-7 | Closures: `Fn` types in the front end, capture-free closures and `call_indirect`, then captures and higher-order functions | the closure fixtures come out Identical | SHP-P0, SHP-3 | L, 3 |
| SHP-8 | Effect handlers: a self-hosted port of `effect_desugar.rs` | handler programs come out Identical or are excluded in §5 | SHP-7 | L, 2–3 |
| SHP-9 | Actors: harness, state, messaging, persistent state | actor programs come out Identical | SHP-3 | L, 4 |
| SHP-10 | Capstone | Identical equals accepted minus exclusions; the refused labels are exactly §5's list | all | S |

Milestones: **M1, fail-closed** (SHP-0); **M2, the tool mirror** (SHP-1 and SHP-2); **M3, the core
language** (SHP-3 to SHP-6); **M4, the full mirror** (SHP-7 to SHP-10). After SHP-0 the work runs
in parallel streams: tools (1 → 2), language (3 → 4 → 6), security surfaces (5), higher-order
code (7 → 8), and actors (9, after 3).

**SHP-0 as built.** 0a landed the gate in the default lane with the divergences pinned as an
exact label set; it changed no compiler. 0b removed every divergence, each by the smaller of an
exact fix or a refusal, and ended with one seed succession. Its review then found more divergent
shapes outside the corpora with probe programs, and a second round closed each class the same
way. The second round found the first round's literal handling too narrow: it had typed bare
literals at three slot kinds, while values reached every other slot at their own width.

- *Exact:*
  - signed `i32` opcodes;
  - every value written to a slot (a call or method argument, a return, a record field, an array
    element, a field or element write) typed by that slot, a bare literal taking the slot's
    integer type, and an array or construct value's parts typed by it in turn;
  - a generic record construct typed by the instance its slot names;
  - literal arithmetic in a binary operand typed by the other operand;
  - a 4-byte constant encoded as `value as i32`;
  - `Region` as `i64`;
  - a byte store always `i64.store8`;
  - a `byte_at` index wrapped only when it is 8 bytes wide;
  - a qualified unit-variant last arm that keeps its tag test, with the fall-through after the
    last tested arm jumping to the match's exit.
- *Refused, whole program:* an outer-ring module, a type alias, a `u256` or `i256` type or an
  integer literal above `i64::MAX`, a call to a higher-kinded generic (the former trap), and a
  parse-error node.
- *Refused, at the construct:*
  - a value whose type differs from its slot's;
  - literal arithmetic where the slot's type is not visible: an assignment's or a tuple's array,
    a generic field with no instance in view, or an enum payload of an untracked type;
  - a tuple literal as an enum payload of an untracked type;
  - a literal-typed enum payload argument narrower than `i64`;
  - a constant not declared `i64`;
  - a name bound twice in one pattern;
  - a call whose return type is unknown, and a void method call;
  - `substr` bounds that are not `i64`, and an `i32` `byte_at` index (exact since the
    signed-index mirror, below).

The full rule list is in [sh-wasm.md](sh-wasm.md); `SHP0B_FENCES` pins programs of each class by
name. One planned item needed nothing at the time: a guarded range-for, which an earlier sweep
of the ungated emitter saw keep a bounds check production elides, was refused by the seed's own
gates (the taint shadow refused every range-for); since SHP-5a the shadow checks range-for bodies
and the emitter poisons an access whose loop variable a guard names (`rf_index_guarded`, "SHP-5a
as built").
Three shapes the review probed are miscompiled by production itself, so the seed refuses them
rather than matching them:
- an `[i32; N]` literal nested in a tuple element or an enum payload, laid out at 8-byte stride;
- a literal enum payload argument narrower than `i64`, stored as 8 bytes;
- an `i32` `byte_at` index, bounds-checked signed (fixed by SR-030 and mirrored, below).

Their fixes are production changes. One program that was identical now refuses:
`tests/frontends/rust/compile/range.sigil`, whose record refinement the parser skips (a skipped
construct cannot be shown to be codegen-free); two others in the same corpus became identical,
so the F floor still rose. Measured after the succession:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 218 | 32 | 50 | 132 | 0 | 4 | 0 |
| **T** | 183 | 5 | 58 | 120 | 0 | 0 | 0 |
| **X** | 638 | 205 | 164 | 262 | 0 | 7 | 0 |

**SHP-1 as built.** Measured on the SHP-0 seed, the tools split into 92 inner-ring and 91 two-ring
programs. Every two-ring tool is refused by the seed's typecheck, which does not know `extern "C"`
signatures: that is SHP-2. Of the 58 inner-ring tools that poisoned, 57 needed only `load8`. SHP-1
lowers it exactly, wrapping an 8-byte address to `i32` as production does, and teaches the
typecheck and the emitter `ct_eq`, `ct_lt` and `ct_select`. Two items in the row as planned were
not needed: `store8` was already exact, and no tool converts an `i32` with `.as_i64()`, so
`SignExtendI32` moves to SHP-4 with the rest of the `.as_*` conversions. An `i32` index to
`byte_at`, planned here, was refused from SHP-0b's review until the signed-index mirror (below),
and a `u32` index is mirrored exactly.

One refusal is deliberate: a `ct_*` operand that is not 8 bytes wide. Production's typecheck
accepts any machine integer there, but its lowering applies i64 opcodes to the operand as given,
and the module does not validate: reproduced for `ct_eq`, `ct_lt` and `ct_select` on `i32`
operands, which wasmtime refuses to compile. The seed refuses the shape (§5) rather than emit an
invalid module or a different one. (Corrected in place after SHP-1: production now rejects such an
operand at typecheck, so the shape left §5; see the narrow `ct_*` operands, below.)

The slice's review left the shadow typecheck's intrinsic parameters unchecked: production
accepts any machine integer there and names a wrong one with its own code, so a concrete
parameter code put a code production does not emit into the shadow's stream, while an unchecked
one only misses production's. The emitter refuses the widths it cannot lower, and a call to a
known intrinsic with the wrong argument count is refused where it stands instead of falling
through to a same-named function.

`SHP1_FENCES` pins one program per construct by name: seven come out Identical and three are
refused. (The three refused rows left the list after SHP-1; see the narrow `ct_*` operands,
below. Two other refused rows joined it later; see the `ct_lt` order, below.) Measured after the
succession:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 218 | 33 | 49 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 638 | 208 | 165 | 258 | 0 | 7 | 0 |

Every inner-ring tool the seed's gate chain accepts is now Identical but one, which poisons on a
capability restriction (SHP-5). The 28 inner-ring tools the gate chain refuses are front-end work.
27 stop at the taint shadow: 25 hold non-public bindings under control flow (SHP-5), and two are
actor and slot demos (SHP-5 and SHP-9). One uses an explicit generic argument (SHP-4).

**The production panics, fixed.** The three programs in `SHP_ORACLE_PANICS` were one emitter bug.
Production looked a `call_indirect`'s type up among the module's function types, which hold a
closure signature only when the module lifts a closure of it, so a module that calls a
closure-typed parameter and builds no closure of that signature crashed. The emitter now appends
each such signature after the function types (`wasm_call_indirect_types.rs`), and the set is
empty. Those three programs and the six embedded in the fix's tests are in scope, and the seed
refuses all nine at typecheck (`T062` at the call), because its typecheck does not resolve a call
through a closure-typed parameter. On every other program in the three corpora, production's
modules are byte-identical to before. Measured after the fix:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 218 | 33 | 49 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 647 | 208 | 165 | 267 | 0 | 7 | 0 |

**The signed-index mirror (after SHP-1).** Production compared a 4-byte signed index with a
signed compare at its bounds checks, so a negative index read or wrote before its buffer
(SR-030). Its fix copies that index into a `u32` before every check. The seed had refused an
`i32` `byte_at` index since SHP-0b's review, and it lowered an `i32` array index with
production's old signed check, which no corpus program measured. Under the keep-up policy it
now makes the same copy at both, with one seed succession. `SHP0B_FENCES` pins the three shapes
by name; `byte_at_i32_index` moved from Refused to Identical. The fix's slice checks need no
mirror, since the seed refuses slice construction and slice indexing. No corpus program changed
class: F gained the fix's own fixture, which the seed refuses on its slice. Measured after the
succession, with the production-panic fix above:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 219 | 33 | 50 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 647 | 208 | 165 | 267 | 0 | 7 | 0 |

**The narrow `ct_*` operands (after SHP-1).** Production's typecheck accepted any machine integer
as a `ct_eq` or `ct_lt` operand or a `ct_select` branch, and its lowering applied i64 opcodes to
the operand as given, so a 4-byte operand gave a module that does not validate. Production now
rejects that operand at typecheck (`T075`), and the hint names the widening, `.as_i64()` or
`.as_u64()`. Rejecting rather than widening in AIR keeps the constant-time sequences the 8-byte
ones `secret-ct.md` §5 audits (`is_ct_operand_type` in `type_check/expressions/intrinsics.rs`
gives the full reasoning), and it needed no seed succession: the seed already refused the shape,
and its emitter refusal stays, now as a fail-closed backstop. The three `SHP1_FENCES` rows pinned
Refused left the list, since the fence test requires production to accept every row, and the
shape left §5. They moved to `SHP1_PRODUCTION_REJECTS`, where
`shp1_narrow_ct_operands_are_rejected_by_production_and_refused_by_the_seed` pins each as exactly
`T075` in production and a refusal from the seed. The self-hosted typecheck's comment that the oracle accepts any machine integer at
these parameters (`tc_build_sigs`) went stale with the fix; the certified source is
digest-pinned, so SHP-2's succession corrected it. F gained the fix's accept fixture,
`tests/compile/ct_wide_operands.sigil`, which comes out Identical, so `SHP_IDENTICAL_FLOOR_F` rose
with it; its reject twin is out of scope. X gained two programs, the fix's whole-program test
literals, both Poison. Measured after the fix (X also holds one Refused program another change
added since the previous table):

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 34 | 50 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 650 | 208 | 167 | 268 | 0 | 7 | 0 |

**SHP-2a as built: the extern front end.** Every one of the 91 two-ring tools is a single module
headed `#[ring(outer)] #[trusted]` whose `tool_main` calls one `extern "C"` function, and the
seed's type check stopped each at that call with `T062`: it registered no extern signatures. It
now registers each `extern "ABI" fn` the way production's type check does, from the declared
params and a Unit return when none is written, so a call to one types like any call. It also
reports the four codes production's type check emits for externs and rings, which the composed
gate now enforces:
- `T160` and `T161`, an extern declaration whose effect row lacks `FFI` or `Unsafe`;
- `R006`, `#[trusted]` on a module that is not `#[ring(outer)]`;
- `E003`, a top-level fn of an inner-ring module whose row names `FFI` or `Unsafe`.

`R004` and `R007`, calls into the other ring, are not mirrored in the type check. A qualified
cross-module call is already untyped there and refused by the emitter, and SHP-2b adds an emitter
check that refuses any call into the other ring. `shp2a_extern_and_ring_checks_match_the_oracle`
pins production's exact answer for each code, for an inner-ring call to an extern (the ring
gate's `R003`, now reached) and for an extern no call reaches (no import, so the module is
identical), and requires the seed's answer to be the same string.

Two-ring modules still refuse whole, so no program became identical. Measured after the
succession:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 219 | 33 | 57 | 125 | 0 | 4 | 0 |
| **T** | 183 | 63 | 6 | 114 | 0 | 0 | 0 |
| **X** | 648 | 208 | 182 | 251 | 0 | 7 | 0 |

Five tools (`manual_http_alloc`, `probe_fs_i64`, `task026_read_file`, `task051_fetch_url` and
`task199_edge_multi_ffi`), seven F programs and seventeen X programs now pass every gate and
poison on the outer ring, which SHP-2b emits. The other 86 tools now stop at the taint shadow
instead of the type check, as do two F programs and one X program. Each of the 86 binds the
extern's result, which is `Internal`, and branches on it, a shape the shadow does not model
(`SH_TAINT_UNSUPPORTED`, SHP-5). So SHP-2b can lift `SHP_IDENTICAL_FLOOR_T` by those five tools
at most, and the 86 wait on SHP-5. SHP-2's exit is unchanged: `SHP_IDENTICAL_FLOOR_T` covers
every tool the seed's gate chain accepts.

**SHP-2b as built: two-ring emission.** A program with an outer-ring module now compiles as
production compiles it, to two modules, answered in the protocol's superset form
`OK:{inner}|{outer}`; a single-ring answer is unchanged. The emitter numbers functions as
production does: every module in source order, both rings, a module with no function of its own
taking one for its synthesized initializer. Each ring is its own module, built from that ring's
functions alone:
- its imports: the inner ring's eight runtime imports, or the outer ring's `fuel_decrement` and
  `alloc` (so `alloc` is `call 1` there, `call 4` in the inner ring), then one `ffi.{name}` import
  per extern its functions call;
- its function types, exports and code, and a table sized by the whole program's function count,
  with one element segment per run of consecutive function indices, so a slot of the other ring
  stays empty (a ring with no function has neither: an outer-only program's inner module is
  production's fixed empty module);
- its own string data and `BUMP_PTR`, each from 1024.

A call takes the callee's index in the caller's ring: the ring's import count plus the callee's
position there. A call into the other ring has no index and is refused; production rejects such a
program first (`R004`, `R007`). A call to an extern is production's `ExternCall`: the destination
before the arguments, no fuel, then the ring's FFI import. The FFI imports are production's
`collect_ffi_imports` exactly: one per distinct key (the extern and the wasm types at the call), in
the order the keys first occur over the ring's functions, their blocks and their statements. The
import count fixes every index in the ring, so it is counted before any body is encoded, from the
distinct externs the ring's functions call, and a ring whose calls register another count is
refused. Also refused: an actor in an outer-ring module (its messaging has no import there; the
taint shadow, which models no actor yet, refuses it first; production rejects the declaration
too, R014), an FFI call in the inner ring (the
ring gate's `R003` rejects it first), and a call to an extern that returns `()` (production's type
check rejects it, `T073`; the seed's does not, so the emitter refuses it, as it does a direct
call to a `()` function).

The function numbering also fixes a latent single-ring miscompile that SHP-2b's probes found
outside the corpora: a call to a function after a module with no function of its own was numbered
one too low and reached that module's initializer, in a module that validates
(`fnless_module_then_call`, SR-029).

SHP-2b's review found two more classes outside the corpora, each probed against production. One
predates SHP-2. A first module whose only function is generic has no function of its own:
production synthesizes its initializer, then files the generic's instances in the first module
after it. The seed counted the instances as the module's own functions and dropped the
initializer, so its module lacked production's `{module}__init` export and numbered every later
function one lower. It is now exact (`generic_only_first_module`, SR-029).

The other came with two-ring emission. Production resolves an extern call in the caller's module:
an extern is private to its module, so a bare call from another module is `T062`. A call is an
FFI call only when it resolved to an extern. When the review ran, production still decided that
from the program's extern names, so a module's own function named like another module's extern
compiled to an FFI call, even in a module that is not `#[trusted]`; production has since fixed
that (the extern set is keyed by qualified name). The seed's type check holds one signature per
name for the whole program and has no module context. So the emitter refuses four shapes before
any function is walked (`ai_extern_refusal`):
- a call to an extern another module declares, which production rejects
  (`shp2_call_to_another_modules_extern_is_refused`);
- an extern named like a function: production resolves each call to whichever of the two the
  caller's module holds, and one signature per name cannot tell them apart
  (`extern_named_like_a_fn`);
- one extern name declared in two modules (`extern_declared_twice`);
- an extern named like one of production's intrinsics, called or not. Production resolves an
  intrinsic's name before any function or extern, so it never calls such an extern; the seed's
  type check models only some intrinsics and typed a call to the rest by the extern
  (`shp2_extern_named_like_an_intrinsic_is_refused`, which reads production's intrinsic list, so
  an intrinsic production adds is checked with no edit).

A user function named like an intrinsic the seed does not model is the same mismatch outside the
extern path, and it predates SHP-2: the seed compiles a call to it (to `slot_take`, say) where
production resolves the intrinsic and rejects the program. The gate measures only programs
production accepts, so this is outside it; no production-accepted program of that shape was found
to differ.

One difference is outside the mirror by the protocol's own rule: for a module that is both
`#[trusted]` without `#[ring(outer)]` and holds a function whose row names `FFI`, the seed's type
check reports `R006` before `E003` and production the reverse. The protocol compares the tc
stage's codes as a set (`normalize_codes` in `pipeline_differential.rs`), so the order is not
part of the answer.

`SHP2_FENCES` pins one program per rule, Identical (both module orders, the empty inner module,
the outer ring's `alloc`, per-ring strings, the call after a function-less module, a first module
whose only function is generic, and the FFI imports' order by first call, function, block and call
types) or Refused (an extern named like a function and an extern declared twice). The outer-ring
actor it also pinned Refused left it when production began rejecting the declaration (R014);
`shp2_outer_ring_actor_is_rejected_by_production_and_refused_by_the_seed` pins the seed still
refusing it.
`shp2_classifier_reads_the_two_ring_form` holds the two-module form to production's two modules in
order, every malformed form included, and is the slice's exit anti-stub: production's outer module
with one call renumbered by SR-018's formula (the global function index, which lands on a
same-signature neighbour) validates, and the classifier reports it. Ingestion excuses no module
count that differs, since every ambient module production can inject is inner-ring
(`shp2_ambient_includes_add_no_outer_module`, retired with the class by SHP-3).
`pipeline_differential.rs` pins four two-ring programs byte-identical in the default lane.
Measured after the succession, on main with the narrow `ct_*` fix, R008 and the extern routing
fix merged in:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 44 | 47 | 125 | 0 | 4 | 0 |
| **T** | 183 | 68 | 1 | 114 | 0 | 0 | 0 |
| **X** | 657 | 279 | 120 | 251 | 0 | 7 | 0 |

Against main's seed on the same tree, every program that moved became Identical, from Poison or
from the type check's refusal SHP-2a lifted: 10 in F (seven outer-ring programs, and the three
stdlib modules that call several externs), the 5 tools SHP-2a predicted, and 70 in X, among them
two-ring programs the R008 tests embed. No program left Identical. Every two-ring tool the seed's
gate chain accepts is now Identical, which is SHP-2's exit; the other 86
stop at the taint shadow and wait on SHP-5. Six two-ring X programs still poison: four on
constructs other slices own, `Fn`-typed returns (SHP-7, two programs), `&&` and an `.as_i64()`
conversion (SHP-4); a call qualified by its module's name (`outer_lib::helper`), which the seed's
emitter refuses; and an extern named like a function, one of the programs the R008 tests embed,
which `ai_extern_refusal` refuses.

**The `ct_lt` order (after SHP-2).** Production's `ct_lt` returned the sign bit of the wrapping
`a - b`, so it misordered an `i64` pair whose difference does not fit in an i64 and read a `u64`
as signed (`tests/attack/KNOWN_GAPS.md`). It now takes the sign bit of an overflow-safe word,
signed for two `i64` and unsigned for two `u64`, with the order carried in AIR. Its typecheck
rejects one `i64` beside one `u64` (`T075`) and checks an integer literal beside a `u64` as a
`u64`. Every `ct_lt` changes bytes, and Identical programs hold one, F's
`ct_wide_operands.sigil` and the two `ct_lt` rows of `SHP1_FENCES` among them. (The fixture now also holds an
unsigned `ct_lt`, and it stays Identical; F's new reject fixture,
`tests/reject/ct_lt_mixed_signedness.sigil`, is out of scope.) Under the keep-up policy the
seed emits the same two sequences, with one seed succession, oracle-agreed in one stage because
the certified source calls no `ct_lt`. The seed takes the order from its operand tokens and
refuses a pair whose tokens differ. That covers production's `T075` pair, pinned by
`shp1_mixed_signedness_ct_lt_is_rejected_by_production_and_refused_by_the_seed`, and an integer
literal or literal binding beside a `u64`, which production accepts but the seed lowers to an
`I64` local. Two new `SHP1_FENCES` rows pin that refusal, so the list holds seven Identical rows
and two Refused. The succession also extends the intrinsic table's comment in the self-hosted
typecheck (`tc_build_sigs`, which SHP-2's succession corrected) to the mixed pair and the literal
rule. No corpus program changed class, so the table is SHP-2's, above. Measured after the
succession:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 44 | 47 | 125 | 0 | 4 | 0 |
| **T** | 183 | 68 | 1 | 114 | 0 | 0 | 0 |
| **X** | 657 | 279 | 120 | 251 | 0 | 7 | 0 |

**The construct-slot mirror (SR-032).** Production typed the parts of a construct on their own:
an enum constructor's arguments, a tuple literal's elements and an assigned value took no expected
type, so a literal kept its `i64` default and a generic construct built the `i64` instance, while
every reader used the slot's declared type. Its fix types each part by its slot. The seed had
copied the old rule, so two programs the gate counts Identical changed bytes: the named fence
`tuple_i32_literal`, and the narrow-payload row of `ag6_6_narrow_variant_size_corpus` (where
production also now takes a type parameter that no payload binds from the expected instance, so
the cell is the instance's). Under the keep-up policy the seed mirrors the rule, with one seed
succession, wherever it can see the slot: a bare literal in a scalar enum payload takes the
payload's type; a type-parameter payload takes the instance's type argument; a tuple literal takes
its slot's element types. Elsewhere it refuses a literal part ([sh-wasm.md](sh-wasm.md), the
construct-slot rule). `SHP0B_FENCES` pins the shapes by name: `enum_payload_i32` and
`i32_array_in_tuple` move from Refused to Identical, and the other SR-032 rows are new. Per
program, against the old seed and the old compiler, nothing in F, T or X lost Identical: F gains
the fix's parity fixture, which the seed refuses on its assignment of a generic construct, and X
gains the fix's tests; of those the old compiler also accepted, two move from Poison to
Identical. Measured after the succession:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 33 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 673 | 211 | 186 | 269 | 0 | 7 | 0 |

**The construct-slot mirror, review round.** Production pinned no argument of a generic function,
while the mirrored seed typed a compound argument by the instance's parameter, which
monomorphization fully substitutes. So a literal part of such an argument diverged
(`g(n, (1, 40))` for `t: (i32, i64)`); an array literal and a bare unit variant of a generic enum
already diverged there on the seed before the mirror. No corpus program holds these shapes. The
review round pins a generic function's argument in production once the arguments before it have
bound every type parameter its declared type mentions. The seed cannot tell which arguments
those are, so it lowers a tuple, array, record or enum argument of a generic instance against a
hidden slot (`cv_call_arg_tid`; `TcSig.inst` marks an instance) and refuses a literal part there,
with one seed succession. `SHP0B_FENCES` pins nine `generic_call_*` rows: six refused, and three
identical where nothing depends on the slot (a plain enum, a local tuple, a scalar literal). Per
program over F, T and X, the verdicts of the old compiler and seed and the new ones are the same;
X gains the review round's tests. Measured after the succession:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 33 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 685 | 212 | 193 | 273 | 0 | 7 | 0 |

**The construct-slot mirror, second review.** Production now pins a generic argument by a
turbofish too, narrows the rest once the instance is known, checks each against its concrete
parameter, and rejects a value typed by an integer literal it is not wherever a narrow slot would
take it. None of that changes what the seed must refuse: a program production newly rejects
leaves the gate, and the compound arguments production now narrows were already refused. One
hole was new. Production now pins an enum argument of a generic function, so a bare variant
several enums declare (`g(n, B(n))` with `B` in two enums) was accepted, while the emitter's
ST-1 fallback, with the slot hidden, took the first declaring enum. A record field had the same
divergence on the seed before SR-032. Both now refuse (four ST-1 sites, one seed succession);
`SHP0B_FENCES` pins six `ambiguous_*` rows, four refused and two identical where the slot is in
view. Production's bare unit variant also took the first declaring enum in a `HashMap`'s order,
so it compiled or failed by chance; it now takes its slot's enum, or T236. Per program over F, T
and X, every verdict is unchanged except the programs of `construct_slot_width.rs` this review
added or removed. Measured after the succession:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 33 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 684 | 212 | 193 | 272 | 0 | 7 | 0 |

**The construct-slot mirror, third review.** The emitter's match lowering resolved a bare pattern
(`B(v) =>`, no `E::`) by the first enum that declares the variant, while production names the
scrutinee's: with `B` in two enums and an `E2` scrutinee the seed tested `E1`'s tag. This
diverged on the seed before SR-032, outside every corpus. A bare pattern that several enums
declare is now refused (one seed succession), and `SHP0B_FENCES` pins it beside the qualified
pattern, which stays identical. Production's own changes in this review leave the seed's answers
alone: a program it now accepts (`or_default(None, 5)`) or rejects (an out-of-range literal in a
compound argument) is refused by the seed either way. Per program over F, T and X, every verdict
is unchanged except two programs this review added to `construct_slot_width.rs`. Measured after
the succession:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 33 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 686 | 212 | 193 | 274 | 0 | 7 | 0 |

**The construct-slot mirror, fourth review.** Production's generic argument check now compares
representations, so it accepts again what main accepted and read alike: a `u64` where a
literal's `i64` instance reads it (`max(0, n)`), and a bare `None` typed without arguments. It
also checks a closure argument's parameter and return types, rejecting a closure whose
argument is stored otherwise. No seed change: the seed refuses each newly accepted program, and
per program over F, T and X every verdict is unchanged except the programs this review added to
or removed from `construct_slot_width.rs`. Measured:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 33 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 690 | 212 | 194 | 277 | 0 | 7 | 0 |

**The construct-slot mirror, fifth review.** Production now fits every part of a generic call or
construct to its instance once the instance is known: a closure inside a tuple, an `Option`, a
generic record's field or a generic enum's payload has its parameter and return types checked;
the literals beside a closure, and a generic record's field or enum payload built with no
annotation, are narrowed; a difference in signedness passes only where a literal bound the
parameter; and a closure's annotations are held to T231. No seed change. The seed refuses each
program production newly accepts (`apply(None, c)`), and production's new rejections take
programs out of the gate. Per program over F, T and X, every verdict is unchanged except four
programs this review added to `construct_slot_width.rs`: one production now accepts and three it
now rejects, all four refused by the seed. Measured:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 33 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 699 | 212 | 197 | 283 | 0 | 7 | 0 |

**The construct-slot mirror, sixth review.** Production now pins a generic enum's payload and a
generic record's field once the parts before it bind its type parameters, as it pins a generic
call's argument; it reports an out-of-range literal in a generic part once; and it compares a
slot a literal bound at the `i64` default through every type. No seed change. Per program over
F, T and X, every verdict is unchanged: the new pins change no program the seed answers for,
and the only X programs this review adds that production accepts, two known-gap pins, are
poisoned by the seed. Measured:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 220 | 33 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 701 | 212 | 199 | 283 | 0 | 7 | 0 |

**The construct-slot mirror, on the merge with main.** The construct-slot tables above were
measured before three changes on main came into this branch: the narrow `ct_*` operands, above;
R008, under which an outer-ring extern needs `#[trusted]`; and the R004 and E002 scope notes. So
they count none of those changes' programs. Per program over F, T and X, the merge changes no
verdict the construct-slot mirror measured. `tests/compile/ct_wide_operands.sigil` comes out
Identical, and the narrow `ct_*` fix's two X programs come out Poison, as its own table says. The
ring tests of the other two changes add eight X programs (one Identical, four Poison and three
Refused) and rewrite one Refused program. Measured on the merge:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 221 | 34 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 710 | 213 | 205 | 285 | 0 | 7 | 0 |

**The construct-slot mirror, seventh review.** Production now pins a generic enum's function-typed
payload with no instance in view, as an enum binds no effect-row variable. It reads a function's
literal-typed part alike at `u64`. It reports a literal once, at its span, where it had skipped
every value typed `Type::Error`. No seed change. Per program over F, T and X, every verdict is
unchanged except two programs this review adds, the `u64` reads of a function's literal-typed
part, which production now accepts and the seed refuses. The X corpus holds only the literal
programs of the test files. A program a test builds with `.replace` or `format!` reaches the
extractor with its placeholders, fails to parse, and is not counted. The test that runs it is its
evidence. Measured:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 221 | 34 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 712 | 213 | 205 | 287 | 0 | 7 | 0 |

**The construct-slot mirror, eighth review.** Production now rejects a function value whose
parameter or return a literal typed wherever a slot reads it at a narrower function type: a
resolved call's argument, a `let` and a return (T071, T041, T049). No seed change. Per program
over F, T and X, every verdict is unchanged. X gains one literal program from this review's
tests, which production accepts and the seed refuses. Measured:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 221 | 34 | 51 | 132 | 0 | 4 | 0 |
| **T** | 183 | 63 | 1 | 119 | 0 | 0 | 0 |
| **X** | 713 | 213 | 205 | 288 | 0 | 7 | 0 |

**The construct-slot mirror, on the merge with SHP-2.** SHP-2 and the construct-slot mirror both
changed the certified source, so the merge took one more seed succession. Main's seed compiled the
merged source, and the result agreed with the oracle in one stage (`seed/PROVENANCE.md`). Per
program over F, T and X, every program on both sides keeps the verdict main measured. The merge
adds the construct-slot mirror's 57 programs: in X, 5 Identical, 33 Poison and 18 Refused, and in F
`construct_slot_width.sigil`, Poison. Each identical floor holds. Measured on the merge:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 221 | 44 | 48 | 125 | 0 | 4 | 0 |
| **T** | 183 | 68 | 1 | 114 | 0 | 0 | 0 |
| **X** | 713 | 284 | 153 | 269 | 0 | 7 | 0 |

**The construct-slot mirror, on the merge with the `ct_lt` order.** The `ct_lt` fix changed the
certified source too, so this merge took another one-stage seed succession from main's seed
(`seed/PROVENANCE.md`). Per program over F, T and X, every program on both sides keeps the verdict
main measured. The merge adds the same 57 construct-slot programs as the merge above. The table
is unchanged from that merge:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Ingestion | Diverge |
|---|---|---|---|---|---|---|---|
| **F** | 221 | 44 | 48 | 125 | 0 | 4 | 0 |
| **T** | 183 | 68 | 1 | 114 | 0 | 0 | 0 |
| **X** | 713 | 284 | 153 | 269 | 0 | 7 | 0 |

**SHP-3 as built: one input for both compilers.** The gate now hands the seed the program
production compiled, not the source alone. `compile_module` gives production one source, and its
source map grows past that source only when the ambient include adds stdlib modules; production
then sorts the files by name, so the source (`<inline>`) comes first and the stdlib modules follow
in path order. The gate joins those files' texts in that order (`production_input`) and hands the
seed the result; a source compiled alone is handed over unchanged. No `selfhost/` change was
needed, so there is no seed succession: the seed already compiles a program of several modules.

The proof the plan asked for runs on every program: for each program production expanded, the
stage chain the seed mirrors (parse, resolve, type check, AIR, memory, fuel, emit, as
`oracle_compile` runs it), plus the effect desugar, the one pass outside that chain that changes
the bytes `compile_module` emits, compiles the handed text to production's exact modules. On the
corpora, 173 programs are expanded (`SHP_EXPANDED_FLOOR`) and the chain agrees on all of them, so
production's multi-file path adds nothing to the bytes that the text does not carry.
`shp3_the_seed_is_handed_the_program_production_compiled` shows the check failing a text that
drops one of production's modules and one that holds them in another order, and a plain
program handed over unchanged.

With one input there is nothing left to set apart, so the Ingestion verdict, its pins and the
classifier's ingestion exemption are gone, and with them the census that held the exemption to
inner-ring ambient modules. Measured on the same seed:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Diverge | Expanded |
|---|---|---|---|---|---|---|---|
| **F** | 221 | 48 | 15 | 158 | 0 | 0 | 89 |
| **T** | 183 | 68 | 1 | 114 | 0 | 0 | 0 |
| **X** | 713 | 295 | 135 | 283 | 0 | 0 | 84 |

Every former ingestion program but one is now Identical: the stdlib `arena`, `map`, `option` and
`vec` modules, and six embedded programs (the higher-kinded and trait-bound parses). The
remaining one, a string-search program, now poisons. Five more X programs that poisoned or were
refused for want of the stdlib are now Identical (a region snapshot, a heap-floor taint case, a
`Vec` compile and two `Vec` runtime programs). The other moves are between refusal kinds, as
programs reach a different refusal with the stdlib modules present: in F, 38 from Poison to
Refused and 5 the other way; in X, 23 and 7. No program left Identical, and none diverges.

**SHP-5a as built: the taint shadow's control-flow join and region models.** Before this slice
the self-hosted taint shadow (`selfhost/taint_check.sigil`) refused every non-public binding
under control flow with `SH_TAINT_UNSUPPORTED`, and every range-for outright; the gate's
dump put 322 of the refused programs at that one stage, 86 of the two-ring tools among them
(they open with `let raw: i64 @Internal = fs_read(..); if raw < 0 { .. }`). The shadow now
carries production's join model: `if`/`match` arms and loop bodies walk clones of the env and
the merge joins every pre-construct name (records field-wise); a one-sided `return`, `break`
or `continue` raises the continuation taint the oracle folds into every later expression;
`break`/`continue` capture frames the loop exit and loop head join; a `let` that shadows an
outer name is restored at its block's end, in the env and in every captured frame; a `while`
runs to the loop-head fixpoint with its guard re-derived from each head (and is T021 from a
head whose guard turned `@SecretCT`); `for` bodies run at a pc fixed by the bound or iterable,
with the loop variable restored after; match patterns bind at the scrutinee's taint and are
restored. It also carries the M6 region model: each bound `alloc` is a region (keyed by its
node, so a loop body's site names the same region on every pass), a pointer local carries its
source's regions through `let q = out`, `q = out + i` and `q = alloc(8) + k`, a raw store
taints every operand's regions with the join of all operands and the pc, and every read folds
its regions' taint. The withdrawn M5b/M6 rejects of the taint differential are back.

What the shadow still does not model refuses as before (a tuple let whose value carries a
nonpublic pc, guarded matches, actors, closures, a function naming more than 62 `alloc`
regions) or lags subset-safe: production's heap floors (S1-S9) and call-site summaries (S5)
produce codes the shadow does not, and where only they fire the shadow is clean — on programs
production rejects, never a false code — pinned by `sh_taint_heap_lag_is_subset_safe` and
counted below. Capability operations still read as `@Public` values (SHP-5c).

Measured against the oracle with the composed shadow tool (the taint differential's harness)
over every F and T file and every embedded X program: 301 F/T files and 720 X programs give
the oracle's exact code set; 108 F/T files and 238 X programs are refused or lag; no program
receives a code the oracle does not, except the six `@Flow` programs whose callers were
already given a spurious code beside the refusal before this slice. The lag, program by
program: five S5 call-summary shapes, one `vec_store`, two capability `split`/`draw`
quantities, one generic `@SecretCT` callee, and the eleven programs the join model newly
reaches whose heap floor alone rejects them were reduced to the five S5 shapes by the region
model. A hand-written join and region fixture set and a generated join surface
(`joinmodel_surface_agrees_exactly`, 32 cases in CI and 256 under `PROPTEST_CASES=256`, the
budget the test reads) agree exactly on both sides.

The self-compile paid for the join model until three refactors: the env holds one entry per
name (an upsert, where the append-only history made every lookup and clone grow with the
statements before it), in a fixed order that lets a merge or capture index a clone by the name
list read from its source instead of scanning it per name, and a loop's converging pass is its
real pass (the pass that leaves the head, the regions and their taint unchanged walked the body
from the converged state, as the oracle's one more walk would). The seed's own compile then
consumes 238,422,927 fuel against 217,179,615 before the slice (10% more), and under CPython
`interp/ddc.py` compiles the certified source in 1,480 s against 1,345 s on main (2.11 against
1.92 billion interpreter steps, the same 10%). The certified source grew from 994,634 to
1,025,810 CSIR nodes,
over the formal projection's 1,000,000-node ceiling; the ceiling and the v9 record ceiling
(`formal::MAX_NODES`, `formal_v9::MAX_RECORDS`, Lean `maxNodes`) are now 2,000,000, still under
the 64 MiB wire ceiling, with the raise's reason at each constant.

One emitter change rode along. Range-for bodies reach the emitter for the first time, and two
X programs diverged: an index access a guard on the loop variable narrows (`for i in 0..10 {
if i < 5 { a[i] } }` over `[i64; 5]`), where production tightens the index's interval with the
guard (RF-M3, its refinement channel) and elides the bounds check this emitter keeps. The
emitter now poisons such an access (`rf_index_guarded`): an access no guard on its loop
variable encloses elides exactly as before. The fence costs one X program that was Identical
with the join model alone (a guard the bound already covered). Measured on the new seed:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Diverge | Expanded |
|---|---|---|---|---|---|---|---|
| **F** | 221 | 49 | 16 | 156 | 0 | 0 | 89 |
| **T** | 183 | 179 | 1 | 3 | 0 | 0 | 0 |
| **X** | 717 | 340 | 141 | 236 | 0 | 0 | 84 |

Against SHP-3's table: T Identical rises from 68 to 179 (111 tools; the 86 two-ring tools and
the inner-ring tools whose `@Internal` or `@Secret` data met control flow), X from 295 to 340,
F from 48 to 49; the three T programs still refused are the capability restriction (SHP-5b)
and two actor and slot demos (SHP-5b, SHP-9). `SHP5_FENCES` pins a secret branch, an
`@Internal` extern result branched on, a secret stored through a pointer rebound to a fresh
buffer every iteration, a match on a secret scrutinee, a range over a secret bound and a
secret-guarded `break` Identical, and the two range-for rows above (covered: Identical; guarded:
Refused); `shp5_the_taint_stage_passes_control_flow_over_secrets` reads the seed's stage for
each and shows a secret-capturing closure still refused at the taint stage.

Review follow-ups, for SHP-5b: `rf_index_guarded` poisons more than RF-M3 narrows (a non-literal
bound, a `while` or `match` naming the index, a `Vec` index), where production and this emitter
already agree, and it walks the node arena twice per index access before `rf_index_elided` walks
it again; gate it on the loop's range fact, the array's declared size and an `if` guard, and
share one innermost-loop lookup. `tt_lookup` in `selfhost/taint_check.sigil` has no caller since
every read folds region taint through `tt_read`; delete it with the next succession rather than
leave a region-blind lookup for a later arm to reach for. The one X program the broad poison
costs is counted in the 340 above.

**SHP-5b as built: the emitter's security-release, borrow and capability arms.** Before this
slice the emitter poisoned every program with a `declassify`, a borrow of a cap, a `restrict`, a
`restrict_deadline`, a `split` or a `draw`, and typed a capability annotation (`Fuel`, or the
parametric usage `Approval(2030)`) as its `<skip>` sentinel. The kind census the slice adds to
the gate (`shp5b_identical_kinds_cover_the_pinned_set`, every production AIR statement kind by
the verdict of the programs carrying it) put `SecurityRelease` on six poisoned programs,
`CapRestrict` on ten, `CapSplit` on two, `CapDraw` on one and a non-slice `Borrow` on one, each
accepted by every stage before emission. The same census put regions, slots, grants and `mint`
only on programs the type check or the taint shadow refuses (regions and slots at both, grants at
the shadow with closures, `mint` at the name resolver), so the emitter has no gated program on
which to prove those arms; they move to SHP-5c, after the shadow admits them.

The emitter now carries production's lowerings ([sh-wasm.md](sh-wasm.md), "Rules from SHP-5b"):
a capability type annotation is a pointer local (`lower_type(Type::Cap)`), found by an arena scan
for the `cap type` declaration on the fallback path no annotation of the certified source
reaches; `declassify` and `declassify_ct` are `SecurityRelease`, the value's source local
allocated first, the cap operand resolved, and a dead pointer local allocated as the ownership
sink; a borrow of a non-array local is `Borrow`; `restrict` is `CapRestrict` with the authority's
bit, its index in the receiver's cap type declaration, and `restrict_deadline` the same statement
with the full mask; `split` and `draw` are one kind, the amount lowered after the receiver is
resolved, emitted as production's signed guard and the `cap_split` call. The receiver's cap type
is read from the function's own bindings (a parameter's or an annotated let's annotation, or an
unannotated let's capability-operation receiver, MI-3), and a name two bindings type differently
is refused rather than ordered against the use. The outer ring, whose reduced import set has no
capability imports, was already refused upstream (R009, SHP-2b); the arms refuse it again.

The two review follow-ups from SHP-5a landed first: `rf_index_guarded` poisons exactly RF-M3's
shape (an `if` within the loop whose condition compares the loop variable with an integer
literal, with the loop's range fact and the array's declared size known), sharing one
innermost-loop lookup with `rf_index_elided`, and the dead `tt_lookup` is gone from the taint
shadow. The follow-ups alone changed no verdict. The seed succeeded in one stage at each step.
Measured on the new seed:

| Corpus | Accepted | Identical | Poison | Refused | Trap | Diverge | Expanded |
|---|---|---|---|---|---|---|---|
| **F** | 221 | 53 | 12 | 156 | 0 | 0 | 89 |
| **T** | 183 | 180 | 0 | 3 | 0 | 0 | 0 |
| **X** | 720 | 358 | 126 | 236 | 0 | 0 | 84 |

Against SHP-5a's table: F Identical rises from 49 to 53 (the four Rust-frontend declassify
fixtures); T from 179 to 180 (the `restrict_deadline` demo; the two tools still refused are the
actor and slot demos, SHP-5c and SHP-9); X from 340 to 358 (three programs the corpus gained
since, and fifteen the slice turned Identical: the two declassify programs, the cap borrow, nine
restricts, two splits and one draw). A per-program comparison against the previous seed shows no
program losing its verdict. `SHP_IDENTICAL_KINDS` pins the 23 kinds at least one Identical
program carries, the 18 before the slice plus `SecurityRelease`, `Borrow`, `CapRestrict`,
`CapSplit` and `CapDraw`; the kinds no Identical program carries are the actor, slot, region,
grant and `mint` statements, `CallIndirect`, `OptionTry` and `ResultTry`, `StrBytesEq` and
`SignExtendI32` (SHP-4, SHP-5c, SHP-7, SHP-9). `SHP5B_FENCES` pins ten Identical rows (a
declassify into a let, a constant-time declassify chained into a declassify, a borrowed cap
passed to a call, a restrict to the second authority, a restrict_deadline on a parametric cap
with two authorities, a split of a parameter amount, a draw of a literal passed to a call, a
restrict chained through an unannotated let, and, on a 32-authority cap type, a restrict to its
last authority and a restrict_deadline, whose masks have bit 31 set and encode as negative
4-byte constants) and three Refused (a borrow of an array as a slice,
a borrow of a slice range, and a restrict on a name two cap types share). The certified source
is 1,044,168 CSIR nodes (1,025,810 at SHP-5a), under the 2,000,000-node ceiling. The ergonomics
ratchet's `exact_empty_else` ceiling lowers from 2050 to 2045.

**SHP-5c-1 as built: the taint shadow's capability quantities and intraprocedural heap floors.**
Before this slice the shadow read a `split` or `draw` as a `@Public` value without looking at its
amount, and production's heap floors were Rust-only: where only a floor produced a code the
shadow was clean (the lag `sh_taint_heap_lag_is_subset_safe` pinned). The shadow now reads the
amount (`@SecretCT` is T027, any other non-public label T001) and carries the floors production
raises and applies within one function: the raw-load and typed-read pair, one per function,
monotone and path-insensitive like the region map, carried and converged on by the loop
fixpoints; raised by an extern call or a callee whose effect row names FFI (S1), by a
heap-resident value at a non-public label — a parameter at entry, any materialisation thereafter
(S2) — by a raw store at the join of its operands and the pc (S4, S6) and by a projected-place
write and its index taint (S6, S7); joined into every raw load and every typed read — an
element, field or slice projection, a `?`, an intrinsic (a call or a method the type checker
lowers to one), a heap-typed local, a `str` literal or f-string (S11). Production keys the typed
rules on types the parse tree does not carry, so the shadow recovers a type descriptor per
binding and expression from syntax — annotations, record and enum declarations, impl methods,
the stdlib's declared signatures — and refuses rather than guesses what it cannot classify
wherever a non-public label would make a floor rule read it (a type alias, refused outright; a
generic record's field; a call to a function the program does not declare; an expression over
a borrowed operand). At `@Public` the typing is inert, so the all-public self-compile is neither
typed nor refused.

Measured against the oracle with the composed shadow tool over every F and T file and every
embedded X program (the SHP-5a harness): 301 F/T files and 716 X programs give the oracle's
exact code set; 108 F/T files and 231 X programs are refused; six X programs lag — the five S5
call-summary shapes and the one generic `@SecretCT` callee — and no program receives a code the
oracle does not, except the six `@Flow` programs whose callers were already given a spurious
code beside the refusal before SHP-5a. The hand-written fixture set gains an exact-set reject and
a clean twin per rule (the two quantity codes; S1 through an extern, a callee's row and an impl
method's row; S2 at entry and at a materialisation; S4 through an element, a method intrinsic
and a heap-typed local; S6; S7; S11); the S2 case leaves the lag pin and an S8 case joins its S5
case there; the refusal canary gains a type alias and a generic record's field read at a secret
label.

Gate: zero divergences; F 53, T 180, X 358 Identical, unchanged — the floors fire only where
production rejects. A per-program comparison against the previous seed shows four X programs
moving from Poison to Refused at the taint stage (three type-alias programs, and one `&&`
expression the self-hosted parser reads as a borrow — SHP-4 — which the typing refuses at its
`@SecretCT` label) and none losing Identical. The certified source is 1,084,628 CSIR nodes
(1,044,168 at SHP-5b), under the 2,000,000-node ceiling. The ergonomics ratchet's
`exact_empty_else` ceiling lowers from 2045 to 2041.

**SHP-5c-2 as built: the taint shadow's call-site summaries.** Before this slice the call-site
summaries were the one heap-floor rule production applied and the shadow did not: a callee's
writes raised no floor and tainted no region at its call site, and a callee's reads brought no
floor into its result (the lag `sh_taint_heap_lag_is_subset_safe` pinned, now retired). The
shadow now computes production's summary for every fn and impl-method row of its table — a
syntactic scan of the body for what a call to it can have written at an existing address, built
into fresh cells, read raw or typed, the bound on the labels it mints (every annotation,
`@Internal` if it calls the host) and the parameter slots a raw write can go through (its
rooted-slot map a fixpoint, as production's), closed over the call graph within production's
bound — and applies it at the site as production does: the floors the callee reads join the
result (S8), the caller's floors rise by what the callee writes at the site's taint joined with
the callee's bound (S5), and every argument the callee writes through has its region tainted
(S5, region side). A lowered method call resolves to its row — a user type's or the stdlib's
impl method, an associated function, a module's function, the `str` and int methods the type
checker routes to stdlib functions, and, in the gate's expanded text, the instance the
monomorph expander pre-resolved — with each argument, the receiver first, checked against its
declared label; a `@Flow` parameter accepts every label but `@SecretCT`, and a `@Flow` return
is the call's label (the six `@Flow` programs the SHP-5c-1 sweep counted as false codes now
refuse cleanly). The stdlib's element intrinsics are a raw read and a raw write wherever a
program names them. Two facts of the scan are three-valued, typed by SHP-5c-1's descriptors
(a type parameter reads as unknown at the leaf, so a generic body's field reads still type
through the record rows), and a row is reliable only when every callee it reaches is one the
shadow names: a site whose callee the shadow cannot name (a call through a local, a `grant` of
a closure held in a local), a site that consults an unreliable row, and an unknown fact that
would decide a floor all refuse — production takes its program-wide bound there, which the
shadow does not reproduce. The pass runs only when a label (an effect operation's parameter
label included, kept by the self-hosted parser as a flag on the declaration — corrected in
place: the third review's follow-up drops the flag, and the walk reads the operation's own
parameter nodes), a flow
signature, an extern, an FFI row or a `declassify_ct` can make a value non-public; the
all-public self-compile pays one tree walk and skips it. The slice also found the self-compile at 95% of the runtime's wasm-instruction
backstop (9.53 G of the 10 G default at SHP-5c-1, measured 2026-10-07), where any growth of
the certified source traps as a hostile loop would: the SELF-4 budget seam gains its fuel
side (`execute_ephemeral_with_budgets`, a per-call wasm-instruction budget under a 100 G
ceiling, rejected loudly above it), the self-compile runs under 40 G of its own
(`SELF_WASM_FUEL`, about four times its measured need), and the default backstop stays what it is
for every other tool.

Measured against the oracle with the composed shadow tool, on the fixture text as the
differential sees it: 301 F/T files and 722 X programs give the
oracle's exact code set, 108 and 236 are refused, one X
program lags (the generic `@SecretCT` callee, whose instance the shadow does not check outside
the gate) and no program receives a code the oracle does not — the five S5 shapes and the
element-store program moved to exact, the six `@Flow` false codes to refusals. On the
ambient-expanded text the gate hands the seed, with the monomorph expander before the
shadow: 349 F/T files and 759 X programs exact,
108 and 250 refused, the same generic lag, and one false
code on a program production rejects — a generic `@SecretCT` branch whose instance clone the
shadow checks where production's instance carries no label (the SHP-4 generic surface, not
this slice's). The hand-written fixture set gains an exact-set reject and a clean twin per
rule (S5 through the caller's buffer, by parameter slot, through an alias and a callee of the
callee, by a materialising callee, by the counted "mentions a secret" cost, through an impl
method's `self`; S8 raw and typed), the lag pin retires, and the refusal canary gains a
stdlib callee with no body in view and an int `to_string` beside a secret.

Gate: zero divergences; F 53, T 180, X 358 Identical,
unchanged; a per-program comparison against the previous seed shows no row changing. The certified source is 1,140,435 CSIR nodes (1,084,628
at SHP-5c-1), under the 2,000,000-node ceiling. The ergonomics ratchet's `exact_empty_else` ceiling stays at 2041 (measured).

Third review (the effect-operation signature). The self-hosted parser skipped each effect
operation's signature token by token to its `;`, so it accepted what production's
`parse_effect_op` refuses — an unknown annotation (`x: i64 @Bogus`, P021 in production, an
`OK:` module from the self-hosted chain), `@Flow` on an operation's parameter, `@ReadOnly @Mut`
on one parameter, a dangling `@in q`, a missing `(`, junk before the `;` — while the same
`@Bogus` on an `fn` item's parameter was refused, because `parser_params` bails on an unknown
annotation. A first fix read the signature with a non-allocating scan that skipped only the
types, under a stated fail-open bound; review found the bound false (an effect row after a
non-`Fn` return type and operator junk after a well-formed type passed) and two fail-closed
divergences beside it (a grouped `(Region)` and a deadline-bearing `Region(5)` are `@in`
targets in production, which unwraps the group and never reads the deadline). The scan is
gone: each operation is now a node of its own (`K_EFFECT_OP`, projected like a trait method
signature — text the operation name, children its parameters and return type, span `fn`..`;`),
so the self-hosted parser reads it with `parser_params` and `parser_type`, ET-P4 holds by
construction, and there is no bound to state. The declaration's text is the bare name again
(the operation names rode it joined `;` before, which the self-hosted effect checker registered
whole — an op-bearing effect's name could never match a row); its flag keeps the last-label
semantics, now read off the parameters' K_PARAM codes. Production's braced declaration ends its
span at `}` (the marker form stays byte-identical), so the operations nest inside it (ET-P6).
The annotation classifier (`parser_annots`) hands labels to `parser_taint` — one table — and
`parser_params` takes production's per-list `allow_flow`: `@Flow` on an `fn` item's parameter
only, refused on a closure's, a trait signature's, an extern fn's, an actor member's and an
effect operation's (the self-hosted parser admitted it on every list before, deferring to the
taint stage). The parser differential pins the refusals, the shapes the review found included:
at production's first-error token on seventeen of them, and by presence on the ten whose first
position legitimately differs (`@Flow` where it is not admitted, a dangling `@in`, a malformed
type). It pins the accepts as exact cases: every type shape an operation can carry, a `Fn`
return type keeping its row, an operation without a return type, `(Region)` and `Region(5)` on
both an operation and an `fn` item. The effect-check differential pins the registration: a
callee's row naming an operation-bearing effect its caller lacks is refused on both sides (the
self-hosted chain accepted it before), and its accept twin is clean. The certified source grows
by 3,727 bytes; seed succession in one stage, oracle-agreed (582,571 bytes). The ergonomics
ratchet's `exact_empty_else` ceiling falls to 2025 (measured).

Third review, follow-up (the member parameter lists and the label table). The third review
found a duplicate parameter on an effect operation or a trait method signature refused by
production's name resolution (N005, the `Item::EffectDecl` and `Item::TraitDef` arms of
`resolve_module_items` through `check_duplicate_params`) and accepted by the self-hosted chain,
`OK:` with a module: the self-hosted resolver checked an `fn` item's list and an actor's only.
The same held for an impl method, production's `Item::ImplDef` arm, which sits outside the name
guard because an impl block has no name; production wired all three in nxrobins/sigil-dev#712
and the mirror never followed. Each member's list is now checked on its own
(`nr_check_member_params`): an effect's operations and a trait's method signatures on the first
declaration of a name (production's N002 `continue` skips the rest of a duplicate), every impl
block's methods. The name-resolution differential pins thirteen rejects, each failing against
the previous resolver (one `N005` short of the oracle, or more), and thirteen accept twins; the
composed compiler's whole answer is pinned on one shape of each (`REJECT:nr:N005;`) and
byte-identical on its twin. Writing `parser_taint`'s comment found the label table taking
`@Flow` at every position, where production admits it on an `fn` item's parameters and return
only: a `let`, a `declassify` target and an extern fn's return carrying it compiled to a module
(measured on one program each), because the taint stage's `@Flow` refusal covers the signature
of a non-generic top-level `fn` only. The table now takes production's `allow_flow`
(`parse_taint_annotation_inner`), so the three refuse, as production's P021 does; the parser
differential pins them by presence (this side bails on the `@`, production reports the `Flow`
token), each beside its corpus twin, and an `fn` item's `@Flow` parameter and return as an exact
accept. The effect declaration's label flag
is gone: an operation parameter's label is its own K_PARAM code, which the taint shadow's signal
walk reads like any parameter's; the parser differential pins those codes by value, and the
taint differential's program-bound pin (an effect operation's `@Secret` parameter as the only
label) fails on a mutant walk that skips effect declarations. Found and not fixed here: `@Flow`
on an impl method or a generic fn, which production's type check refuses (P021,
`validate_flow_polymorphism_scope`), compiles to a module on the self-hosted chain (measured on an
impl method), because the self-hosted type check does not mirror that rule. The certified source
grows by 2,198 bytes; seed succession in one stage, oracle-agreed (582,624 bytes), and the
ergonomics ratchet's `exact_empty_else` count falls by two. Merged with SHP-5c-3 before landing:
a merge succession from main's seed (621,975 bytes) in one stage, oracle-agreed (622,028 bytes),
and the ergonomics ceiling falls from 2020 to 2018 (measured).

**SHP-5c-3 as built: slots and regions end to end.** Before this slice a slot or region
program stopped at the type checker: `slot_new::<C>()` is an explicit instantiation the
self-hosted parser did not read, `Slot<C>` and `Region` were types the checker did not name, and
a `region` statement a kind it did not type; every such program refused, so nothing reached the
emitter's slot and region arms. The parser now reads a turbofish on a single-segment call path
(the type arguments lead the call's children, counted in its flags, and every consumer skips
them; a turbofish on a multi-segment path, on a constructor or without a call bails). The type
checker types the three slot intrinsics as production does — `slot_new::<C>()` takes exactly one
type argument naming a declared capability type, plain or parametric (T192 without one, T191 for
anything else, T074 for an argument); `slot_put(s, c)` and `slot_take(s)` their arity (T074) and
operands (T075 for a non-slot where a slot is due or a non-capability or another capability where
the slot's is due; T195 for the slot's capability at another parametric arity or a shorter
deadline, production's covariance) — and `Slot` as a reserved type name (T193); a slot or
capability place is linear, never reassigned (T043); a `region name(limit) { body }` statement
takes a machine-integer limit (T111), no control flow in its body (T068), and a body whose
mutable set starts empty, so an assignment to a bare name there is T042 unless a `let mut` inside
the body bound it (production's `region_mutables`; rebinding elsewhere stays unmirrored, as
before); the handle is a `Region` value no integer place accepts (T041); `@in r` naming a
parameter that is not a `Region` is P024, production's parser diagnostic, reported at the checker
since the self-hosted parser carries none. Each code joins the pipeline's enforced set, pinned by
a parity fixture against production's exact answer; an explicit instantiation of anything but
`slot_new`, a region used as a value, a tuple let inside a region body and a `Slot<C>` annotation
whose value is not that slot (production's T046, which the pipeline drops by name) refuse with
the checker's own marker, `SH_TC_UNSUPPORTED`, kept by the allowlist. The ownership and
capability shadows carry a slot binding — a `Slot<C>` parameter or let, a `slot_new` result, a
copy through an unannotated let — as a non-linear pointer with no authority of its own: a put
consumes its capability, a take binds the slot's capability at the full mask (production's static
trace ends at the take), a slot handed to a sink is no obligation. The taint shadow treats the
intrinsics as the oracle does (a put and a take are the checked write a slot is, a new slot is
inert, the value the join of the operands) and a region statement as a block of its function at
the same pc, a `@SecretCT` limit T029 and the handle a public scalar; the body's environment is
a copy of the enclosing one, so a write through an outer binding carries its label out and an
outer name cannot be rebound. Production's escape lattice (T254) is not mirrored: in its place
the scalar-only rule admits a body whose every let binds a scalar and whose every expression
constructs no heap value and hands no non-scalar to a call, and refuses every other body, so no
region program reads clean where the lattice rejects it. The emitter reproduces production's
`SlotNew`, `SlotPut` and `SlotTake` (an eight-byte cell from the ring's allocator, the tag and
capability words, the trap on a full or an empty cell) and `RegionBegin`/`RegionEnd` (the bump
pointer saved, the body inlined into the enclosing block, the trap when the net allocation
exceeds the limit, the rewind), with a region handle used as a value materialised as
production's inert `0`; it refuses a body ending in an expression statement (its value is the
region's, a routing this slice does not mirror) and a limit that is not an integer local
([sh-wasm.md](sh-wasm.md), "Rules from SHP-5c-3"). Grants stay refused: a `grant` of a closure
poisons at the emitter (SHP-7).

Measured against the oracle with the composed shadow tool, on the fixture text as the
differential sees it: 303 F/T files and 734 X programs give the oracle's exact code set, 106
and 224 are refused, the same generic `@SecretCT` program lags and no program receives a code
the oracle does not (SHP-5c-2: 301 and 722 exact, 108 and 236 refused). On the
ambient-expanded text the gate hands the seed, with the monomorph expander before the shadow:
351 F/T files and 771 X programs exact, 106 and 238 refused, the same lag and the same one
false code on a program production rejects (SHP-5c-2: 349 and 759 exact, 108 and 250 refused).
The hand-written fixture set gains 18 exact-answer rejects and 13 byte-identical accepts
over the slot intrinsics and region statements (`SHP5C3_CORPUS`), the type-check differential's
slot and region records, a reject and a clean twin per taint rule (a downgrade inside a region
body; a secret written through an outer record inside the body and read after it; a scalar
body, the handle handed to a `Region` parameter, a body-local `let mut` rebound, a public write
through an outer record, a slot round trip beside a secret) and four refusal canaries (a body
binding a record, a str or a slot; a str handed to a call), and the ownership and capability
differentials their slot rows.

Gate: zero divergences; F 54, T 180, X 365 Identical (53, 180 and 358 at SHP-5c-2): eight
programs refused at the type check are now byte-identical — the two-ring region proof gap
fixture in F and, in X, the four slot programs of the first wall, the parametric and the
two-parameter capability slots of the second and third walls, and the runtime slot program — and
two programs holding a user turbofish, which the emitter poisoned, now refuse at the type check.
The AIR statement kinds Identical programs carry grow from 23 to 28 (`RegionBegin`,
`RegionEnd`, `SlotNew`, `SlotPut`, `SlotTake`); `SHP5C3_FENCES` pins thirteen Identical and
five Refused programs by name. The certified source is 1,208,020 CSIR nodes (1,140,435 at
SHP-5c-2), under the 2,000,000-node ceiling, and the self-compile consumes 11.5 G wasm
instructions of its 40 G budget (10.4 G at SHP-5c-2). The ergonomics ratchet's
`exact_empty_else` ceiling falls from 2041 to 2038 (measured).

**SHP-5c-3 review: capability, slot and region values at their boundaries.** An adversarial probe
of the slice (120 programs, each compiled by both compilers) found programs production rejects
that the reviewed compiler emitted a module for, nine of them refused before the slice: a
capability, slot or region value crossing a call into a parameter of another kind, cap type or
deadline (production's T071, which the composed pipeline drops by name, so nothing stood in its
place), a capability or slot under an annotation of another type, a capability returned where
another is declared, a `Region` return type (T253/T254), and a capability carried by a record
field, an enum payload or an array literal (T183, T184, T186), the slot ones newly lowerable once
`Slot<C>` was a pointer, and a `restrict_deadline` production rejects (T200: on a non-parametric
or a multi-parameter cap, or past the cap's own deadline), which the compiler before the slice
already emitted a module for. The type checker now applies production's `type_compatible` to every
capability, slot or region value at a call argument, an annotated let and a return: the same kind,
the same cap type, and — covariant at an argument and a return, invariant under a `Slot<C>`
annotation, as production's checks are — every deadline at least the declared one. A value it
names is a cap-bound or slot-bound local, a `slot_new` or `slot_take`, a `restrict`, `split` or
`draw` of a named cap (an unannotated let of one binds its receiver's cap), a `restrict_deadline`
of a named single-parameter cap (that cap at the narrowed deadline), or, where a capability, slot
or region is due, a plain call of a function declared to return one; anything else is unknown
there and refused. A mismatch is production's code where it is exact (T041 for another cap type
under an annotation, T049 for one returned, T195 for a shorter deadline at an argument, an
annotation or a return) and the refusal marker otherwise; a slot intrinsic whose own checks
already rejected it adds nothing beside its code. Capability-carrying aggregates are T183, T184
and T186 and a `restrict_deadline` that cannot narrow its named cap is T200, each exact and
enforced by the pipeline. The capability shadow had the matching gap on the authority side: a
`restrict` handed straight to a call or a return obligated nothing, so a narrowed capability
reached a full-authority sink with no C003. A capability operation or a `slot_take` at a sink now
obligates as its let-bound twin does, and the slot intrinsics' operands — no sink in production —
obligate nothing, which also retires a false C003 on a restricted capability put into a slot.
Pinned by `SHP5C3_FLOW_CORPUS` (62 rows: 24 of production's exact code — 8 capability-carrying
aggregates, 6 T200s, and the T041, T049, T195 and C003 flows — 20 refusals beside the oracle's
exact answer, and 18 byte-identical accepts of the admitted neighbours), five capability-workload
rows checked against the oracle's own workload, and the T029 region-limit taint row the slice's
text already claimed. The SHP-5c-2 third review, merged in, makes the self-hosted parser refuse a
dangling `@in` itself (`parser_region_dangling`), so the checker's P024 is now a backstop the
composed chain does not reach: such a program refuses at name resolution with the parser bail's
cascade. Re-measured with it merged in: zero divergences; F 54, T 180 and X 365 Identical,
unchanged, and a per-program comparison with the slice's own measurement moves no row. The
certified source is 1,237,552 CSIR nodes, the self-compile consumes 11.8 G wasm instructions of
its 40 G budget, and the ergonomics ratchet's `exact_empty_else` ceiling is 2020 (measured).

## 4. Invariants every slice keeps

- **The fixed point and the seed lineage.** Every `selfhost/` change that alters emission takes a
  seed succession (the `seed_regenerate` ritual). If the second stage of a succession disagrees
  with the oracle, that is a trusting-trust alarm: stop and report, never commit.
- **The self-hosted compiler compiles itself.** New code in `selfhost/` uses only forms the
  self-hosted compiler already reproduces exactly, and only forms the interpreter executes
  (`interp/census.py` inventories the certified surface); the interpreter's digest pins and the
  DDC lane move in the same PR.
- **The ergonomics ratchet.** `tools/selfhost_ergonomics_census.py --ratchet` gates CI; no counted
  pattern may grow.
- **The single-ring protocol is frozen.** `OK:{hex}`, `OK:!!` and `REJECT:{stage}:{codes}` keep
  their meaning. The two-ring form SHP-2 adds is a strict superset and leaves single-ring answers
  unchanged.
- **Fail closed.** A construct the self-hosted compiler cannot reproduce exactly poisons. It never
  approximates.

## 5. Exclusions

Out of the mirror's scope by design:

- host-profile custom sections;
- `runtime_module` and `meta`;
- programs that need the `solver` feature;
- multi-file projects: no corpus holds one. SHP-3 hands the seed an expanded program's files in
  production's order and proves that text is the program production compiled; a project's files
  would travel the same way, but no project is measured;
- diagnostic wording: the gate compares modules and refusals, not messages;
- per-file compiles of `selfhost/`: the certified composition is the supported input;
- production's region escape lattice (T254): the taint shadow admits a region body by the
  scalar-only rule and refuses every other, so a body that builds a heap value — a record, a str,
  an array, a slot — refuses where production accepts it (`SHP5C3_FENCES`:
  `region_body_binding_a_record`, `region_body_binding_a_str`, `slot_inside_a_region`);
- a region used as a value (a let's initializer, an argument) and a region body ending in an
  expression statement: refused at the type checker and the emitter;
- an explicit instantiation of a user generic (`id::<i64>(1)`): the type checker infers from the
  value arguments and refuses the written ones (`slot_new` is its one turbofish) until SHP-4;
- grants: a `grant` of a closure poisons at the emitter until SHP-7;
- a capability, slot or region value the type checker cannot name — a `mint`, an impl method's
  result — under a capability, slot or region annotation, as such an argument, or returned from a
  capability-returning function, and any such value handed to a generic parameter: refused, where
  production may accept (the SHP-5c-3 review);
- a capability argument to an impl method: production's method-call check covers machine-int
  and function-typed parameters only, so it accepts a capability of another cap type there; the
  mirror reproduces that byte for byte, and the gap is production's to close.

Refused while production miscompiles them: no shape today. A shape production miscompiles joins
this list, and leaves it when production's fix lands and the seed mirrors it.

An `i32` index to `byte_at`, which production bounds-checked with a signed compare, left this
list with SR-030: production's fix landed, and the seed mirrors it (§3, the signed-index mirror).
A `ct_*` operand narrower than 8 bytes, for which production emitted a module that does not
validate, left it when production began rejecting that operand at typecheck, so no program
production accepts holds one (§3, the narrow `ct_*` operands). Two more left it with SR-032: an
`[i32; N]` literal nested in a tuple element or an enum payload, which production laid out at an
8-byte stride, and a literal enum payload argument narrower than `i64`, which production stored
as 8 bytes. Production now types each part of a construct by the slot it is written to, and the
seed mirrors it wherever it can see the slot (§3, the construct-slot mirror). Where it cannot, as
for an array literal in an enum payload, it refuses, as at any slot whose type it cannot see
([sh-wasm.md](sh-wasm.md)).

## 6. Open questions

- **X labels.** File plus content hash survives edits elsewhere in the file, and a pin keeps its
  label when a copy of its program appears in another file. An edit to the program itself
  re-labels it, and so does removing it from the pinned file while another file still holds it;
  the gate reports the second case as a moved pin rather than a new divergence. Whether a
  relabelled divergence should need review, or only a new one, is open; today both fail the gate.
- **Floors after SHP-10.** Once Identical equals accepted minus exclusions, the floors could become
  exact counts. Whether that is worth the churn on every new program is open.

## 7. Fence debt

Production changes fenced under the keep-up policy instead of mirrored. Each row names the
construct, the PR that fenced it, and the floor it lowered.

| Construct | Fenced in | Floor lowered |
|---|---|---|
| (none) | | |
