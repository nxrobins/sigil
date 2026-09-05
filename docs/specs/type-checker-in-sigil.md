# The SIGIL Type-Checker, in SIGIL — Implemented (monomorphic core)

**Status:** **Implemented (Epic-1 monomorphic core)** — shipped 2026-06-14 across PRs #268–#300
(PR-0…PR-5h). `selfhost/typecheck.sigil` is a type-checker WRITTEN IN SIGIL that, inlined with
`selfhost/{lexer,parser}.sigil` into one wasm tool, assigns the same resolved per-node type stream
AND rejects ill-typed monomorphic programs with the same integer T-codes as the Rust oracle —
verified by `crates/sigil-runtime/tests/typecheck_differential.rs` (55 tests). The done-line gate
(PR-5h) crystallizes the MIN_COVERED floor: **all 17 core T-codes** (T041/T044/T045/T046/T049/T050/
T051/T054/T055/T060/T062/T070/T071/T087/T088/T120/T190) + **all 12 core `Type` tags**
(`{0,1,2,3,4,5,6,7,9,12,14,19}`) covered at exact parity, plus the ET-T1/T3/T4/T5/T6 gates green
(real-`.sigil`-fixture admission, reject-for-the-right-reason round-trip, no-IntLit/no-Error
property, block-scope resolution parity, determinism + the total `Type→tag` drift-lock). The 3-step
Adversarial-Compiler ritual (2026-06-13) products live in §9 Constraints & Fallbacks and §10
Explicit Anti-Goals. **Follow-on epics since SHIPPED on top of the core: Traits (#304/#305) and
Generics (#306–#312, PR-G0…PR-G4) — see §11/§12; the differential is now at 95 tests.** Deferred to
later epics (each its own design + ritual): refinement obligations, caps/effects/regions, the
Option-B monomorphizer-in-SIGIL; and within the core — composite-VALUE checking (T-codes against
composite literals/returns), composite call-return typing, slice expressions `&a[i..j]`, tuple `.0`
access, and un-annotated composite lets.
**Date:** 2026-06-13 (design) · 2026-06-14 (implemented)
**Authors:** Nigel Robinson
**Scope decision (LOCKED):** **staged ladder — the monomorphic core first.** Epic 1 type-checks
the monomorphic subset (scalars, non-generic records/enums, functions, control flow, basic
inference) identically to the Rust oracle, on a DEDICATED corpus drawn from the existing Rust
type-check fixtures (ET-T1). Generics + monomorphization, traits, refinement-obligation
emission, and caps/effects/regions are EXPLICIT follow-on epics, each with its own design +
ritual.
**Differential decision (RESOLVED by the ritual):** "identical to the oracle" means **Option A —
a resolved-type table + exact T-code parity** (§6). ET-T4 is satisfiable with A and structurally
impossible for B on a generics-free core; AG-T4 hands the full-monomorphized-tree comparison to
the generics epic.

---

## 1. Context & Goal

The self-hosting critical path is `lexer → parser → type-check → … → bootstrap`. The lexer
(#232–#241) and parser (#242–#254) shipped: `selfhost/lexer.sigil` + `selfhost/parser.sigil`
together turn source text into an `Arena<PNode>` AST, proven node-for-node against the Rust
`lex_with_id` / `parse_with_id` oracles. The **type-checker is the next stage**, consuming that
`Arena<PNode>`.

> **Goal (Epic 1).** A SIGIL function `typecheck(nodes: Arena<PNode>) -> (types, diagnostics)`
> that, on every program in a dedicated MONOMORPHIC corpus, assigns the same resolved types and
> emits the same diagnostics as the Rust oracle (`type_check::check_with_options`,
> `crates/sigil-compiler/src/type_check/mod.rs:812`). The Rust type-checker is the differential
> **oracle** — the exact executable definition of "correct."

Like the lexer and parser, this is a dogfood (can SIGIL express a real semantic-analysis stage?)
and a forcing function (it surfaces the next real language gaps). It does **not** replace the
Rust type-checker in the pipeline yet.

**Why the monomorphic core first.** The Rust oracle is ~17 K LOC (`expressions.rs` alone is
5.4 K), 138 T-codes, 24 `Type` variants, with deeply entangled subsystems — generic
monomorphization spread across five files, trait dispatch, effect/region/borrow tracking,
refinement-obligation emission. A faithful whole-stdlib port is a 10 K+-SIGIL-line, multi-epic
undertaking. The monomorphic core is the tractable, value-shipping first slice: it proves the
mechanism (typed differential, type representation, the resolve↔type-check boundary) against a
real-but-bounded surface, and each hard subsystem (generics, traits, refinements, caps) becomes
its own laddered epic afterward.

## 2. The oracle

- **Entry:** `check_with_options(&ResolvedProgram, &CompileOptions) -> Result<(TypedProgram,
  AuthorityRegistry), Vec<Diagnostic>>` (`type_check/mod.rs:812`), over
  `check_collecting` (:210, exposes the partial `TypedProgram` even on error — the differential
  driver, as `check_collecting` was for the refinement oracle).
- **Output — `TypedProgram`** (`typed_ast.rs`): `Vec<TypedModule>` of `TypedFunction`s, each
  carrying resolved param/return `Type`s, an `EffectSet`, a taint label, and a `TypedBlock` of
  `TypedStmt`/`TypedExpr` where **every expression node carries its resolved `Type`**. Records
  and enums resolve to `BTreeMap` tables. NOTE: the oracle's `TypedProgram` ALSO contains
  **monomorphized** generic instances — the typed tree is generic-EXPANDED, so it has more nodes
  than the parse tree. This is the crux of the differential decision (§6); the monomorphic core
  sidesteps it (no generics → no expansion) but the design must not bake in an assumption the
  generics epic can't keep.
- **The `Type` enum** (`type_check/types.rs:37`, 24 variants): `Unit, Bool, I32, U32, I64, U64,
  F64, Str, Generic(name), Named(name, args), Cap(name, deadlines), ActorRef(name),
  Array{elem,size}, Fn(params,ret,linear), Ref(inner,mut), Slice(inner), Ptr, MutPtr, Region,
  Tuple(elems), IntLit(i64), Error`. **The monomorphic core covers:** Unit, Bool, the four
  machine ints, F64, Str, non-generic `Named`, Array, Tuple, Ref, IntLit (the PIL
  polymorphic-int-literal), Error. **Deferred to later epics:** `Generic`, generic `Named`,
  `Cap`, `ActorRef`, `Fn`-as-value, `Slice`, `Ptr`/`MutPtr`, `Region`.
- **T-codes:** 138 total. The monomorphic core hits a SUBSET — declarations/assignments
  (T040–T049), control-flow conditions + operators (T050–T055), undefined names (T060–T069),
  arity (T070–T075), patterns/exhaustiveness (T080–T089, T190), and the basic type-mismatch
  paths. The generic (T150–T161, T227–T236), trait (T244–T250), refinement (T210–T226), cap
  (T100–T120, T180–T201), region/mutation (T251–T261) codes belong to the follow-on epics.
- **Input boundary (RITUAL CANDIDATE):** the oracle consumes `ResolvedProgram` (post
  name-resolution). There is no name-resolver-in-SIGIL yet. The realistic Epic-1 stage is
  therefore **"resolve + type-check together"** — the SIGIL type-checker does its own minimal
  name resolution over the `Arena<PNode>` (lexical local scopes; a top-level signature pre-pass
  for functions/records/enums). Whether that boundary holds, or name-resolution should be its
  own prior SIGIL stage, is for the ritual.

## 3. SIGIL representation

Mirrors the parser's proven shapes:

- **Input:** the parser's `Arena<PNode>` + its shared child-id `Vec` (the exact output of
  `selfhost/parser.sigil`). The type-checker walks it by `(child_start, child_count)` slices.
- **A SIGIL `Type`** — a flat tagged record `record TNode { tag: i64, a: i64, b: i64, name: i64 }`
  in a `Arena<TNode>` (the type-table), where `tag` is the `Type` discriminant, scalar slots
  carry array size / mutability / IntLit value, child slots are `TNode` back-references (for
  `Array.elem`, `Tuple.elems`, `Ref.inner`), and `name` indexes a string pool (for `Named`).
  This is the `Arena<PNode>` pattern applied to types — `Arena<T>` (`stdlib/sigil/arena.sigil`)
  is the proven backing.
- **A SIGIL symbol table** — scoped local bindings (name → `TNode` id) + the top-level
  signature tables (fn sigs, record/enum defs). Hand-written SIGIL has no generic `Map`, so the
  binding store is an explicitly-typed structure (a `Vec` of frames, each a `Vec<(name, tnode)>`,
  or a `BoundedMap`-style monomorphized table — a PR-0 forcing-function decision).
- **Namespace:** all symbols `tc_`/`TC_`-prefixed, disjoint from `lexer_`/`parser_` (the three
  inline into one differential tool; a collision is a compile error).

## 4. The differential harness

Mirrors `crates/sigil-runtime/tests/parser_differential.rs`:

- **Inline composition:** `lexer.sigil` + `parser.sigil` + `typecheck.sigil` inlined into ONE
  tool (`lex → parse → typecheck → encode`), run across a single forge boundary, transferred via
  `as_output`.
- **The Rust oracle side:** a flattener over `check_collecting`'s `TypedProgram`, producing the
  SAME canonical encoding the SIGIL side emits — a TOTAL `Type → tag` map with **no `_` arm**
  (the ET-P9 drift-lock: a new Rust `Type` variant fails to compile until mapped), and a TOTAL
  per-T-code map for the error stream.
- **What is compared:** Option A (§6) — the resolved `Type` of each SOURCE node as an injective,
  name-bearing per-node encoding (ET-T4), plus exact T-code parity for core-owned codes (ET-T3),
  gated behind resolution parity with the oracle's `ResolvedProgram` (ET-T5).
- **Property suite (the ET analog, mirroring the parser's ET-P*):** total corpus coverage (every
  core T-code + every core `Type` tag appears ≥1×); exhaustive injective type encoding;
  determinism/purity/no-trap; bounded type-table; the `Type→tag` table total + drift-locked.

## 5. The dedicated monomorphic corpus

The stdlib uses generics/traits/refinements heavily, so it CANNOT be the Epic-1 corpus (that is
the whole-stdlib north star of a later epic). Per ET-T1, the Epic-1 corpus is the **monomorphic
slice of the existing Rust type-check fixtures** — programs the oracle already checks, authored
independently of the SIGIL checker so the corpus cannot be curated to pass it — staged under
`crates/sigil-runtime/tests/typecheck_corpus/`, exercising every core `Type` variant and every
core-owned T-code, plus a malformed corpus (each fixture mutation-guarded, ET-T3) for T-code
parity. A coverage manifest with an append-only `MIN_COVERED` floor blocks "done" until coverage
is total. "Done" for Epic 1 is: the dedicated corpus type-checks identically + the property suite
holds — explicitly NOT whole-stdlib.

## 6. The differential target — RESOLVED: Option A

The parser compared a structural tree node-for-node. Types are richer, and the oracle's typed
tree is generic-EXPANDED, so the target had two honest shapes. **The ritual resolved it to
Option A** — ET-T4 (an injective, name-bearing per-node encoding) is satisfiable with A and
structurally impossible for B on a generics-free core, and AG-T4 declares B's expanded-instance
comparison the generics epic's burden.

- **Option A — resolved-type table + T-code parity (ADOPTED).** Compare (a) the resolved `Type`
  of each SOURCE expression node (pre-monomorphization, an injective name-bearing per-node
  encoding keyed by AST span — ET-T4) against the oracle's per-node types, and (b) T-code
  diagnostics at EXACT-code parity for core-owned codes (ET-T3, sharper than the parser's
  presence+position AG-P3 because the core's T-code set is small). Proves "types are correct +
  errors match" without replicating the oracle's monomorphized node-EXPANSION. Survives into the
  generics epic (source nodes still have one resolved type each; instances are a separate table).
- **Option B — full monomorphized typed-tree node-for-node (REJECTED for the core; deferred to
  the generics epic per AG-T4).** Serialize the whole `TypedProgram` (expanded instances
  included) as a canonical node stream, compared node-for-node like the parser. Maximally strict,
  but forces the SIGIL side to replicate monomorphization's exact instance generation + ordering
  — a far larger, more brittle target, and one the monomorphic core can't even exercise (no
  generics to expand).

The ritual's Existential-Threat question — *what does a green type-differential actually
prove?* — was the lever (cf. the parser's "a green differential ⇏ a correct parser unless the
serialization is exhaustive + injective"). A green Option-A run proves correctness ONLY under
ET-T4's injective, name-bearing encoding; without it, A degrades to the tag-only fig leaf MC-6
warned of. B is not merely heavier — it is unexercisable by the monomorphic core (no generics to
expand), so adopting it would rest the core's "done" line on zero expanded instances. A it is.

## 7. Ritual candidates (inherited — dispositions after the ritual)

Per the menu plan's ET-M8b, every decision this design inherited was tagged a CANDIDATE the
3-step ritual stress-tested. Dispositions (2026-06-13):

1. **"Monomorphic core first."** The scope cut itself. **→ KEPT, sharpened by AG-T2:** the core
   excludes any type whose DEFINITION is generic (`Vec<T>`, `Option`, … even at concrete args),
   so the `Vec<i64>` transitive-generics trap is closed by definition, not hoped away.
2. **"Resolve + type-check as one SIGIL stage."** Folding name-resolution into the type-checker
   (§2). **→ KEPT, gated by ET-T5:** the SIGIL resolver's binding ids are checked against the
   oracle's `ResolvedProgram` BEFORE any type comparison, so a misresolution can never masquerade
   as a type delta; the corpus stays unambiguous-resolution until a resolver-in-SIGIL is proven.
3. **"Emit obligations, never solve."** **→ DEFERRED to the refinement epic (AG-T3):** the Epic-1
   corpus carries no `where` clauses, so the obligation/Z3 question does not arise here; it is the
   refinement epic's to settle.
4. **The differential target** (§6). **→ RESOLVED to Option A** (ET-T4; AG-T4).
5. **The PIL `IntLit` core inclusion.** **→ KEPT, bounded by ET-T2 + ET-T4:** `IntLit` is
   exercised against ≥2 target int types so a "default-to-i64" shortcut diverges, and no `IntLit`
   tag may survive in the output stream — the wedge is fenced, not avoided.

## 8. The PR ladder (Epic 1 — SHIPPED #268–#300)

All slices shipped 2026-06-14; the resolution-annotator → REJECTER pivot (PR-5a+) and the
composite-type encoding (PR-5e/5f) refined the ladder as the work surfaced detail.

- **PR-0 — the symbol-table primitive + harness skeleton.** ✅ The scoped binding store, the inline
  lexer+parser+typecheck tool, the differential on a trivial program. "Mechanics proven end-to-end."
- **PR-1.x — scalar inference + let/return.** ✅ Literals, machine ints + PIL `IntLit`, bool, str,
  `let`/annotation checking, `return` vs declared type, binary/unary ops.
- **PR-2.x — names + calls.** ✅ Local scopes, function-signature pre-pass, non-generic calls, paths.
- **PR-3.x — records + enums (monomorphic).** ✅ Construction, field access, variant payloads.
- **PR-4.x — control flow + patterns.** ✅ if/match/while, exhaustiveness, enum payload-binding patterns.
- **PR-5a/5b/5c/5d — the REJECTER pivot (the diagnostics channel + all 17 core T-codes).** ✅ A third
  `records|pool|diags` output section; the SIGIL checker now REJECTS ill-typed programs with the
  oracle's exact integer codes (5a expected-known mismatches, 5b binop/name/annotation, 5c call/field,
  5d patterns T087/T088/T044/T190 + guaranteed-return + exhaustiveness analysis).
- **PR-5e/5f — composite types (the `type_detail` encoding).** ✅ The record's 4th field became a
  recursive `mangle_type`-mirrored detail string; Ref (14) via record borrows, Tuple (19) via
  params/returns/literals, Array (12) via literals/index — all 12 core `Type` tags reachable.
- **PR-5g — block-scope resolution parity (ET-T5).** ✅ The canary probe found a real scope-leak bug
  (a nested shadow leaking past its block → spurious T049 false-reject); fixed at the root with
  `tc_scope_unwind` so SIGIL resolves names with proper block scoping — identically to the oracle.
- **PR-5h — the done-line gate.** ✅ The MIN_COVERED coverage manifest + ET-T1/T3/T4 gates. **The
  Epic-1 "done" line.**
- **PR-N — docs + roadmap flip** (this spec → Implemented; the Tier 8-10 row; memory). ✅ This PR.

Concurrently, the **corpus** epic (`crates/sigil-corpus`) extracts every SIGIL
program we author — including this `selfhost/typecheck.sigil` (auto-re-extracted each build) and the
~1,225 inline `module …;` programs in the differential harnesses — into a compiler-validated corpus.

Per-PR gate: the standard gate (`fmt` · clippy `--no-default-features -D warnings` · `cargo test
--workspace --no-default-features` · the shadow run). The differential lives in sigil-runtime
tests (no solver feature needed — the monomorphic core emits no Z3 obligations).

## 9. Constraints & Fallbacks

Products of the 3-step Adversarial-Compiler ritual (2026-06-13). Each is a dumb physical bound +
its fail-fast mode; together they govern every PR in the type-checker epic. The meta-test: the
product is a type-checker, so "corrupt" means a green differential proves nothing — the checker
agrees by memorization, accepts what the oracle rejects, or compares the wrong thing.

**ET-T1 — Corpus from an external source of truth.** The Epic-1 corpus is the monomorphic slice
of the existing Rust type-check fixtures (never hand-authored to pass the SIGIL checker), and a
coverage manifest with an append-only `MIN_COVERED` floor requires ≥1 fixture for all 12 core
`Type` tags and every core-owned T-code. *Fail-fast:* a `typecheck_corpus_coverage` test panics
listing any tag/code with 0 fixtures, and the PR-5 done-line gate stays RED until coverage is
total.

**ET-T2 — Dual inference provenance.** Every core scalar appears in ≥2 fixtures of distinct
provenance (≥1 annotated, ≥1 context-inferred), and PIL `IntLit` is exercised against ≥2 distinct
target int types (`u32` AND `i64`), so no shape-keyed lookup table can satisfy the corpus.
*Fail-fast:* a checker that defaults all literals to `i64` diverges on the `u32` fixture — the
per-node type-tag mismatch fails the differential loudly.

**ET-T3 — Fail-closed, mutation-guarded, exact T-code.** Every malformed fixture carries exactly
one `MUTATION_SITE` (deleting it type-checks clean), the compared diagnostic tuple includes the
integer T-code (exact parity for core-owned codes, not presence+position), and the count of
programs the SIGIL side accepts while the oracle rejects is 0. *Fail-fast:* a wrong code is a
tuple mismatch → fail; an accept-vs-oracle-reject is a diagnostic-set diff > 0 → fail loud; the
`MUTATION_SITE` delete-round-trip is itself a test, catching reject-for-the-wrong-reason.

**ET-T4 — Injective, name-bearing encoding; zero surviving `IntLit`.** The per-node encoded tuple
carries every distinguishing `Type` field (tag, resolved name, array size, mut bit, child tags),
is proven injective by an enumerate-all-core-constructors round-trip, the count of `IntLit` tags
in any final stream is 0, and the type-table has a `TC_NODE_CEILING` (1,000,000 TNodes).
*Fail-fast:* an encoding collision panics naming the colliding pair; a surviving `IntLit` fails
the no-IntLit assertion; table overflow emits a `TC_NODE_CEILING` rejection, never a silent
truncation or OOM.

**ET-T5 — Resolution parity gates the type comparison.** The corpus is restricted to
unambiguous-resolution programs (single module, no use-aliasing) until a name-resolver-in-SIGIL
is independently verified, and the SIGIL resolver's binding ids are compared against the oracle's
`ResolvedProgram` with a required mismatch count of 0 BEFORE any type comparison runs.
*Fail-fast:* a binding divergence fails at the resolution-parity pre-check with a "resolution
delta, not type delta" message — a type mismatch can never be silently a misresolution.

**ET-T6 — Total, acyclic, deterministic, drift-locked.** The parse-node dispatch and the
`Type→tag` map are both TOTAL with no `_` arm (a new `PNodeKind`/`Type` variant fails to compile),
the type-table is acyclic with every child id ∈ `[0, len)`, and two runs × two independent
compiles produce byte-identical streams (BTree, never Hash, iteration order everywhere).
*Fail-fast:* an unexpected node emits a `TC_UNEXPECTED_NODE` sentinel tag into the stream (never a
silent skip) and fails the differential; a cyclic/OOB child id panics `TC_TYPE_TABLE_CORRUPT`; a
determinism diff fails on any single byte; a missing arm is a compile error.

**ET-T7 — Inline-tool budget + decoupling fallback.** The merged lexer+parser+typecheck wasm tool
must compile+instantiate within a pinned per-fixture budget (`PER_FIXTURE_BUDGET_MS`, measured
from the parser two-file baseline × 1.5); exceeding it triggers the fallback of feeding the
type-checker the parser's pre-encoded node stream as data instead of inlining all three.
*Fail-fast:* the harness asserts compile+instantiate time against the budget and HARD-fails
("over budget — switch to the decoupled-input harness") rather than letting a slow tool silently
blow the CI clock.

## 10. Explicit Anti-Goals

Declared so future developers need engineer NO fallback for these:

- **AG-T1 — Whole-stdlib parity is NOT Epic 1.** The done-line is the dedicated monomorphic
  corpus, not `stdlib/sigil/*.sigil`; whole-stdlib parity is a later epic's north star.
- **AG-T2 — Generic-origin types are OUT of the core.** The core EXCLUDES any type whose
  DEFINITION is generic — `Vec<T>`, `Option`, `Result`, `Map`, `BoundedVec` — even at concrete
  args like `Vec<i64>`. "Monomorphic" means generic-FREE, not generics-at-concrete-args. This is
  the scope line, not an edge case.
- **AG-T3 — Refinement-bearing decls are OUT of the core corpus.** No `where` clauses in the
  Epic-1 corpus, so the oracle's decl-time refinement-shape validation (T217) never fires and the
  Z3-free cut is clean by construction. Refinement-obligation emission is a follow-on epic.
- **AG-T4 — The monomorphization-expansion differential is the generics epic's problem.** Epic 1
  guarantees its encoding is injective for SOURCE-node resolved types (Option A); it does NOT
  design the comparison of the oracle's expanded generic INSTANCES. That instance-table
  comparison is the generics epic's burden — a declared boundary, not a defect to pre-solve.
- **AG-T5 — Adversarial scoping depth.** v1 does NOT engineer for pathologically deep nesting or
  adversarial shadowing chains; the WASM stack + the type-table node ceiling are the only
  backstop. A source crafted to exhaust the scope stack is UNSUPPORTED.
- **AG-T6 — Layer attribution for multi-rule violations.** v1 does NOT promise WHICH core T-code
  fires when a node violates multiple rules; the corpus pins the code the implementation actually
  produces (a determinism witness, not a precedence contract).

## 11. The Arc Beyond (the laddered epics after the core)

1. **Traits — ✅ Implemented (#304/#305).** Declaration-time coherence (T248/T249/T250) +
   call-site bound satisfaction (T245/T246) via a built-in table + structural derive.
2. **Generics — ✅ Implemented (#306–#312, PR-G0…PR-G4).** Option-A call-site/construct-site
   inference parity for the in-scope kinds — generic free functions, generic records, and
   generic-impl methods — at exact T-code + record-stream parity with the oracle (95 differential
   tests). See §12.
3. **Refinement-obligation emission** — emit the obligations the Z3 discharge consumes (never
   solve); the bridge to the existing `type_check_v2` obligation model.
4. **Caps / effects / regions** — the exotica; authority shape-checking, effect inference, region
   escape.
5. **Whole-stdlib parity** — the north star: every `stdlib/sigil/*.sigil` type-checks identically.
6. **Pipeline wiring** — the Stage-0 → Stage-1 bootstrap.
7. **Monomorphization-in-SIGIL (Option-B graduation)** — reproduce the oracle's expanded instance
   stream (mangle-byte-parity, cache-dedup, drain-order). Declared OUT of the generics epic (AG-G1);
   a future graduation epic now that call-site inference is green.

## 12. Generics epic — Implemented (#306–#312)

**Decision: Option A + instance FILTERING (not Option B).** The oracle augments `module.functions`
with one monomorphized instance per concrete type (`id__i64`, `Box__get__i64`), each reusing the
generic SOURCE span. The differential FILTERS those instances (`generic_source_spans`, now covering
both generic `FnDef`s and generic-impl methods), and the SIGIL side skips any generic-source body
(a `fn`/`impl` carrying `P_K_TYPE_PARAM` children) — so both sides compare only the concrete source
slice, with the generic DIAGNOSTICS firing at the concrete call/construct site. No monomorphizer is
built in SIGIL (ET-G7).

**Mechanism.** A type-param binds from the first CONCRETE arg/field, ELSE the expected type
(let-annotation / return position), ELSE T150/T233 (ET-G3b). `TcSig.rettp`/`parmtp` carry the
return/param type-param positions; a call/construct substitutes the result and arg-expected from the
binding (`TcBind.targs`, the ";"-joined concrete codes captured from the annotation). `TC_T_GENERIC=8`
lives only in the sig/rec tables — it is NEVER emitted (`pr_g4_zero_generic_tag_full_corpus`).

**In-scope (at parity):** generic free fns (T150); generic records — field-substitution at access,
un-annotated construction inference (T233), conflicting-field rejection (T234), construct-time
field-init T071, **generic-Named-annotated-let value check** (a `let b: Box<i64> = <value>` whose
value is a different Named / scalar / enum → T041, an unknown base name → T046 — closing a
pre-existing false-ACCEPT the `tc_annot_tag`-returns-`TC_NO_EXPECT` path left open; fail-soft on an
out-of-core value); generic-impl methods — `-> T`/renamed-`-> U`/2nd-3rd-slot return substitution,
type-param method-param substitution + T071, param/local receivers, nested-generic CONSTRUCTION
(clean inner values); **generic ENUMS** (PR-G2b, #314/#316/#…) — generic-Named function/method
RETURN records (`-> Opt<i64>` → `9,Opt`, concrete-arg-gated, ET-G15), MATCH-arm payload substitution
from the scrutinee's targs (`match o { Opt::Some(x) => … }` binds `x: i64`, via `TcRec.vptp`),
enum-CONSTRUCT payload mismatch → T041 (ET-G18: T041-at-let, not T071; AG-G12 int-lit flex), and the
ambiguous-bare-variant T236 (a bare variant in ≥2 in-scope enums, annotation/qualifier-suppressed).

**The oracle method-arg quirk** (PR-G3b): the oracle checks METHOD-call args INT-LITERAL-only (it
rejects only a surviving int-literal whose i64 default mismatches the concrete/substituted param
type), UNLIKE a FREE call, which is strict. SIGIL gates its method-arg T071 on the int-literal flag.

**Done-line gate** (PR-G4): MIN_COVERED for the generic codes (T150/T233/T234/**T236** in
`CODE_MANIFEST`) + the zero-tag-8 property + the AG-G9 body-code-asymmetry corpus-admission gate (every
admitted fixture's oracle core-code span lies in a CONCRETE function, never a filtered generic body) +
the instance-filter no-op-on-monomorphic property.

**Anti-goals (engineer no fallback):** AG-G1 (Option-B instance stream), AG-G2 (turbofish), AG-G6
(nested-generic RETURN inference — fail-soft to TC_UNHANDLED; the let binds from its annotation so no
stray code cascades — AND nested-CONSTRUCTION inner-value checking: an inner construct's slots are
NOT re-substituted from the outer targs, so a mismatched inner value like `Outer<i64> = Outer { i:
Inner { x: "s" } }` is not caught — only CLEAN nested construction is at parity), AG-G9 (body-internal
generic errors — checked on neither side; corpus stays clean), AG-G12 (int-literals kept polymorphic
through generics by the oracle, frozen by SIGIL), AG-G14 (field-access / non-local-path method
receiver — receiver must be a simple bound local), AG-G15 (enum payload inference is single-type-param,
single-payload — multi-payload-binding / `None`-only / nested-recursive payloads OUT), AG-G17 (non-local
MATCH scrutinee — a call-result / field / index scrutinee carries no targs → payload fail-soft, OUT),
AG-G18 (T236 is single-module, kind-disjoint, import-blind), AG-G19 (generic-Named CALL-result /
cross-fn-boundary value-flow carries no type-args — a value-flow follow-on, fail-soft), `impl<T> Box<T>`
explicit form (parser gap), method-level `<U>`/T235 (oracle ICEs).

---

## Cross-references

- `selfhost/parser.sigil` + `crates/sigil-runtime/tests/parser_differential.rs` — the stage this
  consumes + the differential-harness template.
- `crates/sigil-compiler/src/type_check/` — the oracle (mod.rs entry, types.rs `Type` enum,
  expressions.rs/statements.rs the woven inference, universe.rs the global tables).
- `crates/sigil-compiler/src/typed_ast.rs` — the `TypedProgram` differential target.
- `stdlib/sigil/arena.sigil` — the `Arena<T>` backing for the type-table.
- `docs/specs/self-hosting-completion-ladder.md` — the current bootstrap authority.
- `docs/specs/parser-in-sigil.md` — the sibling stage (Implemented); the ET/AG/ritual pattern.
