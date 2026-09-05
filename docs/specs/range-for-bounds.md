# Range-for + loop-variable bounds elision (`for v in a..b`)

The exclusive i64 range loop, and the compile-time array-bounds story it carries:
`for v in 0..K { … arr[v] … }` with `K <= N` compiles with the runtime bounds
check **statically discharged** — the `[T; N]` size pays rent as compile-time
proof for a loop index, exactly the [true-north array corollary]: for an
unattended AI writer, push safety from *a runtime guard the model ignores* to
*a compile-time obligation the model participates in*, and resolve ties toward
**local checkability** (the bound is visible in the loop header; nothing here
ever needs whole-program reasoning).

## 1. Surface + semantics

```sigil
for v in a..b {      // exclusive end; a, b : i64, each evaluated exactly ONCE
    …                // v : i64, IMMUTABLE (assignment to v is T042)
}
```

- Both bounds are `i64` (**T280** otherwise; integer literals narrow via PIL;
  `arr.len()` on a fixed-size array is accepted directly — §3). Bounds are
  evaluated in the OUTER scope (v is not in scope in its own bounds), each
  exactly once (the AIR pre-header hoist — a body write to a bound variable
  does not change the trip count; exec-pinned).
- Empty when `a >= b`. Signed throughout (`for i in 0-2..2` iterates
  -2,-1,0,1). `break`/`continue` work; `continue` advances the counter.
- `..=` is rejected at parse (**P029**): one canonical loop form keeps the
  compile-time fact (`v < end`) *exactly* the loop condition — no off-by-one
  variant for the oracle or the SH-AIR shadow to mis-derive.
- There is NO general Range expression, type, or value — the range form exists
  only in the for-header position.
- Lowering: a direct AIR arm (init `v = a`; hoisted `__r_end = b`; header
  `v < __r_end` + the `Loop` terminator — fuel is the ordinary back-edge
  charge; increment block `v += 1`, which cannot wrap: `v < end <= i64::MAX`
  pre-increment).

## 2. The bounds fact — sound BY CONSTRUCTION, not flow tracking

The type-checker records `v ∈ [0, K)` on a dedicated channel
(`MonomorphTracker::range_loop_facts`) **iff every gate holds**:

1. the start is the surface literal `0`;
2. the end resolves Z3-free to a compile-time `K`: an integer literal, or
   `arr.len()` on a **bare local** of type `[T; N]` (§3);
3. `K >= 1` (an empty loop makes no claims);
4. the body **pre-scan** finds no rebinding of `v` through ANY binder form —
   `let`, `let (…)` tuples, match-arm bindings (enum + array patterns),
   nested loop variables. Any rebinding anywhere refuses the WHOLE loop's
   fact (no partial windows).

Why this needs no flow analysis:

- **Mutation-proof**: the loop variable is bound immutably — `v = …` is a hard
  T042, and errors abort before AIR, so no unsound stamp can ever reach
  codegen.
- **Shadow-proof**: the pre-scan is a TOTAL match over `Stmt` and `Pattern`
  (a future binder variant fails to compile there and must be classified —
  the walker-totality defense).
- **Context-proof**: closure bodies and effect-handler clause bodies are
  **barriered** — the channel is emptied (`mem::take`) around their checks.
  Both lambda-lift into *different functions* whose binders may shadow the
  name; no enclosing-loop fact is ever visible inside them, fail-closed.

The consumer (`infer_index_expr`) stamps `bounds_proven` on `arr[v]` when the
index is a **bare local** with a channel hit and the interval fits `[0, N)` —
a plain i64 compare against the array's static size (`Type::Array { size }`,
anchored by the SC-4/T227 invariant: every `[T;N]` value's allocation length
IS N). AIR then skips the `LoadField(len)`/`WrapI64`/`oob`/`TrapIf` chain.

**Z3 is never consulted.** The elision behaves identically with the `solver`
feature off; Z3 stays out of the memory-safety TCB (the SC-6 discipline the
literal-index elision established — this feature is its second setter, same
contract, documented at `TypedIndexExpr::bounds_proven`).

## 3. `arr.len()` as a bound (the headline shape)

`for i in 0..a.len() { a[i] }` is the canonical machine-written loop. `len()`
on `[T; N]` types as `u32` (the `ArrayLen { size }` intrinsic), which the T280
gate would otherwise reject — so when the end bound is `ArrayLen` on a **bare
local** receiver, the checker substitutes the STATIC size as an i64 literal.
Sound by SC-4 (allocation-len == N, always), and strictly better code: the
loop header compares against a constant instead of re-loading the length. A
*computed* receiver (`f().len()`) is NOT dropped — it stays `u32` and rejects
T280 loudly (never a silent effect deletion).

## 4. The decision table (all plain i64 compares)

With the fact interval tightened by any enclosing `if` guards on `v`
(clauses compose only under the channel certificate — an immutable,
never-rebound name is what makes trusting the narrowing frames sound here;
non-literal clause RHS are ignored, never trusted):

| Proven interval at the index site | Verdict |
|---|---|
| ⊆ `[0, N)` | **elide** — the bounds check is statically discharged |
| entirely `>= N` | **T278** (source c) — provably OOB on *every* execution; compile-time reject, the same per-execution claim as the literal `a[7]` path. Fires through else-branch negations too. |
| empty (contradictory guards) | no claim — the access is unreachable; the floor stays, harmlessly |
| anything else (straddle / no fact / compound index / slice) | the **runtime-trap floor** — never elided, never falsely rejected |

Examples: `for i in 0..10 { if i < 5 { a5[i] } }` **elides** (the guard IS the
runtime check); `if i >= 5 { a5[i] }` is a **compile error**; bare `a5[i]` in
`0..10` keeps the trap (executions 0..4 succeed — a reject would be false).

## 5. Anti-goals (v1 — declared, fail-loud)

No general Range values; no `..=`; no step/downward ranges; no iterator
integration; **no Z3 anywhere in this feature**; no facts from `break` (break
only shortens execution — per-iteration facts are unaffected); no elision
through closures or handler clauses (the barrier); no elision for compound
indices (`arr[i+1]` — no arithmetic reasoning, ever); non-zero literal starts
deferred (a one-line widening); narrow-int bounds reject T280; no
invalidation-based (flow-tracked) shadow handling. The pre-existing
diagnostics-tier narrowing gap for MUTABLE variables (V4-W4S10, documented at
its site in `type_check/statements.rs`) is NOT inherited: elision only ever
trusts the immutable-certified channel.

## 6. Machine-checkability (the SH-AIR shadow)

The elision rule is parse-tree-derivable BY DESIGN (that is *why* it is
syntactic): the shadow re-derives K (literal / len-of-array-bind), N (the
indexed bind's type), and the pre-scan, then compares `K <= N` itself —
`selfhost/air.sigil`'s `ai_index_elided` range rule, differential-pinned by
the `BODY_FORRANGE` lane (`P_K_FOR_RANGE` / `K_FOR_RANGE` = 88 on both sides).
The M3 guard-tightened elisions are UNCOVERED-not-broken in the shadow lane
(a follow-on rung needs the narrowing-walk re-derivation); covered fixtures
stay within the channel-only subset. Note the literal rule's "no N needed"
trick (type-cleanliness alone guarantees a literal index in-bounds) does NOT
extend to range vars — the shadow must compare K against N.

## Cross-references

- `docs/specs/bounded-collections.md` — the sibling bounded-ledger story.
- `type_check/statements.rs` (`check_block`'s ForRange arm, the pre-scan,
  `resolve_range_fact_end`), `type_check/expressions.rs` (`infer_index_expr`,
  both setters), `air.rs` (the ForRange arm; `index_base_and_bounds`).
- Tests: `crates/sigil-compiler/tests/range_for.rs` (accept/reject matrix),
  `range_for_elision.rs` (the AIR decision-table proof),
  `crates/sigil-runtime/tests/range_for.rs` (exec semantics + the binding
  corpus), the `range_for_basic` snapshots (the elided golden).
