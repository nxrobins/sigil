# The SIGIL Parser, in SIGIL — Implemented

**Status:** ✅ Implemented (PR-0 … PR-6 shipped, #242–#254) — the second self-hosting stage.
The SIGIL parser (`selfhost/parser.sigil`, ~3.4 K lines) parses every `stdlib/sigil/*.sigil`
file **node-for-node identically** to the Rust `parse_with_id` oracle — kinds, spans, values,
flags, child counts, names, effects, taints — proven by
`crates/sigil-runtime/tests/parser_differential.rs` (the whole-stdlib corpus, the ET-P1
coverage manifest over the full 1–80 kind space, the error-parity corpus, and the ET property
suite).
**Date:** 2026-06-10 (design) · 2026-06-12 (implemented)
**Authors:** Nigel Robinson
**Scope decision:** whole stdlib, full grammar — the SIGIL parser parses every
`stdlib/sigil/*.sigil` file node-for-node identically to the Rust oracle.
**AST decision:** a flat `Arena<Node>` (a `Vec<Node>` of tagged records with NodeId indices),
fronted by a small `Arena<T>` stdlib type landed first.

---

## 1. Context & Goal

The **lexer-in-SIGIL epic shipped** (#232–#241): `selfhost/lexer.sigil` tokenizes every
`stdlib/sigil/*.sigil` file — and its own lexical errors — token-for-token, value-for-value, and
diagnostic-for-diagnostic identically to the Rust `lex_with_id` oracle. The next stage on the
self-hosting critical path (`lexer → arena → parser → … → bootstrap`) is the **parser**, which
consumes the lexer's `Vec<Token>`.

> **Goal.** A SIGIL function `parse(tokens: Vec<Token>) -> Arena<Node>` whose AST, on every
> `.sigil` source in a corpus, is **node-for-node identical** to the Rust parser's
> (`crate::parser::parse_with_id`). The Rust parser is the differential **oracle** — not a fuzzy
> spec but the exact, executable definition of "correct."

Like the lexer, this is a dogfood that proves SIGIL can express a real, recursive compiler stage,
and a forcing function that surfaces the next real language gaps. It does **not** replace the Rust
parser in the pipeline yet (a later bootstrap stage); it runs alongside it as a tested artifact.

**Why batch + arena.** A batch parser is a pure function of its token input — trivially
differential-testable (parse both, compare the two ASTs). The Rust AST is a recursive heap tree
(`Box<Expr>`/`Vec<Stmt>`); SIGIL has no `Box`, and a `Vec<Node>` arena with `NodeId = i64` index
is the idiomatic, proven-expressible shape (the lexer's `Vec<Token>` already stores records). The
arena also makes serialization for the differential a flat pre-order walk.

---

## 2. The Target (the grammar + AST to reproduce)

The Rust parser (`crates/sigil-compiler/src/parser.rs`, ~4.8 K LOC) is recursive-descent with
**11-level precedence climbing** for expressions; the AST (`ast.rs`, ~1.2 K LOC) is a recursive
tree rooted at `Program`:

- **Entry (the oracle):** `parse_with_id(&SourceFile, SourceId) -> (Program, Vec<Diagnostic>)`
  (parser.rs:34). It **lexes internally** (`lex_with_id`), then parses. The SIGIL side composes
  `parse(lex(src))` instead, so the corpus input is source bytes (§4).
- **`Program` → `Vec<Module>` → `Vec<Item>`** (ast.rs:85/97/114).
- **Items (11):** `UseDecl`, `ConstDef`, `FnDef`, `ActorDef`, `CapTypeDef`, `RecordDef`,
  `EnumDef`, `ImplDef`, `EffectDecl`, `ExternFnDecl`, `TraitDef` (ast.rs:114).
- **Statements (10):** `Let`, `LetTuple`, `Assign`, `Expr`, `If`, `Match`, `While`, `ForIn`,
  `Return`, `Break`, `Continue` (ast.rs:674).
- **Expressions (23):** `Literal`, `Path`, `Call`, `MethodCall`, `Binary`, `FieldAccess`,
  `Index`, `Slice`, `ArrayLit`, `Tuple`, `Closure`, `Borrow`, `RecordConstruct`, `EnumConstruct`
  (the everyday set), plus the SIGIL exotica `Send`, `Ask`, `Spawn`, `CapRestrict`,
  `CapRestrictDeadline`, `CapSplit`, `CapDraw`, `Grant`, `Handle`, `Declassify`, `DeclassifyCt`,
  `Region`, `Try`, `ResultCtor` (ast.rs:837). `BinaryOp` has 14 variants (ast.rs:1107).
- **Patterns (5):** `Literal`, `Range`, `Wildcard`, `Binding`, `EnumVariant` (ast.rs:776).
- **Types:** `TypeExpr` — a multi-overlay struct (ast.rs:539): nominal `path` + optional
  `ref_kind`/`deadline`/`fn_type`/`array_type`/`tuple_type`.
- **Spans:** every node carries a `Span { start, end, source }` (byte offsets).
- **Error recovery:** `Option`-based with `synchronize_program`/`_item`/`_block_statement` points
  → a partial `Program` + accumulated diagnostics (parser.rs:4493+).

The **whole-stdlib "done" line** forces the full grammar the stdlib uses: generics (`<T>`,
`<K: Hash + Eq, V>`), impls, traits, refinement `where`-clauses, `extern fn`, attributes
(`#[ring(outer)]`, `#[trusted]`), records, enums-with-payload, the precedence ladder, etc.

---

## 3. The SIGIL Representation (the `Arena<Node>`)

The AST is a flat arena. `Arena<T>` (the parser's PR-0) is a thin `Vec<T>` wrapper:

```sigil
record Arena<T> { store: Vec<T>, count: i64 }
// allocate(self @Mut, item: T) -> i64   (returns the NodeId = index)
// get(self, id: i64) -> T
```

A `Node` is a fixed-size tagged record; variable-arity children live in ONE shared child-id `Vec`
(addressed by a `(child_start, child_count)` slice), so arity is unbounded:

```sigil
record Node {
    kind: i64,         // K_* tag (the harness contract; §5)
    span_start: i64,
    span_end: i64,
    value: i64,        // op-code (Binary) / scalar (IntLit, BoolLit) / pool byte-length (name-bearing)
    flags: i64,        // per-kind bitflags (e.g. FnDef bit0 = pub) — the ET-P2 slot for
                       // semantic markers `value` can't carry (PR-1 amendment)
    child_start: i64,  // index into the shared child-id Vec
    child_count: i64,  // number of children (0 for leaves)
    text: str          // the name string for name-bearing nodes (Ident/Path/field/type); "" otherwise
}
```

The parser builds **bottom-up** (recursive descent parses children first, gets their NodeIds, then
allocates the parent referencing them) — so child NodeIds are always **back-references** (already
allocated). `value` and `text` are at most one-meaningful-per-kind, exactly like the lexer's
`Token { value, text }`. The proven-feasibility basis: SIGIL enums carry payloads
(`option.sigil`/`result.sigil`), `Vec<record-with-str>` works (the lexer's `Vec<Token>`), and
`@Mut self` methods on generic records exist (`VecIter::next`) — so this needs **no compiler
change** (any gap that does surface becomes its own gated PR, as `as_output` did for the lexer).

---

## 4. The differential-test harness (the north star)

Mirrors the lexer harness (`crates/sigil-runtime/tests/lexer_differential.rs`) exactly:

1. **Compose in-SIGIL.** Inline BOTH `lexer.sigil` + `parser.sigil` into one tool; the body reads
   source via `from_bytes`, runs `parse(lex(src))`, and `encode_ast(...).as_output()`s the result
   across the single forge boundary. (`parser.sigil` symbols are `parser_`/`P_`-prefixed so the
   two inlined files don't collide — a self-detecting compile error otherwise.)
2. **Serialize pre-order.** `encode_ast` walks the arena from the root in a canonical **pre-order**
   (allocation order is not stable; pre-order is), emitting per node
   `kind,span_start,span_end,value,flags,child_count;…` then a `|`-separated string **pool** (each
   name-bearing node contributes one length-prefixed slice; `value` = its byte-length). Pre-order +
   `child_count` reconstructs the tree with no shipped child-ids. *(PR-1 amendment: the tuple
   gained `flags` — ET-P2 forces semantic markers like pub-ness to be compared, and `value` is
   taken by the text byte-length on name-bearing kinds.)*
3. **Compare node-for-node.** The host runs `parse_with_id`, **flattens** the `Program` tree into
   the SAME pre-order schema, and compares: `kind` (via a TOTAL `node_kind_of` map, §5),
   `span_start`/`span_end`, `value`, `child_count`, and the decoded name strings — at the first
   divergent pre-order index, with the offending lexeme (ET-P2).
4. **Oracle-independent checks.** Spans nest (`assert_span_containment`, ET-P6); the encoding is
   bounded + host-validated (ET-P7); two runs are byte-identical (ET-P8).
5. **Diagnostics.** Parser syntax errors are in-stream **error-nodes** (a `K_ERR` kind, `value` =
   P-code, the error span); the host splits them out and compares to the oracle's diagnostics by
   code + position (AG-P3), reusing the lexer's PR-3b error-token pattern. The clean corpus is all
   valid (zero diagnostics); a SEPARATE malformed corpus exercises each P-code (ET-P1).

---

## 5. Load-bearing decisions

- **The canonical child-order schema (ET-P3).** The single most important contract: each node
  kind has ONE fixed, total child order, defined once and produced IDENTICALLY by the SIGIL
  encoder and the Rust flattener. E.g. `FnDef` = `[type-params…, params…, return-type?,
  where-clauses…, body]`; `If` = `[cond, then-block, else?]`; `Call` = `[callee, args…]`;
  `Match` = `[scrutinee, arm…]`. Optional children are present-or-absent (the `child_count`
  reflects it); a `?`-absent child is simply omitted (its absence is meaning, ET-P2). The schema
  table is the spec's appendix and the flattener's contract.
- **The node-kind tag table (`K_*`) ⟷ `node_kind_of` (ET-P9).** SIGIL `parser.sigil` `const K_*`
  tags are the contract with the harness's TOTAL `node_kind_of(&ast-node) -> i64` (no `_` arm) —
  a new Rust AST variant won't compile until mapped, drift-locked exactly like the lexer's
  `tag_of`. The literal/operator tags reuse the lexer's value conventions where they overlap
  (`BinaryOp` ⟷ the lexer's operator tags).
- **Name strings via the pool.** Unlike the lexer (only `StrLit` carried text), MANY parser nodes
  are name-bearing (`Ident`, each `Path` segment, field names, type names). Each ships its bytes
  through the same length-prefixed pool the lexer's `StrLit` used; `value` carries the length.
- **Composition over re-lexing (AG-P4).** The parser consumes the SIGIL lexer's `Token` values
  verbatim and inherits its anti-goals — `FloatLit` is span-only, identifiers ASCII; the parser
  never re-derives a token value.

---

## 6. Mechanism details & SIGIL constraints

- **Recursive descent + precedence climbing** mirrors the oracle's 11 levels (parser.rs
  ~3140–3553). Hand-written SIGIL constraints apply (see `memory/sigil-handwritten-code-gotchas`):
  no `&&`/`||` (nested `if`), explicit empty `else {}`, every path `return`s, `Vec<T>` element
  type from the binding, build large strings via `Vec<str>` + `join` (not O(n²) `concat`), slice
  on codepoint boundaries.
- **Mutual recursion** between `parse_expr`/`parse_stmt`/`parse_item`/`parse_type` threads the
  `@Mut` arena through dozens of helpers — the most likely place to surface a compiler gap; treat
  any as its own gated PR.
- **Tokens in, AST out, one boundary.** No token re-serialization: `lex(src)` yields `Vec<Token>`
  in-tool; the parser indexes it with a cursor (the parser's ET-P5 progress invariant: every step
  consumes ≥1 token).

---

## 7. Staging plan (the PR ladder)

Each stage is a shippable, gated PR; each grows the differential corpus it must pass.

- **Design PR** ✅ (#242) — the ritual-hardened design (the ETs/matrix/anti-goals below).
- **PR-0 — `Arena<T>`** ✅ (#243) — `stdlib/sigil/arena.sigil` (`allocate`/`get`/`len`, ambient
  wiring) + 8 runtime tests pinning the threading + NodeId-tree patterns. Surfaced NO compiler
  gap; `set` (in-place patch) was added in PR-2a for the literal fold, exactly as PR-0 predicted.
- **PR-1 — harness + minimal parser** ✅ (#244) — the inline lexer+parser tool, the pre-order
  encoder, the differential vs `parse_with_id`; mutual recursion + forward refs proven. The
  per-node tuple gained `flags` (the ET-P2 amendment).
- **PR-2.x — expressions** ✅ — 2a (#245) the 7-level binary climb + prefix (the unary-minus
  parse-time FOLD via Arena::set, the `!` desugar) + all literals; 2b (#246) postfix/calls/
  methods/paths (NO parse-time FieldAccess — dots extend paths; the method receiver spans the
  FULL path); 2c (#247) arrays + the `[elem; N]` parse-time clone-expansion, tuples, record
  construction.
- **PR-3.x — statements** ✅ — 3a (#248) let/let-tuple/assign (the LOCAL compound desugar:
  cloned target + statement-wide Binary) /expr-stmt; 3b (#249) if/while/for-in/break/continue +
  match with the 5-pattern grammar (arm separators REQUIRED — juxtaposition is P018).
- **PR-4.x — items & types** ✅ — 4a (#250) the full TypeExpr grammar (refs are FLAGS — the
  oracle hoists the inner path; `&mut [T]` drops the mut; nested generics close `> >`), params
  (+ annotations), closures; 4b (#251) record/enum/const/use/impl/trait/extern-fn/effect items,
  fn generics + effect rows, module attributes (`ring` lexes as a KEYWORD).
- **PR-5.x — ret-taint + the exotica** ✅ — 5a (#252) ret-taint + THE WHOLE STDLIB PARSES (the
  north star, hit early: the stdlib's only exotica usage was ret-taint); 5b (#253) actors,
  cap-types, the actor/cap ops (`.send`/`.ask` lex as keywords), spawn/grant/handle/declassify/
  region, refinement where-clauses (spans start at `where`; a record-level clause sits OUTSIDE
  its record's span — the second ET-P6 exemption), cap-deadline types. Grammar-totality:
  the only unmapped Expr variants (EnumConstruct/FieldAccess) are never parser-produced.
- **PR-6 — the manifest + error parity** ✅ (#254) — the ET-P1 coverage manifest over the full
  1–80 kind space (green first run); parser-error PRESENCE + dispatch-level FIRST-POSITION
  parity (coarse P-code parity deferred — see the AG-P3 amendment); CI-budget sampling.
- **PR-N — docs + roadmap flip** ✅ — this flip.

Streaming/incremental parsing, the P-code retrofit, and swapping the SIGIL parser into the
pipeline are **post-v1**.

---

## 8. Constraints & Fallbacks (the hardened constraint set)

The adversarial pass distilled one meta-thesis — **a green differential ⇏ a correct parser unless
the serialization is exhaustive + injective, the corpus is total, and the arena is structurally
sound** — into nine Existential Threats, each a strict negative constraint with a dumb physical
bound (the *Boring Limit*) and a non-swallowing *Fail-Fast*.

### Existential threats → strict negative constraints

- **ET-P1 — Total corpus coverage.** A coverage-manifest test MUST assert every AST node-kind tag
  AND every parser production appears ≥1× in the corpus's `parse_with_id` output; a SEPARATE
  malformed corpus MUST exercise each P-series error code; the corpus MUST include hand-written
  productions + adversarial fragments BEYOND the fixed stdlib. "Done" is BLOCKED until node-kind
  coverage is total and the whole stdlib parses.
- **ET-P2 — Exhaustive, injective serialization.** The per-node compared tuple MUST carry every
  semantically-distinguishing field — kind, operator/discriminant/variant, EVERY literal value,
  EVERY identifier/path/field/type-name string, and the present-vs-absent bit of each optional
  child. Two ASTs differing in any meaning-bearing way MUST serialize differently. Kind-only or
  span-only comparison is FORBIDDEN.
- **ET-P3 — Children complete + canonically ordered.** The Node representation MUST store ALL
  children of every node (N children → N serialized; no fixed-arity truncation). Each node kind
  MUST have ONE deterministic total child order (§5), produced IDENTICALLY by the SIGIL encoder and
  the Rust flattener.
- **ET-P4 — Arena integrity (valid, acyclic, reachable).** Every child slot MUST be the single
  reserved no-child sentinel (`-1`) or an in-bounds BACK-reference (`0 ≤ id < current_len`);
  forward/OOB indices FORBIDDEN. The graph MUST be acyclic. Every allocated node MUST be reachable
  from the root (reachable-count == allocated-count — no orphans).
- **ET-P5 — Monotone progress + bounded traversal.** Every parse step MUST consume ≥1 token OR
  total steps ≤ token-count (zero-progress is a rejected ICE); the encoder MUST emit ≤ node-count
  nodes; over-count MUST fail-fast, never hang. Fuel is the runtime backstop.
- **ET-P6 — Span containment (oracle-independent).** A property test MUST assert, without the
  oracle, `parent.start ≤ child.start ≤ child.end ≤ parent.end` for every edge, the root span
  covers the module, and sibling spans are non-decreasing.
- **ET-P7 — Bounded, host-validated encoding; fail-fast.** The encoding MUST be size-bounded
  (`NODE_MAX`); the host MUST validate node-count + byte-len + EVERY decoded child index against
  the actual buffer size BEFORE use; over-bound → distinct sentinel, never a wrapped/stale pointer.
- **ET-P8 — Determinism, purity, no-trap.** `parse` MUST be a pure deterministic function of the
  tokens (identical encoding every run + across two compiles; NO heap address in any node field)
  and MUST NOT trap on any token sequence the SIGIL lexer can produce (incl. lexer error-tokens).
- **ET-P9 — Tag table total + drift-locked.** `node_kind_of(&ast-node) -> i64` MUST be TOTAL with
  NO `_` arm (every `Expr`/`Stmt`/`Item`/`Pattern`/… variant mapped) + injective; a host test
  asserts it against the Rust AST enums.

*Not an ET:* the inlined `lexer.sigil` + `parser.sigil` MUST share no symbol (a self-detecting
compile error; `parser_`/`P_`-prefixed disjoint namespace).

### Constraint Matrix (a Boring Limit + a Fail-Fast per ET)

This PINS the encoding: a pre-order node stream `kind,span_start,span_end,value,flags,child_count;…`
+ a `|`-separated string pool; the arena's internal child-ids are validated during the walk but not
shipped (pre-order + counts reconstructs the tree).

| ET | Boring Limit | Fail-Fast |
|----|--------------|-----------|
| ET-P1 Coverage | Manifest = 100% of the node-kind set (N = Expr+Stmt+Item+Pattern+TypeExpr-overlay variant count) + every P-error code + ≥1 non-stdlib input. | `parser_coverage` enumerates kinds in the reference AST; any uncovered kind → FAIL listing misses; "done" blocked until total + whole stdlib parses. |
| ET-P2 Injective encode | Compared per-node tuple is EXACTLY `(kind, span_start, span_end, value, flags, child_count)` (+ the decoded name text); name strings ride a length-prefixed pool (one slice per name-bearing node, `value` = byte-length); `flags` carries per-kind semantic bits (FnDef pub etc.); one compare fn. | Any field divergence → node compare FAILS at the first pre-order index (expected vs actual + lexeme); a name-bearing node with no pool slice → encode hard-errors. |
| ET-P3 Children | Node holds children as a `(child_start, child_count)` slice into one shared child-id `Vec` (unbounded arity); per-kind child order is a fixed schema table; encoder emits pre-order + `child_count`. | SIGIL `child_count` ≠ oracle count at a node → FAIL there; `child_start+child_count >` array len → `Vec.get` bounds-trap → tool trap → harness FAIL. |
| ET-P4 Arena integrity | Child ids ∈ {−1} ∪ [0, node_count); the pre-order walk visits each node exactly once (counter ≤ node_count). | OOB id → `Vec.get` bounds-trap (caught); walk emits > node_count → `PARSE_CYCLE`; reachable < allocated → FAIL with the orphan gap. |
| ET-P5 Progress | Parser steps ≤ token_count (≥1 token/step); encoder emits ≤ node_count. | Zero-advance step → `PARSE_NO_PROGRESS` sentinel, never a hang; over-count → `PARSE_CYCLE`; fuel is the runtime backstop. |
| ET-P6 Span nesting | `parent.start ≤ child.start ≤ child.end ≤ parent.end` per edge; root span = `[0, len]`; siblings non-decreasing EXCEPT around synthetic desugar nodes (the oracle's `!x` → `x == false` puts a synthetic `false` at the BANG's span — a second child that precedes the first in source; containment still holds). SECOND exemption (PR-5b): a RECORD-level refinement `where` clause is a child that sits OUTSIDE its record's span — the oracle closes the record span at `}` before the clause parses — so K_REFINEMENT nodes are exempt from the containment check. | Oracle-independent `assert_span_containment` panics on the first violating edge (parent + child spans); every fixture. |
| ET-P7 Encoding bound | `node_count ≤ NODE_MAX = 2^20` (~1.05M; largest stdlib file ~10 K nodes → ~100× headroom); each `child_count ≤ node_count`; `byte_len < 2^32`. | `node_count > NODE_MAX` → `0 - PARSE_TOO_LARGE` (negative sentinel), never a wrapped pointer; host validates `byte_len ≤ memory.size()` + every index < node_count BEFORE decode, else hard error. |
| ET-P8 Purity/no-trap | `parse` reads only the tokens (no clock/heap-addr/random); no node field stores a pointer. | Determinism test: two runs + two compiles byte-identical, else FAIL (SHADOW infra); no-trap fuzz feeds adversarial token streams + lexer error-tokens, asserts a returned tree (a trap FAILS it). |
| ET-P9 Tag table | One tag per Rust AST variant (count == total variant count); fixed enumeration, no duplicates. | `node_kind_of` `match` with NO `_` arm — a new variant fails to COMPILE; a host test asserts no-dup + SIGIL `K_*` consts == the map. |
| (build) Namespace | Every `parser.sigil` top-level symbol is `parser_`/`P_`-prefixed, disjoint from `lexer.sigil`. | A collision is a COMPILE error in the inlined tool (self-detecting); a lint asserts the symbol sets are disjoint. |

---

## 9. Anti-Goals (v1 does NOT do)

Formally declared so future developers need engineer NO fallback for these:

- **AG-P1 — Adversarial recursion depth.** v1 does NOT engineer an iterative parser or a
  recursion-depth guard for pathologically deep nesting (hundreds–thousands of levels). Real SIGIL
  nests shallowly; the WASM stack + fuel are the only backstop. A source crafted to overflow the
  recursive-descent stack is UNSUPPORTED.
- **AG-P2 — Sources beyond the encoding ceiling.** A source whose node arena would exceed
  `NODE_MAX` (ET-P7) is UNSUPPORTED; the encoder fail-fasts rather than chunking/streaming.
- **AG-P3 — Error-recovery internal-span + message fidelity.** v1 matches parser-error PRESENCE +
  POSITION, NOT the exact message strings NOR the internal spans/shape of the
  partial/synchronized nodes the oracle synthesizes during recovery. (The parser's AG-L4.)
  *PR-6 amendments:* (1) POSITION parity holds at dispatch-level errors, where the SIGIL bail
  node survives as the production's result; an error deep inside an expression whose partial
  subtree the bailing production DISCARDS (an orphan, absent from the pre-order stream)
  surfaces only as a later cascade bail, so those fixtures assert PRESENCE only. (2) Coarse
  P-CODE parity is DEFERRED: the SIGIL parser's uniform `parser_bail` carries no per-site code
  (the oracle has ~24 P-codes across ~100 expect sites — a retrofit tracked as a follow-on),
  unlike the lexer's 4-code L-series, which did ship code parity.
- **AG-P4 — Inherited token-value fidelity.** The parser consumes the lexer's `Vec<Token>` and
  inherits its anti-goals unchanged: `FloatLit` is KIND + span only (no `parse_f64`), identifiers
  are ASCII. The parser does NOT re-lex or improve any token value.
- **AG-P5 — Representational (not just structural) identity.** "Identical to the oracle" means
  identical under the canonical serialization (kind + ordered children + distinguishing values +
  spans), NOT identical memory layout. The SIGIL side is a flat `Arena<Node>`, the Rust side a
  boxed tree; v1 does NOT mirror `Box`-vs-index, struct field order, or `Debug` formatting.

---

## 10. The Arc Beyond

1. **Type-check the SIGIL AST** — the next compiler stage, consuming this `Arena<Node>`.
2. **The P-code parity retrofit** — thread per-site P-codes through `parser_bail` (~24 codes /
   ~100 sites) to upgrade AG-P3's error parity from presence+position to coarse-code.
3. **Streaming / incremental parsing** — post-v1, over the same recursive-descent core.
4. **Wire the SIGIL parser into the pipeline** — a Stage-0 → Stage-1 bootstrap step.
5. **`Arena<T>` generalization** — region-associated arenas, bulk reset (the memory-model roadmap).

---

## Cross-references

- `selfhost/parser.sigil` — THE artifact (with `selfhost/lexer.sigil`, inlined into one tool:
  `lex → parse` composes in-SIGIL).
- `crates/sigil-runtime/tests/parser_differential.rs` — the proof: the whole-stdlib corpus, the
  ET-P1 manifest, the error-parity corpus, the ET property suite.
- `docs/specs/lexer-in-sigil.md` — the sibling stage (Implemented); the harness pattern this mirrors.
- `crates/sigil-compiler/src/parser.rs` + `ast.rs` — the oracle + AST inventory.
- `stdlib/sigil/arena.sigil` — the AST storage (`Arena<T>`, this epic's PR-0).
- `docs/specs/self-hosting-completion-ladder.md` — the current bootstrap authority.
