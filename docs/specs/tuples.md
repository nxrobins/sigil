# Tuples — Structural Anonymous Products

**Status:** Implemented — v1 (#229): tuple types `(A, B, …)`, literals, multi-return, and `let (x, y) = …` destructuring. `.0`/`.1` index access and tuple match-patterns are deferred (lexer blocker).
**Date:** 2026-06-09
**Authors:** Nigel Robinson

---

## 1. Design Summary

A tuple `(A, B, …)` is an **anonymous product type** — the last broadly-useful primitive
on the COMPLETENESS list, and the one most directly enabling the **SIGIL lexer**, whose
every step returns `(token, new_position)`. Today that multi-return requires a named
`record` or a hand-packed `i64`; a tuple says it directly.

The implementing insight is one line:

> **A tuple IS a record.** `Type::Tuple(Vec<Type>)` is a new *structural* type, but its
> runtime representation is an anonymous record — a heap struct with positional fields
> `"0"`, `"1"`, … — so it reuses the entire record lowering with **zero new AIR nodes**.

```sigil
fn lex_step(s: str, pos: i64) -> (i64, i64) {   // (token_kind, new_pos)
    return (classify(s, pos), pos + 1);
}
let (kind, next) = lex_step(src, p);             // destructure; kind, next are i64
```

### Core Principles

1. **A type, not a trait.** `(A, B)` is structural and anonymous — no declaration, no
   `impl`. Two tuples are compatible iff their arities match and every position is
   (recursively) compatible.
2. **A record at runtime.** A tuple literal lowers to a `RecordConstruct` (heap `BumpAlloc`
   + per-field stores); an element read is a `FieldAccess`. **No new `AirValue`, no new
   `TypedExprKind`, no change to the ~10 typed-AST walkers** — the existing record arms
   already recurse.
3. **Destructure-only reads (v1).** A tuple is taken apart with `let (x, y) = …`, which
   **desugars at type-check** into a hidden temp + field reads — reusing `check_let`. There
   is no surface `.0`/`.1` yet (§5).
4. **Fail loud on a malformed tuple.** A 1-tuple `(a,)`, an empty `()` type, an over-arity
   tuple, a non-tuple destructure, or an arity mismatch is **T261** — never a silent
   mis-shape.

---

## 2. The Surface

| Form | Example |
|---|---|
| **Type** | `fn f(p: (i64, i64)) -> (i64, bool) { … }` |
| **Literal** | `let p = (1, true);` |
| **Multi-return** | `fn split(x: i64) -> (i64, i64) { return (x + 1, x + 2); }` |
| **Destructure** | `let (a, b) = p;` — per-binding `mut`: `let (mut a, b) = p;` |
| **Nested** | `let (inner, c) = ((1, 2), 3); let (a, b) = inner;` (AG-2: one level per `let`) |

The **comma is the sole discriminator** between a tuple and parenthesized grouping:
`(e)` is grouping (byte-identically to before — the AST carries no paren node), `(a, b)`
is a tuple. A 1-tuple `(a,)` is rejected (a single parenthesized value is just that value).
Arity is `2..=12` (`MAX_TUPLE_ARITY`).

---

## 3. The Mechanism

### Type (`Type::Tuple(Vec<Type>)`)

A new structural variant. Every exhaustive `Type` match grew a **recursive** arm —
`render`/`type_compatible`/`mangle`/`lower`(→`Ptr`)/`classify_value_kind`/`apply_subst`/
`is_send`/`default_int_lit`/`reassignable`/`collect_named_instantiations`. Two are
load-bearing for soundness (ET-9): `apply_subst` substitutes generics *inside* a tuple
(so a generic method returning `(T, T)` monomorphizes rather than ICE-ing in `mangle`),
and `classify_value_kind` is `Linear` if any element is (so a cap hidden in a tuple isn't
silently `Copy`).

### Construct — reuse the record path (registry-free)

A tuple literal type-checks to `RecordConstruct { type_name: <mangle>, fields: [("0", a),
("1", b), …] }`. The construct path is **registry-free**: `memory.rs::flatten_record`
derives each field's `AirType` from its own `VarId` and lays out offsets as cumulative
`width()` (align 8) — it never consults `type_name` or the field registry. So the tuple's
`type_name` is inert, given an unforgeable, injective mangle anyway (`$tuple2__i64_i64` —
the `$` is outside the identifier grammar, so it can NEVER collide with a user record; ET-2).

### Read — on-demand offset (no registry entry)

`field_base_and_offset` gains a `Type::Tuple` branch that computes the element offset
**inline**: `offset = Σ lower_type(elem[..i]).width()`, bypassing the registry entirely.
This is the **same** width rule `flatten_record` lays out on the construct side, so read
and write agree by construction — one layout, no second source of truth (ET-5).

### Destructure — a type-check desugar (the iterator precedent)

The parser emits `Stmt::LetTuple { bindings: Vec<(name, is_mut)>, ty, value, span }`. In
`check_block` the RHS is inferred once to validate it is a tuple of matching arity; on any
mismatch it emits T261 and binds the names to `Type::Error` — it **never** builds a
field-access on a non-tuple (ET-4). On success it desugars (built as untyped AST, checked
through the real `check_let`, spliced into the statement stream):

```text
let $tup_K = <value>;     // bound ONCE → evaluated once (ET-3); K = byte offset
let [mut] a = $tup_K.0;   // FieldAccess, field "0" — synthesized as a String, never lexed
let [mut] b = $tup_K.1;
```

- **Hygiene.** `$tup_K` is `$`-prefixed (ungrammatical for users) + byte-offset-suffixed,
  so it is unforgeable, unreferenceable, and distinct per destructure (ET-7). It leaks into
  the block's scope alongside `a`/`b`, but is inert.
- **Synthesized field names.** The `"0"`/`"1"` strings are built directly in the AST — they
  never pass through the lexer (which tokenizes `.0` as a float), which is exactly why this
  ships while surface `.0` stays deferred.
- **`check_let` does the bookkeeping.** Mutability, readonly, region, alias tracking all
  come free; the bindings persist in the current scope because `check_let` inserts them.

---

## 4. Diagnostics (T261)

One code spans every malformed-tuple shape — at parse time and at type-check:

- **Parse:** a 1-tuple `(a,)`, an empty `()` type, a literal/type/destructure over
  `MAX_TUPLE_ARITY` (12).
- **Type-check:** `let (x, y) = <non-tuple>` (only a tuple can be destructured), or an
  arity mismatch (`let (x, y, z) = (1, 2)` — names must equal the tuple's arity).

A trailing comma in a ≥2 tuple (`(a, b,)`) is accepted.

---

## 5. Constraints & Fallbacks (as shipped)

The epic's adversarial Constraint Matrix produced nine existential threats; each, as it
landed (every one has a Boring Limit + a Fail-Fast):

- **ET-1 — honest element types.** `(i64, bool)` etc. work; a non-`i64` *integer* element
  (the pre-existing call-width gap) errors at type-check, never a silent wrong-width store.
- **ET-2 — unforgeable, injective identity.** The synthetic `$tuple…` `type_name` carries a
  `$` (outside the identifier grammar) and an arity-tagged recursive mangle; it can never be
  spelled by user code nor collide with a record. A tuple is never keyed in the named-record
  registry.
- **ET-3 — evaluate the RHS once.** `let (x, y) = v` binds `v` to one hidden temp before any
  extraction. *(Tested: a single side-effecting RHS runs once.)*
- **ET-4 — errors abort before the desugar.** A non-tuple RHS / arity mismatch emits T261,
  binds names to Error, and emits **zero** field-extraction statements — no ICE.
- **ET-5 — one layout.** Construct (`flatten_record`) and read (on-demand) both derive
  offsets from `lower_type(elem).width()`; a round-trip test reads every element back.
- **ET-6 — region-escape parity.** A tuple is a heap pointer → region-escape-tracked exactly
  like a record/Vec (T254); no tuple exemption.
- **ET-7 — hygienic temp.** `$tup_K` is `$`-prefixed + byte-offset-suffixed: unforgeable,
  unreferenceable, distinct per destructure.
- **ET-8 — byte-identity / clean disambiguation.** `(e)` (no comma) parses byte-identically;
  the tuple branch fires only on a comma + ≥2 elements; `(a,)` rejected, `(a, b,)` accepted.
  Workload and JSON-shape snapshots pin byte identity.
- **ET-9 — recursive `Type` arms.** No catch-all absorbs `Type::Tuple`; `apply_subst`
  (tuple-of-generic) and `classify_value_kind` (tuple-of-cap → Linear) recurse.
  *(Tested: a generic method returning `(T, T)` compiles.)*

---

## 6. Anti-Goals (v1 does NOT build / guarantee)

- **AG-1 — `.0`/`.1` index access + tuple match-patterns.** Deferred (lexer blocker — `.0`
  lexes as a float, and `.field` postfix isn't parsed at all today). A tuple is read ONLY
  via `let (..) =`. A tuple that is a record field, a nested element, or
  returned-but-not-immediately-destructured cannot be element-accessed until that lands.
- **AG-2 — nested destructuring `let ((a, b), c)`.** Bindings are flat; hand-unroll with a
  second `let`.
- **AG-3 — non-`i64` integer element types.** Inherits the pre-existing `Vec<i32>`/`Vec<bool>`
  literal-call-width limitation; `(i64, …)` and non-int elements (`bool`, `str`, records,
  nested tuples) work; a non-`i64` int element errors (ET-1) rather than miscompiling.
- **AG-4 — 1-tuples `(a,)`.** Rejected (the `(a,)`-vs-`(a)` ambiguity + a `"(T,)"`-render
  special-case aren't worth it). A single value is just that value.
- **AG-5 — duplicate pattern names `let (x, x)`.** Normal `let`-shadowing; no de-dup
  diagnostic.
- **AG-6 — desugar internals in diagnostics.** A message may reference the synthetic `$tup_K`
  temp; v1 does not polish that out.

---

## 7. The Arc Beyond

The read path is already wired on `Type::Tuple`, so the next steps are cheap:

1. **`.0`/`.1` index access + tuple match-patterns (PR-2).** Gated ONLY on the lexer: split
   `.0` from a `FloatLit` and parse `.field` postfix. The type-check + AIR read side is
   already done (§3) — once `.0` parses, it reuses that branch; match-patterns add a
   `Pattern::Tuple`.
2. **`Map`/`Set` iteration.** `for (k, v) in m.iter()` — the structural iterator protocol
   yields `(K, V)` now that tuples exist (closes iteration.md's AG-1).
3. **Nested destructuring** (AG-2) — a `Pattern`-valued binding list.

The marquee consumer is the **SIGIL lexer-in-SIGIL**: a `next(self @Mut) -> Option<(Token,
i64)>` step is now expressible, and its caller destructures the pair directly.

---

## Cross-references

- `docs/specs/iteration.md` — the structural iterator protocol whose AG-1 (`(K, V)` pairs)
  tuples unblock; the type-check-desugar pattern this reuses.
- `docs/specs/bounded-collections.md` — the sibling "monomorphized record at runtime" epic;
  the 12-byte-header layout discipline tuples inherit (offsets = cumulative `width()`).
- `docs/specs/readonly.md` — T253/T254 escape gates (ET-6 region parity).
