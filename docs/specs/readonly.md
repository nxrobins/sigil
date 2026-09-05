# `@ReadOnly` — Mutation-as-Capability

**Status:** Implemented — v1 complete (PR-0 … PR-5); **default-frozen SHIPPED** (DEF-1, `bare ⇒ frozen`)
**Date:** 2026-06-02 (DEF-1 update: 2026-06-05)
**Authors:** Nigel Robinson

---

## 1. Design Summary

SIGIL verifies capability, constant-time, and taint guarantees over a **shared-mutable heap**: records, `Vec`, and `Map` are heap pointers with reference semantics, so `let b = a;` aliases the same header and a write through either is observed by both. The type system had no way to say *"this function will not mutate the value you hand it."* `@ReadOnly` is that statement — the first capability primitive that gates **mutation authority** rather than behavior or confidentiality.

`@ReadOnly` is a type-level annotation on a function parameter. It is the simplest possible capability and the exemplar for the project's capability heuristics: **fully static** (no runtime component, zero codegen impact), the **attenuation** primitive (you can freeze a mutable value on the way in, never thaw a frozen one), pure **shape** (a no-mutate interface, never "which fields" or "how much"), and **orthogonal** to taint (`@SecretCT @ReadOnly` compose, each checked independently).

```sigil
record Point { x: i64, y: i64 }

fn distance_sq(p: Point @ReadOnly) -> i64 {
    return p.x * p.x + p.y * p.y;   // OK — reads through the frozen handle
}

fn corrupt(p: Point @ReadOnly) -> i64 {
    p.x = 0;                        // REJECTED at compile time (T251)
    return p.x;
}
```

It ships alongside `@Mut`, the explicit-mutable marker, so the eventual default-flip (bare param ⇒ frozen) is a one-line predicate change rather than a re-architecture.

### Core Principles

1. **Gate the write, don't just track the value.** Taint tracks where a value *flows*; `@ReadOnly` controls whether a *handle* permits mutation. Different axis, different check.
2. **A callee-side promise, not a caller-side guarantee.** `@ReadOnly` soundly means *"I, the callee, will not mutate through this handle, and I will not leak a mutable handle to it."* It does **not** mean *"no alias anywhere mutates this object"* — that is the global guarantee a borrow/region pass provides (DEF-2), and v1 is honest about not providing it (§7).
3. **Attenuate, never escalate (H6).** A mutable value may be frozen on entry to a `@ReadOnly` parameter. A frozen value may never reach a mutable sink. The authority chain only loses power; there is no `thaw` operation.
4. **Shape, not power (H2).** `@ReadOnly` names the *interface* (a read-only handle). It never names which fields are protected or how deeply — that would be a different, finer feature (AG-4, AG-5).
5. **Compose, never inherit (H7).** Mutability is one axis, taint another. A parameter may be `@SecretCT @ReadOnly`; each is checked independently and neither masks the other. There is no super-annotation.
6. **Static where possible (H4); default-frozen since DEF-1 (H5).** 100% compile-time; AIR and WASM are untouched and byte-identical. v1 shipped *opt-in* (a default-frozen the compiler couldn't enforce against remote aliases would have been theater); once DEF-2c closed AG-1's call-site core, **DEF-1 flipped the default — a bare param is now frozen, `@Mut` the opt-up** (§8). The honesty lint (§3.7) still marks the deep-aliasing boundary.

---

## 2. Findings & Rationale

### 2.1 Why a Tri-State Enum, Not a `Type` Wrapper

Three representations were considered:

| Option | Trade-off |
|--------|-----------|
| `Type::Frozen(Box<Type>)` wrapper | Touches ~20 `Type` match sites; infects the type so every consumer must thread frozen-ness; fights H2 (the annotation is on the *handle*, not the type) |
| A flag on `Type::Ref` | Records / `Vec` / `Map` pass by a **bare heap pointer**, not `&T` — they are not `Ref`, so the flag would miss the common case |
| **`Mutability { Default, ReadOnly, Mut }` on `Param`** | One positional axis on the parameter, mirroring the proven `FunctionSig.param_refinements`; visible cross-module via `workspace_sigs` with no extra threading |

The third is the clean fit. `Mutability` is an orthogonal axis carried beside `TaintLabel` on `ast::Param`, threaded to `FunctionSig.param_mutability: Vec<Mutability>`. It never enters `TypedParam`, the AIR, or the WAT — which is why every snapshot in the corpus is byte-identical across all six PRs.

### 2.2 Why Opt-In (the H5 Honesty Decision)

"The compiler infers least authority" (H5) means *verifies* least authority. SIGIL has no borrow or aliasing pass yet, so it cannot prove the global property "no other alias mutates this object." A default-frozen world would therefore promise a guarantee the compiler cannot back. v1 instead defaulted to **neither**: a bare parameter was mutable (nothing in the existing corpus changed), `@ReadOnly` an opt-in restriction the compiler *can* soundly enforce (the callee-side promise), and `@Mut` the opt-in explicit-mutable marker. The H5 end-state — bare ⇒ frozen — was deferred to DEF-1, where it lands as a one-line predicate flip once the enforceability gap closes.

**Update (DEF-1 shipped).** That gap closed: DEF-2c (`docs/specs/exclusivity.md`) shut AG-1's reachable call-site core (T255), making default-frozen soundly enforceable for the case the flip introduces *en masse*. DEF-1 then performed the flip — `is_frozen` is now `matches!(self, ReadOnly | Default)`, so **a bare param is frozen and `@Mut` is the opt-up**. The opt-in framing in the rest of this spec describes the original v1 design; the *default* is now frozen, while the gates, the mechanisms, and the soundness boundary below are exactly as written (the flip changed only which params the gates apply to, not the gates).

### 2.3 The Mutating-Method Dissolution

`vec.push`, `vec.set`, `map.insert` are ordinary SIGIL functions taking `self` (`stdlib/sigil/vec.sigil`, `stdlib/sigil/map.sigil`). `v.push(x)` binds `v` into `push`'s `self` parameter. So "reject `.push()` on a `@ReadOnly` receiver" **is** the escape gate applied to the receiver — no special case for mutating methods. The stdlib *declares* which methods are read-only by annotating `self: Vec<T> @ReadOnly` on `len`/`capacity`/`get` (and the full read surface of `Map`) and leaving the mutators with a plain `self`. The checker needs zero knowledge of which methods mutate; the signature is the single place a reader looks (H1).

### 2.4 Cost Model

| Operation | Cost |
|-----------|------|
| Representation (`Mutability` on `Param` + `FunctionSig`) | One enum field; never reaches `TypedParam`/AIR/WAT |
| Parse (`parse_param_annotations`) | One annotation loop, already present for taint labels |
| The readonly set + WRITE/ESCAPE gates | One `HashSet<String>` per function body + a label comparison per assignment / escape sink, at typecheck |
| The honesty lint (T252) | One pure-AST pass over parameters, once per definition |
| Runtime cost | **Zero.** Every check is at typecheck; the WAT is byte-identical to the un-annotated program. |

---

## 3. Mechanisms — The Enforcement Model

`@ReadOnly` / `@Mut` ride the existing taint-annotation parse rails, then fork into two static gates plus the honesty lint. Nothing reaches AIR.

### 3.1 Representation

```rust
pub enum Mutability { Default, ReadOnly, Mut }   // ast.rs
```

`pub mutability: Mutability` on `ast::Param`; `param_mutability: Vec<Mutability>` on `FunctionSig`, populated in `collect_function_sigs` (`type_check/universe.rs`) from `def.params`, positionally aligned (including `self` at index 0 for methods).

### 3.2 Parse

After the parameter type and optional taint label, `parse_param_annotations` (`parser.rs`) consumes an optional `@ReadOnly` / `@Mut`. A parameter carries exactly one of the three states. `@ReadOnly @Mut` together is a parse error (**P021**) — no contradictory authority (H3). An unknown `@Ident` in parameter position that is neither a taint label nor a mutability marker is the same P021 path.

### 3.3 The Readonly Set (NC-1)

`MonomorphTracker.readonly_locals: HashSet<String>` is **one append-only set per function body**. It is *seeded* in `check_function_block` from the `@ReadOnly` parameters (saved and restored around the body via `std::mem::replace`, like the return-refinement frame, so nested closures and monomorph re-entry never leak readonly names across function boundaries). It *grows* monotonically: a `let b = <expr>` whose place-root is already readonly adds `b` — this propagation is what catches the one-line launder `let b = p; b.x = 10`. The set is append-only (no branch-sensitive removal — conservative, fail-closed). `let` is the **sole** propagate site; every other appearance of a readonly value is a *sink*.

Membership uses one recursive helper, `place_root_local(expr) -> Option<&str>`, which walks `FieldAccess.object` / `Index.array` to the root `Local` (mirroring `render_place`).

### 3.4 The WRITE Gate (T251)

In `check_assign` (`type_check/statements.rs`): any assignment — plain `=` or **any** compound `op` (`+=`, `-=`, …) — whose place is a `FieldAccess` or `Index` rooted in a readonly local is rejected with **T251**. The gate is **op-agnostic** (it reads the place, never the operator) and **fail-closed** (the place set is the T243-whitelisted `Local`/`FieldAccess`/`Index`, over which `place_root_local` is total). A bare-local rebinding (`p = …`) is the T042 path, not a write-through, so it is not a T251 site.

### 3.5 The ESCAPE Gate (T253)

A value rooted in a `@ReadOnly` local may flow only into another `@ReadOnly` position. Reaching a **mutable** destination hands a mutable handle to the caller/callee and re-widens authority, so it is rejected with **T253**. The sink set is **closed**:

| Sink | Site | Rejected when |
|------|------|---------------|
| `return <value>` | `check_return` | the returned value aliases a readonly local |
| call / `extern` argument | `infer_call_expr` | the arg flows into a non-`@ReadOnly` parameter |
| method receiver + method argument | `infer_method_call_expr` | the receiver hits a plain-`self` method, or an arg flows into a non-`@ReadOnly` parameter |
| record-construct field | `infer_record_construct_expr` | a field value aliases a readonly local |
| assignment RHS | `check_assign` | the RHS aliases a readonly local and the LHS place-root is **not** readonly |

Two properties make the gate sound and precise:

- **Alias vs. copy.** `is_aliasable_type(ty)` is true only for heap/reference types (`Named`, `Array`, `Ref`, `Slice`, `Ptr`, `MutPtr`, `Generic`) and false for scalars, `Str` (an immutable view), `Unit`, `Cap`, `Fn`, `ActorRef`. So `return p.x` (an `i64` copy) stays legal while `return p` (a record alias) is rejected. Reading a frozen value is always free; only an *alias* of it escapes.
- **The single chokepoint (NC-3).** Every call-dispatch flavor routes argument binding through the same predicate. Free calls, cross-module calls, and the string/trait method reroutes all rewrite to `infer_call_expr`'s gate; true methods use the structurally identical gate in `infer_method_call_expr`. The per-parameter decision is one helper, `Mutability::is_frozen()` (§3.8).

*Allowed direction (H6):* `mutable → @ReadOnly` (freeze on entry) and `readonly → readonly` compile; `readonly → mutable` never does.

### 3.6 The Stdlib Read Surface

`@ReadOnly self` is declared on the entire read surface so frozen collections stay readable:

- `vec.sigil`: `len`, `capacity`, `get` (mutators `push`, `set` keep plain `self`)
- `map.sigil`: `len`, `capacity`, `is_empty`, `key_eq`, `find_slot`, `get`, `get_or`, `contains` (mutators `ensure_buckets`, `grow`, `insert` keep plain `self`)

The annotations **compose**: a `Map` read calls `self.<field>.get(..)` on its `Vec` fields and `self.find_slot(..)` on `self`, all of which are now `@ReadOnly self`, so a frozen map reads through its frozen `Vec` fields with no self-rejection. String and trait methods need **no** annotation: their receivers (`str`, `i64`, `bool`) are non-aliasable, so the escape gate is vacuous there.

### 3.7 The Honesty Lint (T252) — the First Warning

A `@ReadOnly` parameter whose declared type is an aliasable **reference/view** (`&T` / `&[T]`, i.e. `Param.ty.ref_kind.is_some()`) emits **T252**, a **non-blocking warning**: without a borrow/aliasing pass, the no-mutation promise is partial for a view (a different alias could mutate the pointee). The annotation is still honored as far as v1 enforces it. By-value heap parameters (records / `Vec` / `Map`, `ref_kind == None`) carry the same partial guarantee but are **not** per-site linted (AG-11) — else every `@ReadOnly self` in the stdlib would flood warnings.

T252 is SIGIL's first warning-severity diagnostic. It required building the warning channel the language never had: `type_check::check_with_warnings` aborts on `Severity::Error` only and threads warnings out on success to `Compilation.warnings` / `CompileResult.warnings`; `check_with_options` remains the 2-tuple back-compat wrapper. This is byte-identical to the historical errors-only gate for every program that emits no warning.

### 3.8 The Freeze Predicate (NC-4)

All three gate sites (the readonly seed, the call-arg gate, the method gate) route their "is this parameter restricted?" decision through one predicate:

```rust
impl Mutability {
    pub fn is_frozen(self) -> bool { matches!(self, Mutability::ReadOnly) }
}
```

Since DEF-1, both `@ReadOnly` AND bare (`Default`) freeze through this one predicate (`matches!(self, ReadOnly | Default)`); only `@Mut` is mutable. `@Mut` is represented distinctly from `Default` and never collapsed into it — which is exactly what let the flip be a single unambiguous line (§8).

---

## 4. The Soundness Boundary

What v1 **guarantees** for a `@ReadOnly` parameter `p`:

- The function body does not write through `p` or any local that aliases it (T251).
- No alias of `p` escapes the function to a mutable destination — return, call/method/extern argument, record field, or mutable assignment (T253).
- These hold through arbitrary `let`-hop chains and through every call-dispatch flavor (NC-1, NC-3).

What v1 does **not** guarantee (and does not claim):

- **Remote aliasing (AG-1).** A *different* function holding a second binding to the same heap object may mutate it while this function holds `p @ReadOnly`. The global "no alias anywhere mutates this object" property needs regions/borrows (DEF-2). v1 is a per-function callee-side promise. *(Update: DEF-2c — call-site exclusivity, `docs/specs/exclusivity.md` — now closes the reachable CORE of AG-1: the single-call frozen+mutable aliasing case is rejected (T255). The through-return and container-mediated remainder still awaits full borrow checking.)*
- **Deep / through-return aliasing (AG-4).** The guarantee is shallow: it covers the top-level structure rooted at `p`, not interiors reached through a method's return value. `ro_vec.get(0)` returns a fresh value whose readonly-ness is not propagated (returns carry no annotation surface, AG-6).

The honesty lint (§3.7) marks the most visible place this boundary bites — aliasable reference/view parameters — and the boundary is closed, not patched, when borrow checking lands.

---

## 5. Diagnostic Inventory

| Code | Severity | Fires when |
|------|----------|------------|
| **P021** | Error (parse) | `@ReadOnly @Mut` on one parameter, or an unknown `@Ident` mutability marker |
| **T251** | Error | a write-through (`p.x = …`, `p[i] = …`, any compound op) to a place rooted in a `@ReadOnly` value |
| **T252** | **Warning** | `@ReadOnly` on an aliasable reference/view parameter (`&T` / `&[T]`) — partial guarantee until borrow checking |
| **T253** | Error | a `@ReadOnly` value (an alias) escapes to a mutable destination in the closed sink set (§3.5) |

T251 and T253 abort compilation (no bytecode emitted, per the standing `has_errors() ⇒ abort-before-AIR` rule). T252 is non-blocking; the program still compiles.

---

## 6. Heuristic Map

| Heuristic | How v1 honors it |
|-----------|------------------|
| **H1** first-attempt legibility | a reader sees `self @ReadOnly` on `.get` and plain `self` on `.push` and guesses correctly; `@ReadOnly`/`@Mut` read on first encounter |
| **H2** shape, not power | `@ReadOnly` names the read-only handle, never which fields or how much |
| **H3** no authority conflict | one of three states per parameter; `@ReadOnly @Mut` rejected (P021); a frozen value can reach exactly one (read-only) authority chain |
| **H4** static where possible | 100% compile-time; AIR/WASM untouched; T252 marks the exact boundary of what is not yet statically verifiable |
| **H5** least authority = verify | v1 verified the callee-side promise it could soundly back; default-frozen SHIPPED (DEF-1) once DEF-2c made it enforceable |
| **H6** attenuate, never escalate | `mutable → readonly` allowed, `readonly → mutable` forbidden — the monotone exemplar |
| **H7** compose, never inherit | mutability and taint are independent axes; `@SecretCT @ReadOnly` each checked separately; no super-annotation |

---

## 7. Explicit Anti-Goals

The following are formally OUT OF SCOPE for `@ReadOnly` v1. A program exhibiting any of these does NOT violate the `@ReadOnly` guarantee, and contributors are NOT required to detect or engineer fallbacks for them. PRs adding such detection are not blocked, but reviewers MUST NOT block a PR for failing to address an item here.

- **AG-1 — Remote / cross-function aliasing.** v1 catches the LOCAL launder (`let b = p; b.x = 10` is rejected, NC-1) but not a remote alias held in a different function that mutates while this function holds `p @ReadOnly`. The global guarantee needs regions/borrows (DEF-2). *(DEF-2c — call-site exclusivity — has since closed the reachable CORE of this: a single call may not hand one object to a frozen and a mutable parameter (T255, `docs/specs/exclusivity.md`). The through-return / container remainder still awaits full borrows.)*
- **AG-2 — Regions / borrow inference.** Out of scope — the substrate the lint points at (DEF-2).
- **AG-3 — Default-frozen (the H5 flip).** Was deferred to DEF-1; v1 shipped both annotations so the flip would be a predicate change. **DEF-1 has since shipped** (`bare ⇒ frozen`, one line at `is_frozen`); the stdlib + corpus `@Mut` migration was done by hand (the `sigil fix --add-mut` codemod stayed an anti-goal — the corpus was small enough).
- **AG-4 — Deep aliasing through method RETURN values.** The guarantee is shallow: a `@ReadOnly` container whose element is itself a heap pointer can have an element mutated via a value returned from a read method, because v1 does not propagate readonly through return values. Closing this needs return-position provenance (DEF-1+).
- **AG-5 — `Vec<@ReadOnly T>` element freezing.** The annotation is on the parameter handle, not container elements.
- **AG-6 — No let/return/field annotation surface.** `let x @ReadOnly = …`, `-> T @ReadOnly`, `field: T @ReadOnly` do not parse (parameters only). Readonly still PROPAGATES into let-locals (NC-1) — it simply cannot be written there explicitly.
- **AG-7 — Closures / indirect calls.** A `Type::Fn` value carries no per-parameter mutability, so v1 cannot gate an indirect-call argument. (SIGIL has no first-class closures yet, so this path is not live.)
- **AG-8 — Runtime revocation / dynamic freeze.** Fully static, forever.
- **AG-9 — Inferring which methods mutate.** The stdlib *declares* `@ReadOnly self`; v1 analyses no method bodies to deduce mutation.
- **AG-10 — No forcing function (opt-in coverage).** v1 gave an un-annotated corpus zero protection, BY DESIGN (the H5 opt-in decision). **DEF-1 resolved this**: the default is now frozen, so coverage is universal — every bare heap param is protected without annotation, and `@Mut` is the explicit opt-OUT.
- **AG-11 — Lint covers reference/view types only.** T252 fires on `&T` / `&[T]` parameters only. By-value heap parameters carry the same partial guarantee but are not per-site linted (the caveat lives in this prose, not a per-param warning).
- **AG-12 — Primitive `@ReadOnly` is vacuous, accepted silently.** `@ReadOnly x: i64` has no effect (scalars are copied, never mutated through); v1 accepts it without diagnostic.

---

## 8. The Arc Beyond v1

`@ReadOnly` is the seed crystal. Each step extends the same shape-based, compiler-enforced, monotone-attenuating discipline.

- **DEF-1 — The H5 default-flip — SHIPPED.** DEF-2c (call-site exclusivity) closed AG-1's reachable core, making default-frozen soundly enforceable; DEF-1 then performed the flip. `Mutability::is_frozen` is now `matches!(self, ReadOnly | Default)` — a bare param is frozen, `@Mut` the opt-up — plus the stdlib/corpus `@Mut` migration (done by hand; the flip is **global**, not scoped/opt-in). Because every gate routes through that one predicate, the flip auto-extended all of them with no gate rework; `crates/sigil-compiler/tests/def1_flip.rs` is the proof matrix (bare ≡ `@ReadOnly` on every gate). NC-4 kept `@Mut` distinct so the flip was a single unambiguous line. The deep-aliasing remainder (AG-1 remote / AG-4 through-return) is unchanged — the same boundary `@ReadOnly` always had, now the default's boundary too, to be closed by full borrow checking.
- **DEF-2 — `@Region` / regions.** The borrow/aliasing substrate that closes AG-1 — "secret material that physically cannot outlive the request" (`docs/memory-model.md`). DEF-2a (lexical regions), DEF-2b (region-polymorphism), and DEF-2c (call-site exclusivity, `docs/specs/exclusivity.md`) have shipped; the *global* no-remote-alias guarantee's remainder (disjoint-region non-aliasing, through-return provenance) awaits per-region arenas.
- **DEF-3 — Capabilities-as-values.** `Cap<FileRead>` first-class and composable (H7) — the other capability flavor.
- **DEF-4 — Authority-origin / coherence-as-authority.** The orphan rule's deferred real model (the trait Wall's `validators.rs:86` "structural proxy … deferred to the capability model").

Capabilities are traits for authority; `@ReadOnly` is the first.

---

## 9. Constraints & Fallbacks

Each Existential Threat from the design's Adversarial-Compiler review reduced to a hard bound (the Boring Limit — a count or closed set that makes the edge case impossible) plus a loud, non-swallowing stop (the Fail-Fast). These are compile-time bounds; the fail-fast is a specific diagnostic plus the standing `has_errors() ⇒ abort-before-AIR` rule (zero WASM emitted).

### 9.1 NC-1 — No-escape attenuation

*Boring Limit:* exactly **1** readonly set per function body (append-only — once readonly, readonly for the whole body) + **1** `is_readonly_source` predicate (the expr's place-root, via the single `place_root_local`, is in the set). The value-sink set is closed (§3.5); `let` is the sole propagate site; ungated sinks = **0** (NC-3). *Fail-Fast:* a readonly source reaching any sink → **T253** at that site; body poisoned; **0** WASM bytes. *Accepted cost:* the stdlib carries `@ReadOnly self` on its entire read surface (§3.6), else frozen values can't be read through it.

### 9.2 NC-2 — Op-agnostic, fail-closed write gate

*Boring Limit:* op-branches in the write gate = **0** (it reads the place, never the operator — plain `=` and every compound op share one path); fail-open `_ => allow` arms = **0** (`place_root_local` is total over the T243-closed `Local`/`FieldAccess`/`Index`). *Fail-Fast:* a write to a readonly-rooted place → **T251**; an unmodelled place form (unreachable by T243) → an internal-compiler panic, never a silent allow.

### 9.3 NC-3 — Single attenuation chokepoint

*Boring Limit:* the per-parameter freeze decision is exactly **1** predicate, `Mutability::is_frozen`; the call-dispatch flavors that bind a parameter are a closed set (free, cross-module, true-method, string/trait reroute) each routing binding through the gate; ungated binding paths = **0**. The associated-function constructor path is deliberately excluded — it is reached only by no-`self` generic constructors (`Vec::new`, `Map::new`, `with_capacity`), every one of which takes only non-aliasable arguments, so its readonly-aliasable-argument condition is unreachable. *Fail-Fast:* `readonly → non-@ReadOnly` at any flavor → **T253**.

### 9.4 NC-4 — `@Mut` represented distinctly

*Boring Limit:* the `Mutability` enum has exactly **3** variants `{Default, ReadOnly, Mut}`; `Mut → Default` collapse points across parse / AST / `FunctionSig` = **0**. *Fail-Fast:* a flip-readiness unit test asserts `is_frozen` is true only for `ReadOnly` today and `Mut != Default`; any collapse turns the test red.

### 9.5 CM-arity — `param_mutability.len() != params.len()`

*Boring Limit:* built in the same `def.params` map ⇒ equal by construction; reads use `.get(i)` (missing ⇒ treated as mutable, safe). *Fail-Fast:* an out-of-range index is `None` ⇒ not frozen ⇒ no spurious gate; never a panic on a well-formed program.

### 9.6 CM-spelling — `@ReadOny` / `@readonly` / `@Frozen`

*Boring Limit:* `parse_param_annotations` matches the exact tokens `ReadOnly` / `Mut`; any other `@Ident` in parameter position that is not a taint label is rejected. *Fail-Fast:* **P021** at the annotation site — never a silently-ignored annotation.

---

## 10. Verification

The shipped suite (`crates/sigil-compiler/tests/readonly_parse.rs`, `readonly_compile.rs`, `readonly_stress.rs`):

- **WRITE (T251):** `p.x = 10`; `p.x += 1` (compound, NC-2); `a[0] = 9`; the launder `let b = p; b.x = 10` (NC-1); three-hop `let` chains.
- **ESCAPE (T253):** `return p`; `g(p)` into a plain parameter (re-widen); `Foo { f: p }` (record-wrap); `q.x = p` (assign-RHS); `v.push(1)` / `v.set(0,1)` / `m.insert(..)` on a frozen receiver; `q.store(p)` into a mutable method argument; a frozen `Vec` into a mutating free function.
- **Negative controls (compile clean):** `return p.x` (primitive copy); `let b = p; return b.x`; `v.get(0)` / `v.len()` / `m.contains(k)` on a frozen receiver; `mutable → @ReadOnly` freeze-on-entry; `@Mut` writes; mutate-a-copied-out-primitive.
- **Lint (T252):** `@ReadOnly s: &[i64]` warns and still compiles; a by-value `@ReadOnly` record does not warn (AG-11); a bare `&[i64]` does not warn.
- **Orthogonality:** `@SecretCT @ReadOnly` (either order) still rejects the write; `@SecretCT` alone does not freeze.
- **Flip-readiness (NC-4):** `is_frozen` is true only for `@ReadOnly`; `@Mut != Default`; `@Mut` behaves as bare.

**Zero-cost invariant:** the type-check, AIR, Wasm, workload, and JSON-shape snapshots remain byte-identical; `@ReadOnly` adds enforcement at typecheck and nothing to the emitted artifact.

---

## 11. References

- Boyland. "Alias Burying: Unique Variables Without Destructive Reads." Software: Practice and Experience, 2001. (Read-only references over a shared heap without full linearity.)
- Clarke, Potter, Noble. "Ownership Types for Flexible Alias Protection." OOPSLA 1998. (Confinement and read-only views as the substrate DEF-2 reaches toward.)
- Boyland, Noble, Retert. "Capabilities for Sharing: A Generalisation of Uniqueness and Read-Only." ECOOP 2001. (Read-only as a capability — the framing this spec adopts.)
- Matsakis, Klock. "The Rust Language." (The borrow checker that DEF-1's default-flip and DEF-2's regions converge toward.)
