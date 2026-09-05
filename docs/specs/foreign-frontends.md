# Foreign Frontends — Spec

**Status:** PR-FE0 (TypeScript → capabilities, inner-ring), PR-FE1 (TypeScript
`@effects` → effects, outer-ring), and PR-FE2 (booleans, records, control flow —
a typed subset behind a sound type+scope checker) implemented. Crate:
`crates/sigil-frontends`. CLI: `sigil translate --from <lang>` and
`sigil check --from <lang>`.

## Thesis

A *foreign frontend* is an **untrusted** source-to-source translator that
compiles an external surface DSL into SIGIL **text**, which the mature Rust
`sigil-compiler` then verifies. The translator is never trusted; **SIGIL is the
trust anchor**. This mirrors the project's pervasive compiler-as-oracle stance
(differential testing, the kernel-primitives fitness oracle). The verifier is
the *Rust* compiler — the self-hosted `selfhost/*.sigil` toolchain is a smaller
differential subset and is explicitly out of scope: emitted SIGIL need only be
accepted by the Rust compiler, and frontends are not gated on self-hosted parity.

## Contract

```rust
pub trait Frontend {
    fn name(&self) -> &'static str;
    fn translate(&self, src: &str, source_name: &str)
        -> Result<EmittedSigil, Vec<FrontendDiag>>;
}
```

`EmittedSigil { source_name, text, map }` carries the emitted SIGIL and a
best-effort source map. `FrontendDiag { code, message, span }` is a
translator-level rejection. Translation either succeeds with **well-formed SIGIL**
or fails with ≥1 diagnostic — it never panics, hangs, or emits partial output.

### FE-code family

| Code | Meaning |
|------|---------|
| `FE001` | construct outside the supported subset |
| `FE002` | input/complexity bound exceeded (size, depth, function count) |
| `FE010` | unrecognized/misspelled policy annotation (fail-closed) |
| `FE011` | `@cap`-derived cap never threaded into the body (internal guard) |
| `FE012` | emitted authority envelope ≠ authored policy (internal guard) |
| `FE020` | identifier outside `^[A-Za-z_][A-Za-z0-9_]{0,63}$` |
| `FE021` | identifier collides with a SIGIL keyword, the `__fe_` prefix, or a reserved SIGIL type name (`i64`/`bool`/`str`/`Region`/`Slot`/… used as an `interface` name) |
| `FE030` | numeric literal not an exact in-range decimal i64 (incl. a negative or i64::MIN `@cap` deadline, which is unemittable as a parametric-cap literal) |
| `FE031` | operator outside the FE0 whitelist |
| `FE040` | a `@cap`-bearing function is called intra-program (deferred convention) |
| `FE500` | emitted SIGIL failed the parse self-check (internal — translator bug) |
| `FE201` | a file mixes `@cap` and `@effects` (mode is per-file homogeneous) — FE1 |
| `FE202` | a `@cap` item reached effect-mode emission (internal backstop) — FE1 |
| `FE210` | an emitted effect row name has no co-emitted `effect` decl (internal) — FE1 |
| `FE211` | an emitted top-level name collides (effect/cap-type vs fn → N002) — FE1 |
| `FE213` | an author `@effects` name collides with a reserved effect (`Unsafe`/`FFI`/`Alloc`) — FE1 |
| `FE301` | an in-subset TS type error (the checker rejects rather than emit ill-typed SIGIL) — FE2 |
| `FE302` | a record construction omits a declared field — FE2 |
| `FE303` | an `if`/`while` condition is not `bool` (no truthiness) — FE2 |
| `FE304` | an object literal in a position with no inferable record type — FE2 |
| `FE305` | a record construction names a field the record does not declare — FE2 |
| `FE306` | a non-unit function does not `return` on every path — FE2 |
| `FE307` | a reassignment that cannot lower to a legal `let mut` (const/param target) — FE2 |
| `FE308` | an unresolved reference (no live binding in scope) — FE2 |
| `FE309` | unary `!` on a non-`bool` operand — FE2 |
| `FE310` | a record value used where a different (nominal) record is expected — FE2 |
| `FE311` | operand-type mismatch: relational on non-i64, or `==`/`!=` across unequal types — FE2 |
| `FE320` | a TS construct outside the FE2 allow-list (optional fields, methods, unions, `/`, `%`, …) — FE2 |
| `FE502` | a two-run byte-compare found nondeterministic output (test-gate marker) — FE2 |

`FE012`/`FE500` are internal invariants: if they fire, the *translator* is buggy
— never a user-policy fault. Errors in emitted SIGIL otherwise surface as the
compiler's own `T-` codes (e.g. **T199** for a stale cap).

## TypeScript policy subset → capability contract (FE0)

A discovered two-ring constraint shapes the design: **outer-ring functions cannot
own capabilities**, while **effect rows only enforce in the outer ring** (inner-
ring modules are exempt from `effect_check`), and **cross-ring calls are
R004-forbidden**. Capabilities and effects are therefore mutually exclusive per
module. So a translated file is **cap-mode XOR effect-mode**, chosen by a
whole-file pre-pass: any `@effects` → effect-mode (outer ring, FE1, below);
otherwise cap-mode (inner ring, FE0). A file with both `@cap` and `@effects` →
**FE201** (mixed-mode deferred — would need a cross-ring `grant` bridge). FE0
(cap-mode) emits inner-ring capability contracts:

| TS construct | Emitted SIGIL | Enforced by |
|---|---|---|
| `function f(a: number): number {…}` | `pub fn f(a: i64) -> i64 {…}` | type checker |
| `number` | `i64` | type checker |
| `/** @cap Name(deadline=D) */` | `cap type Name(deadline_ms: i64) {}` + a synthetic `__fe_cap_i: Name(D)` parameter, threaded (moved) into a generated terminal consumer | `capability::verify` + **T199** |
| return body | `return (<expr>) + __fe_consume_k(__fe_cap_i)…;` | ownership (move) |

Supported subset: top-level function declarations; `number` params and return;
body `return <expr>;` over `+ - *`, integer literals, parameters, and calls to
other declared (non-cap) functions; the `@cap` JSDoc annotation. Everything else
is a fail-closed `FE` rejection.

Capabilities are threaded (not decorative): the synthetic cap parameter is
**moved** into a terminal consumer, so the compiler's ownership pass tracks it
(threading twice is a use-after-move, O001). This matters because the compiler
does **not** flag an *unused* cap parameter — so the translator, not the
compiler, must guarantee the cap is used.

### Enforcement demo

`@cap Net(deadline=2020)` translated, then `sigil check --from typescript
--build-deadline 2025 …` → the compiler emits **T199** (the cap would be stale
before execution). The translator is untrusted; SIGIL proves the contract.

## TypeScript `@effects` → effect contract (FE1, effect-mode)

A file with any `@effects` is **effect-mode**: emitted as an `#[ring(outer)]`
module so the compiler's effect checker runs. `/** @effects A, B */` becomes a
sorted effect row `! { A, B }`; functions without `@effects` get an explicit
`! { }`. Each distinct effect is co-emitted as an `effect Name;` decl.

| TS construct | Emitted SIGIL | Enforced by |
|---|---|---|
| `/** @effects A, B */ function f(x: number): number {…}` | `effect A; effect B;` (once each) + `pub fn f(x: i64) -> i64 ! { A, B } {…}` | `effect_check` / **E001** |
| a function with no `@effects` | `pub fn f(...) -> i64 ! { } {…}` | (empty enforced row) |

**The fail-open spine (F5).** Effects are *never ambient*: an effect name in a row
with no `effect Name;` decl is **silently dropped by the compiler, no diagnostic,
zero enforcement**. The emitter therefore co-emits an `effect Name;` (same module)
for every name in every row, both derived from the one authored `@effects` set
(row ⊆ decls); the parse self-check (FE500) cannot catch a missing pairing.
`Unsafe`/`FFI`/`Alloc` are compiler-reserved and rejected as author effect names
(**FE213**); emitted effect names must also not collide with function names
(**FE211** — the collision is N002 at name-resolution, invisible to FE500).

### Enforcement demo (FE1)

A function that omits an effect its callee declares → the compiler emits **E001**
(effect leakage), the FE1 analog of T199:

```
/** @effects NetIO */ function fetch(t: number): number { return t; }
function handler(a: number): number { return fetch(a); }   // ! { } calls ! { NetIO } → E001
```

## TypeScript typed subset → booleans, records, control flow (FE2)

FE0/FE1 only expressed `i64` arithmetic in a single `return <expr>;`. FE2
broadens the subset — in **both** ring modes — to the `boolean` type,
comparisons (`== != < <= > >=`), unary `!`, logical `&&`/`||` (desugared),
`interface`→`record` with construction and field access, bool/record params and
returns, and **control-flow bodies**: `let`/`const` locals + reassignment,
`if/else`, `while`, and multi-statement blocks.

| TS construct | Emitted SIGIL | Enforced by |
|---|---|---|
| `boolean`, `true`/`false` | `bool`, `true`/`false` | type checker |
| `a < b`, `a == b`, `!x` | passthrough (→ `bool`) | type checker / **T012/T041** |
| `interface N { x: number; y: boolean }` | `record N { x: i64, y: bool }` (decl order) | type checker |
| `let p: N = { y: b, x: a }` | `let p: N = N { x: a, y: b };` (decl-order fields) | type checker |
| `p.x` | `p.x` | type checker |
| `let`/`const` + reassignment | `let mut` (if reassigned) / `let` | ownership / **T042** |
| `if (c) {…} else {…}`, `while (c) {…}` | passthrough; `if` always emits an `else` | **T012** / T044 |

This turns the translator into a small compiler, so **its spine is its own
*sound* type + scope checker** (`typescript/check.rs`). The checker resolves
every reference against a block-scoped stack, assigns every node a resolved type
(`i64`/`bool`/named record), and verifies operand/argument/condition/field/return
types **before emission** — so emitted SIGIL never fails for a translator reason.
Any in-subset TS type/scope/return error becomes a clean `FE3xx` reject, not a
masquerading compiler `T`-code:

- **The ill-typed-emission spine (H2/M1).** The checker's per-node type must equal
  the type the SIGIL compiler would resolve (oracle agreement) — totality
  ("carries *some* type") is insufficient; a uniform "everything i64" checker is a
  defect. Any in-subset type error → **FE301** (relational/equality mismatch →
  **FE311**), never a stray T012/T041/T054/T055.
- **Records fail-open spine (H1).** The compiler **silently accepts a record
  construction that omits fields** (no diagnostic). The checker therefore requires
  the provided field-name set to equal the declared set exactly: a missing field →
  **FE302**, an unknown field → **FE305**. Construction must name the record type
  and only appears where that type is statically inferable (return / let / param /
  field / call-arg) → else **FE304**. Fields are always emitted in **declaration
  order** regardless of literal order (M6 — equivalent literals are byte-identical).
- **No truthiness (H4).** `if`/`while` conditions must resolve to `bool` → else
  **FE303**; the translator never synthesizes `x != 0`. Unary `!` requires a `bool`
  operand → else **FE309**.
- **Return-path analysis (H5).** A non-unit function must `return` on every path
  (`if`/`else` counts iff *both* branches do) → else **FE306** (never emit a body
  that would hit T044).
- **Scope + mutability (H6/H7).** Each reference resolves to the innermost live
  binding → unresolved → **FE308**. `let mut` is emitted iff a binding is
  reassigned; a reassignment whose target is a `const` or a parameter → **FE307**.
- **Nominal records (H17).** The interface→record name map is injective; a value of
  record `A` used where record `B` is expected → **FE310** (no structural equivalence).
- **Reserved type names.** An `interface` may not be named a SIGIL built-in type
  (`unit`/`bool`/`i32`/`u32`/`i64`/`u64`/`f64`/`str`/`Region`/`Slot`) → **FE021**: the
  compiler resolves such a name to the *built-in* before consulting user records, so
  the emitted `record` would be silently shadowed (a value flow diverges, or field
  access fails with T122). `is_sigil_keyword` does not catch these — primitives are
  Idents, not keywords — so the checker carries the set explicitly. A bare annotation
  naming a primitive (`p: i64`, where TS should write `number`) is **FE320**.

### `&&`/`||` desugaring (ANF — `typescript/desugar.rs`)

SIGIL has no logical operators and `if` is a statement, so `a && b` / `a || b`
are lowered (M3: **before** check and emit) to a `bool` temp plus a guarded `if`
that evaluates the RHS only on the short-circuit-reachable path:

```
return a < b && b < 10;     →     let mut __fe_0 = (a < b);
                                   if __fe_0 { __fe_0 = (b < 10); } else { }
                                   return __fe_0;
```

Temps use the reserved `__fe_<n>` prefix with a per-function monotonic index,
declared in the nearest enclosing block immediately before use (M4); lowering is
strictly intra-function — no new helpers, no call relocated across a function
boundary (M5, which preserves effect attribution / E001). `&&`/`||` are lowered in
**any position whose enclosing statement evaluates the expression exactly once** —
return value, `let`/`const` RHS, assignment RHS, expression statements,
`if`-conditions, **call arguments, and field values** (including nested logical,
whose RHS hoists *inside* the guard). The single exception is a `while` condition:
it re-evaluates each iteration, so `&&`/`||` there cannot be hoisted to a one-shot
temp and are rejected (**FE301**; lift the test into a helper).

## Solidity → SIGIL (SOL0 + SOL1)

The Solidity frontend (`src/solidity/`, codes **FE4xx**) translates a contract
subset to a SIGIL `record` (state) + `impl` (methods). The synergy is
**overflow-safety + fund-safety by construction** — not "proved invariants"
(Solidity declares none): checked-`u256` arithmetic traps on under/overflow (the
classic drain bug is impossible), and the bounded-ledger transfer is atomic
checks-then-effects. The existential risk for any frontend is a translation that
*compiles* but *means* something different, so the discipline is **reject (an
FE4xx), never best-effort** — and because the trusted compiler only ever sees the
emitted `u256`, the frontend's `check.rs` is the **sole gate** for the
distinctions below.

**SOL0 (scalar state).** `uint256`/`uint` → `u256`, `bool` → `bool`; checked
`+ - * / %`; `require`/`assert(c)` → `trap_if(!(c))`, `revert` → `trap_if(true)`
(reason dropped); `if`/`return`; state-field literal initializers populate a
synthesized `new()` (else zero-default). Strict **checks-then-effects (NC-S1)**:
no trap-capable op may run after a committed storage write (a SIGIL trap does not
roll back prior writes, unlike a Solidity revert) → **FE412**. Type allow-list
→ **FE410**; pragma `>= 0.8.0` + no `unchecked` → **FE411**; non-literal init →
**FE413**; closed subset (member access, calls) → **FE401**/FE410. Totality is
frontend-owned: a Solidity-local `MAX_NEST_DEPTH` is threaded through every
recursive descent *and* every flat operator/postfix loop, so adversarial nesting
yields **FE402** rather than a stack overflow in the parser, the downstream
walkers, the recursive `Drop`, or the FE500 re-parse (*bounding recursion depth ≠
bounding AST depth*).

**SOL1a (stateful ledger).** The `address` type is a **closed distinct type** that
lowers to `u256` but, enforced by a sound `SolTy` inference pass: rejects
arithmetic/ordering on an address (**FE443**), never silently mixes with `uint256`
(assign/compare/index-key cross-use → FE443), and bounds an address literal to 160
bits (**FE430**) — at *every* value-flow position, including state-field
initializers. A single-level `mapping(K => V)` (K,V ∈ {address, uint256}) becomes
the bounded `BoundedMap_u256_u256_64` (nested → **FE440**, bool-keyed/valued →
**FE441**); `m[k]` read → `get_or(k, 0)` (the Solidity zero-default), write →
`insert`. A key whose static type ≠ the mapping's declared key type → FE443/FE442;
indexing a non-mapping → **FE442**. A non-address type mismatch (bool↔numeric) →
**FE445** (kept distinct from FE443 so the address-misuse code stays precise).

**Bounded-ledger zero-value limit (NC-L1).** The map has no key deletion, so a
value-0 entry is physically present where Solidity treats an *absent* key as 0. A
**bare** `m[k] += v` / `-= v` write lowers to an unconditional
`insert(k, get_or(k, 0) ± v)`, so a runtime `v == 0` on a *fresh* `k` materializes
a value-0 slot — a fail-closed divergence (it can force the 65th-key capacity trap
earlier than 64 *funded* holders, but never yields a wrong balance) that is the
bounded ledger's documented approximation, **not** guarded at the emission site
(guarding every scalar map-write would cost a stdlib method or an emit-time branch
for a benign, capacity-only divergence). The **recognized transfer idioms** —
`transfer` / `transfer_split` / `transfer_from` (and, on the SOL-UPDATE path,
`erc20_update`) — are zero-value-**faithful**: a zero-delta leg on a fresh key is
skipped (no slot reserved, no capacity consumed), matching Solidity's no-op `+= 0`
exactly. This closes the divergence for the common fee-on-transfer / mint / burn /
transferFrom paths while leaving the rare bare-write case as the honest NC-L1 limit.

**SOL1b (caller authority + guards + transfer).** A pre-check pass (`desugar.rs`,
order *lex → parse → desugar → check → emit*) lowers three things:

- **`msg.sender`** → a synthesized `__fe_sender: address` param (prepended after
  `self`), making the caller explicit. It is an **untrusted** input — plumbing,
  not a security mechanism (it does not reproduce the EVM's unforgeable
  `msg.sender`; no authentication is built for it). Other `msg.*`/`tx.*`/`block.*`
  members stay FE410; `msg`/`tx`/`block` as user identifiers are FE420.
- **`&&`/`||`** → the same ANF desugar as TypeScript (bool temp + guarded `if`,
  short-circuit preserved); the SOL1 subset has no loops, so every position is
  hoistable.
- **the canonical transfer** `bal[from] -= a; bal[to] += a;` (compound or
  expanded) → folded into one call to the **trusted** stdlib
  `BoundedMap_u256_u256_64.transfer(from, to, amount)`. That method does *all*
  checks before *any* write — balance, self-transfer (`from == to`) net-zero,
  credit overflow, and bounded-ledger capacity reservation — so a trap leaves no
  partial state (the fund-safety the naive sequential two-write form cannot give,
  since a SIGIL trap is not an atomic revert). The fold is **conservative +
  fail-closed**: only an *adjacent*, same-map, same-amount debit→credit pair whose
  `from`/`to`/`amount` are free of map reads folds; anything else stays two writes
  and the second is FE412. The map-read-free guard is a **soundness** requirement —
  `bal[a] -= bal[a]; bal[b] += bal[a];` must NOT fold (Solidity credits the
  post-debit value; a fold would read the pre-debit value), so it is left unfolded
  → FE412.

**SOL1c (modifiers → inlined guards).** A `desugar.rs` pass 0 (run *before*
`lower_sender`) inlines each applied `modifier` into the function it guards: the modifier
body's single `_` placeholder is replaced by the host function body, so check/emit see one
merged body and the guard's `msg.sender`/`&&`/transfer idioms flow through the existing
passes unchanged. The leftmost modifier is outermost (a right-fold). Every step is
fail-closed — a dropped guard is the existential failure for a security translator:

- **exactly one `_`** per modifier, counted across nested `if` branches — 0 would drop the
  body, >1 duplicate it → **FE447**. Parameterless modifiers only: a declared parameter or
  an applied argument list → **FE448**; `payable`/`virtual`/`override` (function attributes
  that lex as bare idents in modifier position) → **FE452**.
- **no dropped guard (E1)** — after inlining, every `Function.modifiers` is empty and no
  `_` placeholder survives, asserted in *both* desugar and emit → **FE500** otherwise.
- **no silent shadow** — a modifier-introduced local colliding with a host local/param, **a
  contract state field**, or another applied modifier's local → **FE449**. Flat inlining
  merges the scopes, so the collision would silently shadow the name (a state-field shadow
  redirects the host's reads/writes to a dead local — a verified-but-wrong translation).
  Rejected, never alpha-renamed.
- **no suffix after `_`** — statements after the placeholder run on function EXIT in
  Solidity (even after a body `return`), which flat inlining cannot model (the suffix becomes
  dead code when the body returns — e.g. a `nonReentrant` unlock that never clears). The `_`
  must be in tail position; a suffix → **FE453**.
- **undefined / duplicate** modifier → **FE451** / **FE450** (never silently drop a guard).
- **totality (E3)** — splicing concatenates two depth-bounded bodies, so the merged body is
  re-bounded to `MAX_NEST_DEPTH` *before* emit's trusted re-parse → **FE402**, never a
  native stack overflow.

The **CEI synergy**: a `nonReentrant`-style modifier that writes a lock *before* `_` makes
the spliced body's first guard a trap-capable op after a committed write → **FE412** by the
existing CEI rule, with no new code. This is faithful: under SIGIL's no-rollback trap a body
trap would brick the lock (stuck set), so the unfaithful form is correctly refused.
Guard-only modifiers (`onlyOwner`, `whenNotPaused`) inline cleanly.

**SOL-CAP v1 (onlyOwner → unforgeable `&Cap` gate, opt-in).** Today `onlyOwner` lowers to
a *forgeable* `trap_if(!((__fe_sender == self.owner)))` (the frontend declares `__fe_sender`
"NOT a security mechanism"), so the translation under-delivers the source's guarantee. Behind
the opt-in directive `// sigil:cap-access-control`, the recognizer turns the `onlyOwner`
*read-gate* into a `&C_Owner` capability parameter (unforgeable; a caller without it can't
compile the call): a per-contract `cap type C_Owner mintable_by C_Deploy { all }`, `new()`
mints the root cap and returns `(C, C_Owner)`, guarded methods gain `&C_Owner` (the trap is
dropped), and the owner field — used purely as the gate — is dropped from the record. It is
fail-closed and additive: OFF by default (byte-identical SOL1c); the address may be used
ONLY as the gate (any data use → FE454); only the exact `require(msg.sender == <addr>); _;`
shape qualifies (a near-miss → FE455). The full design + the harden-spec constraints
(E-1…E-6, IMPL-1…IMPL-5) are in `solidity-access-control-via-capabilities.md`.
`transferOwnership`/`onlyRole` are deferred. See `cap_mint.rs` (the `mint`/`&Cap` substrate,
PR #396).

**SOL-ERC20 v1 (bounded nested mappings → full ERC20).** A `mapping(K => mapping(K2 =>
V))` (the ERC20 `allowance`) now lowers to a **bounded two-key map**
`BoundedMap2_u256_u256_u256_64` — parallel `[u256; 64]` key1/key2/value arrays, a flat
≤64 *pairs* total (the same accepted bounded-ledger lie as the single-level map, one
dimension up; the 65th distinct pair traps loud, never a silent drop). A two-level read
`m[a][b]` → `get_or(a, b, 0)`, write → `insert(a, b, v)`; a third level (`m[a][b][c]`,
or a deeper mapping type) → **FE440**; a singly-indexed two-key value → **FE442**;
either key's static type ≠ the declared key → FE443/FE445 (both positions checked).
This unblocks `approve` (a nested write) and the `allowance` getter (a nested read).
**`transferFrom`** is the security crux: the canonical `allowance[from][spender] -=
amount;` + the balance debit/credit *cannot* be two separate writes (a SIGIL trap
between them would desync funds from allowance — there is no atomic revert), so the
recognizer folds the allowance debit + the (already-folded) balance `MapTransfer` into
ONE call to the **trusted** cross-map `allowance.transfer_from(balances, from, spender,
to, amount)` — every check across both maps before any write, the allowance write last
and provably trap-free. A non-canonical / non-atomic transferFrom is **not** folded;
its two writes hit the CEI gate (**FE412**), so no non-atomic transferFrom can compile.
Events (`event` declarations + `emit` statements) are parse-and-DISCARDED — they carry no SIGIL
state/funds/control-flow effect (SIGIL models no logs), so the faithful lowering is nothing. The one
guard: an `emit` argument that is effectful (a real function call, or trap-capable arithmetic like
`a - b`) → **FE481** (a discarded emit can't preserve its argument's revert/side-effect; bind it to a
local first). Plain reads and pure casts (`address(0)`) are dropped freely. (Was FE459, retired.)
The two-key map + `transfer_from` are ambient-injected stdlib
(`bounded_map2_u256_u256_u256.sigil`), re-verified like all SIGIL — not a language or
compiler change.

**FE4xx codes.** FE401 unsupported construct, FE402 size/depth, FE410 unsupported
type / unsupported member, FE411 unchecked/pragma, FE412 non-CEI, FE413
indeterminate init, FE414 bad guard, FE420 bad/reserved identifier, FE430 bad
number / over-160-bit address literal, FE440 mapping nesting deeper than 2 levels,
FE441 bad mapping K/V, FE442 bad index, FE443 address misuse (arith/ordering/uint256-mix), FE445
non-address type mismatch, FE446 view/pure state write, FE447 modifier `_` count,
FE448 parameterized modifier, FE449 modifier/host local collision, FE450 duplicate
modifier, FE451 undefined modifier, FE452 unsupported function attribute, FE454
cap-mode address-used-as-data, FE455 cap-mode onlyOwner near-miss, FE456 cap-mode
multiple owner authorities, FE457 cap-mode synthesized-name collision, FE500
emitted-SIGIL parse self-check (internal).

**Bounded-ledger limitation (NC-L1, accepted).** `BoundedMap_u256_u256_64` is a
≤64-entry ledger, NOT a faithful unbounded mapping: the 65th distinct-key insert
(or a transfer creating it) **traps** — loud, never a silent drop. The capacity
cap is the only place the bounded model intentionally diverges from Solidity, and
it diverges in the safe direction (revert, never corruption).

**Accepted Solidity translation divergences (SOL-HARDEN audit, 2026-07-02).** Each is
authority-/state-faithful or fails in the safe (narrower / louder) direction; recorded here
so the divergence is auditable, not a shrug:

- **Function visibility is not enforced in the emitted contract (F1).** `internal`/`private`
  Solidity functions emit as non-`pub` SIGIL methods, but the trusted compiler currently
  registers every impl method as `Public` (`universe.rs`), so the `pub`/non-`pub` distinction
  is cosmetic — a former-`internal` method is callable by any SIGIL host/importer. Bounded: a
  referenced internal function is FE401 (intra-contract calls are out of subset), so any
  *surviving* internal function is dead code; this widens the surface to dead entry points, not
  past an existing guard. This is a compiler property the frontend cannot influence (it emits the
  correct non-`pub`); it will close when the compiler honors impl-method visibility.
- **`public` state-variable getters are dropped (F2).** Solidity auto-generates an external
  getter for a `public` state var; the frontend emits only the record field, no getter method.
  A NARROWER surface (fail-closed, no authority/state/fund effect).
- **Scalar `string` state variables are dropped.** A `string public name = "X";` is
  parse-discarded (pure metadata, no SIGIL state/funds/control effect — like events); a later
  read of the dropped field is an unresolved-identifier FE401 (fail-closed).
- **A discarded `event`/`emit` arg is not a cap-mode data use (C2).** Under `//
  sigil:cap-access-control`, an `emit` argument that reads the owner field (even as a map key) is
  discarded before the E-2 gate and does NOT disqualify cap-translation — the `&Cap` authority
  envelope is byte-identical to the same contract without the emits, and FE481 keeps the discarded
  arg side-effect-free. See the cap spec §E-2 carve-out + `compile/cap_emit_owner.sol`.

## Constraints & Fallbacks

Each threat has a dumb physical bound (an exact number, a fixed whitelist, or a
structural impossibility) and a fail-fast that emits nothing. Bounds align to
compiler constants where they exist (S005 = 5 MiB input; S006 = 10 000
functions; i64 literal range). The FE0 depth bound (64) is **FE0-owned and
checked before descent** — the Rust parser has no recursion-depth cap, so
totality cannot be delegated to it, and the FE500 self-check re-parse runs only
on already-depth-bounded output. Synthetic names use the reserved `__fe_` prefix,
disjoint from user identifiers by construction. The full matrix lives in the arc
plan; the conformance suite is `crates/sigil-frontends/tests/typescript_golden.rs`.

## Explicit Anti-Goals (FE0 + FE1 + FE2)

- **Source-map fidelity** — an identity map is acceptable; diagnostics on emitted
  SIGIL need not map to exact `.ts` spans.
- **Mixed cap + effect in one file** — deferred (would need a cross-ring `grant`
  bridge); a mixed file is FE201.
- **Effect least-privilege / nominal labels** — FE1 trusts the author's `@effects`
  and enforces *vocabulary-consistent propagation* (E001), not authority over real
  operations; labels are opaque, bound to no concrete I/O.
- **`@taint` / `@requires`** — deferred (taint / refinements).
- **Cross-function cap calling convention** — a `@cap`-bearing function may not be
  called intra-program (FE040); the threading convention is deferred.
- **Corpus ingestion** — does not feed translator output into `sigil-corpus`.
- **`/` and `%`** — not translated (TS-float vs SIGIL-int divergence); out-of-subset
  → FE320.
- **Cyclic records** — not pre-rejected; the compiler accepts self-/mutually-
  recursive records (4-byte pointer, no cycle analysis).
- **`while` non-termination** — a runtime/fuel concern, not a translate-time one;
  the only compile-relevant slice (missing return) is FE306.
- **`&&`/`||` in a `while`-condition** — the one non-hoistable position (the
  condition re-evaluates each iteration), rejected with FE301. Every other position
  (return / let / assign / expr-stmt / if-cond / call-arg / field-value, incl.
  nested) is lowered soundly; FE2 need not support logical operators in a
  re-evaluated condition.
- **Record construction outside inferable positions** — only where the expected
  record type is statically known (return / let / param / field / call-arg) → else
  FE304.
- **`mut` minimality** — a TS `const` may emit as `let mut`; an unused `mut` is
  harmless. Determinism (M6) still holds; only the immutability hint is lost.

## The broader arc

Next: `@taint`/`@requires` (taint / refinements), a `FrontendCorpus` extractor,
and mixed cap+effect files via `grant`. The Solidity frontend is under way (SOL0 +
SOL1 + SOL1c above: overflow-safe scalar contracts, address/mapping/index,
caller-authority `msg.sender`, `&&`/`||`, the atomic bounded transfer, and
modifiers → inlined guards); its capability/effect layer (`address`+`transfer` → a
`@Transfer` cap, events → `@Log`, per-width `uintN`) is the next slice once the
cap-XOR-effect split allows it. Later frontends: Python→bounded plans;
agent-manifest→deploy-cert and IaC→authority-graph once those SIGIL targets exist.
