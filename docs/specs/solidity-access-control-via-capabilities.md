# Solidity access control via SIGIL capabilities — proposal

**Status:** **v1 IMPLEMENTED 2026-06-25** (opt-in `// sigil:cap-access-control`; the
owner read-gate → `&C_Owner`; codes FE454–FE457 live). Both the design (§7 E-1…E-6)
and the implementation plan were harden-spec'd; the strict constraints + fail-fast
matrix are §7–§8 and are honored by the implementation. `transferOwnership`/`onlyRole`
remain deferred (§5). Originally a pre-spec proposal; this section + §7–§8 are the
durable record.

**Depends on:** the `mint` capabilities-as-values epic (PR #396, **MERGED to `main`
2026-06-24, `d5ba88a`**) — the `&Cap` gate (T273), `mint <Cap> for`, delegation,
attenuation, static revocation. The dependency is satisfied; the epic is buildable
(§7 E-6).

**Builds on:** the SOL0/SOL1c Solidity frontend (`crates/sigil-frontends/src/solidity/`).

---

## 1. The opportunity (and why it's real, not cosmetic)

The Solidity frontend already translates the most common access-control pattern —
the `onlyOwner` modifier — but it translates it to a guard the frontend itself
declares **is not security**:

```solidity
// only_owner.sol
modifier onlyOwner() { require(msg.sender == owner); _; }
function setX(uint256 v) public onlyOwner { x = v; }
```
lowers today to (`only_owner.sigil`, the committed golden):
```sigil
pub fn setX(self: C @Mut, __fe_sender: u256, v: u256) {
    trap_if(!((__fe_sender == self.owner)));   // ← the "guard"
    self.x = v;
}
```

The load-bearing problem is in `desugar.rs`'s own header comment (AG-L1):

> `__fe_sender` is an UNTRUSTED, caller-supplied input — it is plumbing only,
> **NOT a security mechanism** (it does not reproduce the EVM's unforgeable
> `msg.sender`, and SOL1 builds no authentication for it).

So the emitted guard is **forgeable**: any caller can pass `self.owner`'s value as
`__fe_sender` and walk through `setX`. In Solidity this check *is* real security
(the EVM makes `msg.sender` unforgeable). **The translation under-delivers the
source's guarantee** — it's a faithfulness gap, not a chosen weakening.

**Capabilities close exactly this gap.** A `&Cap<Owner>` is unforgeable in SIGIL
the way `msg.sender` is unforgeable in the EVM: you either hold it or you don't,
and you cannot fabricate it (C001 + the `mint` gate). Translating `onlyOwner` to
"requires `&Cap<Owner>`" turns a forgeable runtime comparison into an
**unforgeable, compile-time-proven** authorization — the thing the Solidity author
actually meant. That is the synergy: not the `mint` keyword (ERC20 `mint` is
unrelated token-creation), but **access control**.

---

## 2. The deep tension — read this before anything else

Solidity access control and SIGIL capabilities are **different authorization
paradigms**, and the mapping is not mechanical:

| | Solidity (`onlyOwner` / `onlyRole`) | SIGIL capabilities |
|---|---|---|
| Authority is… | **identity** — *being* a specific `address` | **possession** — *holding* a `&Cap` token |
| Model | ACL / ambient-identity (`msg.sender`) | object-capability (unforgeable, transferable) |
| Check | runtime (`==` against stored address) | compile-time (the `&Cap` param must be in scope) |
| "Transfer" | reassign a stored address (`owner = x`) | delegate/mint a cap (linear move) |
| Introspection | `owner` is a readable `address` value | a cap is opaque; you can't read "who holds it" |

This is the classic ACL-vs-capability distinction. The consequences:

- **Where does authentication live?** In the EVM, the runtime authenticates the
  transaction signer and sets `msg.sender`. In SIGIL, *whoever calls `setX` must
  already hold `&Cap<Owner>`*. Authentication doesn't vanish — it **moves to the
  host/runtime boundary** that decides who is issued which caps. That's arguably
  the *right* place for it (the contract stops doing identity checks and just
  states its requirement), but it means the translated contract is no longer
  self-contained: it presumes an environment that distributes caps correctly.

- **Observable-semantics divergence.** A Solidity contract can do
  `require(msg.sender == owner)` *and* expose `owner` as a public getter, compare
  it, log it, transfer it by assignment, or have *two* checks against the same
  address. A capability has none of that — it's opaque and linear. So a faithful
  capability translation can only cover contracts whose use of the owner address
  is **purely authorization** (gate-and-nothing-else). The moment `owner` is read
  as data, the capability model and the address model diverge observably.

**Implication for scope:** capabilities should translate the *authorization role*
of an address, not the address itself. Contracts that use the address as data
must keep the address model (or be rejected). This split is the core design call.

---

## 3. Proposed mapping (scoped to the tractable case)

Target the **owner pattern only** for v1 — it's the most common, and it's the one
where the address is used purely as an authorization gate.

### 3a. The cap type and the gate
A contract with an `address owner` guarded by an `onlyOwner`-shaped modifier emits
a per-contract authority cap and threads a borrow through guarded methods:

```sigil
cap type C_Owner mintable_by C_Deploy { all }   // the contract's owner authority

impl C {
    // The guarded method REQUIRES the owner authority instead of comparing a
    // forgeable address. No `__fe_sender`, no `trap_if` identity check.
    pub fn setX(self: C @Mut, owner: &C_Owner, v: u256) {
        self.x = v;
    }
}
```
The `&C_Owner` borrow is the gate: a caller without it **cannot compile** a call
to `setX` (vs. today, where it traps at runtime *if* it passes the wrong sender —
and doesn't even do that, since the sender is forgeable). This is the whole win in
one line.

### 3b. Where the root owner cap comes from
Deployment mints it. The Solidity constructor (which usually sets
`owner = msg.sender`) maps to minting the root `C_Owner` at `new()`:
```sigil
pub fn new(deploy: &C_Deploy) -> (C, C_Owner) {   // returns the contract + its owner cap
    let owner_cap = mint C_Owner for /* the contract */ ;
    return (C { x: 0 }, owner_cap);
}
```
The deployer holds `&C_Deploy` (the mint authority, injected at the program
entrypoint — the "who may deploy" root). This is the capability analogue of "the
deployer becomes the owner."

### 3c. `transferOwnership` → delegation — **DEFERRED (harden-spec UP-4)**
`function transferOwnership(address n) onlyOwner { owner = n; }` *conceptually* maps
to **moving the owner cap** (linear delegation). **But the harden-spec pass showed
this does not fit v1's record model:** the contract emits as `record C` + `impl C`,
and a cap can never be stored in a record field (**T183** — see §7 E-3) or minted
without `&C_Deploy` in scope. So a `transferOwnership` *method* has no cap to move —
the move can only happen caller-side (the holder of the `C_Owner` value moves it),
which is not a translated contract function at all. Moreover `transferOwnership`
*writes* the owner field (`owner = n`), so under §7 E-2 it is an "address used as
data" use that disqualifies the contract from cap translation anyway. **v1 therefore
does NOT translate `transferOwnership`/`renounceOwnership`** (deferred — §5); they
are the natural second rung once the caller-side-move story is designed.

### 3d. `onlyRole(ROLE)` — deferred (see §5)
Role-based access (`MINTER_ROLE`, OpenZeppelin `AccessControl`) is the natural
extension — each role becomes a `cap type C_MinterRole`, `grantRole` becomes mint
+ delegate, `revokeRole` becomes (static) cap consumption or (later) reactive
revocation. **But it's out of the current SOL1 subset** (needs `bytes32` role ids
and the two-level `mapping(bytes32 => mapping(address => bool))` that FE440/FE410
reject today). So roles are a *second* epic, after the owner pattern proves out.

---

## 4. The hard parts (honest assessment — harden-spec seeds)

These are the brittle assumptions a real spec must resolve. Listed so the decision
to proceed is informed.

- **H1 — record-vs-actor model.** Contracts emit as `record C { … } + impl C`,
  **not** `actor`. The `&Cap` *gate* works fine in plain `fn`s (T273 only needs the
  borrow in scope). But capability **delegation via `send`** is actor-only — so
  `transferOwnership`-as-`send` (§3c) doesn't fit the record model. Options: (a)
  model ownership transfer as a returned/moved cap value (works in records, no
  `send`), or (b) move contracts to actors (big change, affects all of SOL1).
  **Recommend (a)** for v1 — keep records, transfer = linear cap return.

- **H2 — the authentication boundary moves, and must be stated.** §2: the contract
  stops checking identity and instead *requires* a cap. Something outside the
  contract must issue caps to the right principals. For a translated contract to be
  *runnable end-to-end*, we need a story for that boundary (a host that maps
  callers→caps). v1 can stop at "the contract requires the cap; cap distribution is
  the embedder's job" (compile-time proof only), but we must say so plainly — not
  imply runtime authentication we don't provide.

- **H3 — address-as-data contracts must be detected and excluded.** §2: if `owner`
  (or any access-controlling address) is read as a value — returned by a getter,
  compared elsewhere, stored, emitted — the capability model diverges. The frontend
  must **detect "address used only as an authorization gate"** vs "address used as
  data" and only capability-translate the former; the latter keeps the address
  model (or is rejected fail-closed). This dataflow analysis is the real
  engineering core, and the main risk of silent unfaithfulness if gotten wrong.

- **H4 — faithfulness of `transferOwnership`/`renounceOwnership`.** Solidity allows
  `owner = address(0)` (renounce → permanently locked) and re-assignment. Linear
  caps model transfer cleanly but "renounce" = drop/`burn` the cap (no holder ever
  again), and "two owners" / "compare owner to a literal" have no capability
  analogue. Enumerate which owner-ops are faithfully translatable.

- **H5 — opt-in / backward compatibility.** The existing goldens (`only_owner.sigil`
  etc.) and their tests encode the current `__fe_sender` shape. A capability
  translation changes every guarded function's signature and the golden output.
  Must be **opt-in** (a frontend flag, a pragma, or a heuristic that only fires on a
  recognized owner pattern) so SOL1 behavior is preserved by default and this is
  additive. Don't silently rewrite every contract.

- **H6 — the `mint`/deploy root.** §3b needs a `C_Deploy` authority to mint the
  owner cap. Where does *that* come from? The entrypoint-injected root (the program
  that instantiates the contract holds deploy authority). This is the same
  "turtles bottom out at the entrypoint" story as the base epic — fine, but the
  generated `new()` signature changes (it now takes `&C_Deploy` and returns the
  owner cap), which ripples into how a SIGIL program *uses* a translated contract.

- **H7 — `msg.sender` for non-owner logic. ⚠️ The post-impl review proved naive
  "coexistence" UNSOUND; v1 REJECTS it (FE454).** The original hope was that cap
  translation replaces only the *authorization* `msg.sender` while data uses
  (`balances[msg.sender]`) keep the `__fe_sender` plumbing, the two models coexisting.
  But inside an `onlyOwner` body `msg.sender` IS the authorized owner (the gate pinned
  `msg.sender == owner`): Solidity's `withdraw` could only ever touch `bal[owner]`.
  Dropping the gate frees `msg.sender` into the unconstrained `__fe_sender`, so an
  `&C_Owner` holder could pass ANY address and drain `bal[victim]` — a translation that
  compiles but is strictly weaker (funds theft). The opaque cap cannot rebind the owner's
  address, so **a guarded body that reads `msg.sender` cannot be faithfully cap-translated
  and is rejected** (FE454, see §7 E-2). Coexistence only holds for guarded bodies with NO
  `msg.sender` use (e.g. the headline `setX(v) { x = v; }`).

---

## 5. Scope

**v1 (the proposed first epic — owner pattern, gate-only):**
- Recognize the `onlyOwner`-shaped pattern (a modifier whose sole effect is
  `require(msg.sender == <stateAddr>)`), where `<stateAddr>` is used *only* as an
  authorization gate (H3 dataflow check).
- Emit a per-contract `cap type C_Owner` + thread `&C_Owner` through guarded
  methods (drop the `__fe_sender == owner` trap for those methods).
- Mint the root owner cap in `new()`; deploy authority from the entrypoint.
- **Opt-in** behind a flag/pragma (H5); SOL1 default unchanged.
- New FE codes for "address used as data, can't capability-translate" (fail-closed).

v1 is therefore strictly **gate-only**: recognize the `onlyOwner` *read-gate*, thread
`&C_Owner`, mint the root cap in `new()`. Nothing that *writes* the owner field.

**Deferred (later epics):**
- `transferOwnership` / `renounceOwnership` — they write the owner field (an
  address-as-data use, §7 E-2) and need a caller-side linear-cap-move story the
  record model can't express as a method (§3c, harden-spec UP-4).
- `onlyRole` / OpenZeppelin `AccessControl` (needs `bytes32` + nested mappings —
  out of SOL1 subset; a prerequisite subset extension, then the cap mapping).
- Reactive revocation (`revokeRole` as runtime revocation) — rides the base epic's
  deferred runtime-revocation follow-on.
- Actor-model contracts + `send`-based delegation (H1 option b).

**Explicit anti-goals:**
- Reproducing the EVM's *runtime* `msg.sender` authentication (capabilities move
  that to the host boundary by design — H2; we won't fake EVM signature checks).
- Capability-translating address-as-data uses (H3 — those keep the address model).
- A general ACL→capability compiler (this targets the recognized owner/role
  *patterns*, not arbitrary identity logic).

---

---

## 7. Strict Constraints (harden-spec, 2026-06-24 — binding)

These are hard MUST/MUST-NOTs that prevent the existential failures by construction.
The existential failure class for this feature is the translator's general one made
sharper: a translation that **compiles but is weaker than the source** (a dropped or
forged authorization). Each constraint below makes one such failure impossible.

- **E-1 — exact-shape recognizer (no over-fire).** Capability translation fires ONLY
  when an applied modifier's body is *exactly* `require(msg.sender == <F>); _;` — one
  guard statement plus the placeholder, nothing else — where `<F>` is a single state
  `address` field and the comparison is exactly `msg.sender == <F>` or `<F> ==
  msg.sender`. Any extra statement, extra operand (`&& …`), different operator, or
  compound condition disqualifies the modifier: it MUST emit the SOL1c `__fe_sender`
  shape instead, never a bare `&Cap` gate that silently drops the rest. (Closes
  MC-1/UP-5: dropping a co-located check is fail-*open*.)

- **E-2 — the access-controlling address is used ONLY as a gate.** The field `<F>`
  may appear in at most two positions across the whole SURVIVING contract: the E-1 gate
  comparison, and a constructor assignment `<F> = msg.sender`. ANY other occurrence —
  a getter return, another comparison, arithmetic, a map key,
  a second assignment (incl. `transferOwnership`), or any read as data — disqualifies
  the contract from cap-translating `<F>`. The classifier is **total and fail-closed** over
  the surviving program: an unknown or unanalyzable use counts as "data," so the default on
  doubt is to keep the address model, never to cap-translate. (Closes H3/MC-2/MI-2.)

  **SOL-HARDEN carve-out (2026-07-02): a discarded `event`/`emit` argument is NOT a data use.**
  `event`/`emit` are parse-time DISCARDED (SOL-EVENTS — events carry no SIGIL state/funds/control
  effect), so `<F>` read inside an emit — `emit E(owner)`, and even `emit E(bal[owner])` with `<F>`
  as a map key (the strongest data-use shape) — has NO sink in the emitted program and does NOT
  disqualify cap-translation. E-2 scans the SURVIVING program (the AST after parse-time discards),
  not the source text. This is sound because FE481 (`emit_arg_discard_safe`) guarantees a discarded
  emit argument is side-effect-free (no call, no trap-capable arithmetic), so a discarded owner read
  is a pure, sink-less read; the `&Cap` authority envelope is byte-identical to the same contract
  with the emits removed. **FE481 is the SUFFICIENT precondition** — were it ever weakened, this
  carve-out would need revisiting. Pinned by `compile/cap_emit_owner.sol` (all three shapes:
  plain read, map-key read, and an emit between the gate `require` and `_`).
  **Review fold (2026-06-25): the gate IDENTITY is broader than the field token.** E-2
  also rejects (FE454): (a) a guarded method body that reads `msg.sender` — under
  `onlyOwner` that value equals the owner, and the opaque cap cannot supply it (the
  funds-theft H7 case); and (b) an owner field with a fixed initializer (`address owner =
  0x..`) — a cap cannot represent a pinned owner address. A non-initialized owner is the
  canonical "deployer becomes owner": the `C_Owner` minted in `new()` IS that authority
  (E-5). (Also, general SOL0 name fixes the review surfaced: a function named `new`, and
  duplicate function names, are rejected FE420 — they would collide as impl-methods.)

- **E-3 — caps never enter an aggregate.** GROUNDED: SIGIL rejects a cap in a record
  field (**T183**), enum payload (**T184**), array element (**T186**), or generic
  aggregate (**T242**), and `type_contains_cap` recurses tuples/`Fn`. Therefore the
  owner cap MUST be emitted only as a borrow parameter (`&C_Owner`) or a returned
  value — **never stored in the contract `record`**. **SPIKE-CONFIRMED 2026-06-24**
  (against merged `d5ba88a`): `fn new(deploy: &C_Deploy, …) -> (C, C_Owner) { … return
  (C { … }, mint C_Owner for …); }` compiles cleanly — the T183/T242 family rejects
  caps in *stored* aggregates, not in a *return tuple*; the bare-cap return and the
  `&C_Owner` borrow-param gate also compile. (Re-verify under a `--features solver`
  build during implementation — the spike ran structural cap rules only; the Z3
  cap-flow proof of a returned full-authority minted cap is expected clean, since
  `cap_mint.rs::mint_then_delegate_via_call` already proves a minted cap discharges a
  full-authority sink.) (Closes MI-3/UP-3.)

- **E-4 — opt-in, all-or-nothing.** Capability translation is OFF by default; the
  default output for every contract is byte-identical SOL1c (`__fe_sender`). It is
  enabled only by one explicit opt-in (flag/pragma). Within a translated contract the
  decision is per-contract all-or-nothing: every `onlyOwner`-gated method is cap-gated
  or none is — never a partial mix. (Closes MC-3/H5/MI-1/MI-4.)

- **E-5 — compile-time proof only; no runtime-auth claim.** The emitted contract
  proves *requirement* of a cap at compile time; it performs NO runtime authentication
  and the spec/docs MUST NOT imply it reproduces the EVM's `msg.sender` signing.
  Cap *distribution* to principals is explicitly the embedder's responsibility.
  (Closes H2/UP-6.)

- **E-6 — dependency gate (SATISFIED 2026-06-24).** The `mint` capabilities-as-values
  epic (**PR #396**) is now merged to `main` (`d5ba88a`); the gate is cleared and the
  epic is buildable. The `&Cap` gate (T273), `mint <Cap> for`, attenuation (T199), and
  forgery rejection (C001) are all live. (Closed UP-0.)

## 8. Constraints & Fallbacks (boring limit · fail-fast)

| # | Boring limit | Fail-fast |
|---|---|---|
| E-1 | recognized modifier body = exactly `require(msg.sender == <addr field>)` + `_` (2 nodes) | any deviation → emit the SOL1c `__fe_sender` shape; never a partial/bare-cap gate |
| E-2 | `<F>` occurs in ≤ {1 gate comparison, 1 `<F> = msg.sender` ctor assign}; 0 elsewhere **in the SURVIVING program** (a discarded `event`/`emit` arg is exempt — no SIGIL sink, FE481-pure) | any other occurrence (incl. unanalyzable) → new FE code, keep the address model |
| E-3 | 0 emitted caps in record field / enum / array / tuple-in-aggregate (T183/T184/T186/T242) | emitted SIGIL fails its own compile / a pre-emit assert trips → translator bug, reject (FE500-class) |
| E-4 | cap mode off by default; exactly 1 opt-in switch; per-contract all-or-nothing | opt-in absent → byte-identical SOL1c; mixed gating within a contract → reject |
| E-5 | the spec carries 1 explicit "compile-time proof only, no runtime auth" statement | documentation invariant (reviewed, not runtime) |
| E-6 | ~~do not implement until PR #396 is on `main`~~ — **SATISFIED** (`d5ba88a`, 2026-06-24) | (gate cleared; the epic is buildable) |

**Ambient backstop:** the translator is untrusted and the emitted SIGIL is re-verified
by the trusted compiler, so any cap that *does* slip into a forbidden position, or any
attenuated/expired owns cap passed to a full-authority sink, fails loudly via the
existing cap rules (T183/T184/T186/T242, T199, C001/C003) rather than silently — the
constraints above exist so the *frontend* never emits such SIGIL in the first place.
