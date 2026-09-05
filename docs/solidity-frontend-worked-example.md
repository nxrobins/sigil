# Solidity → SIGIL: a worked example (what actually happens)

This is a hands-on walkthrough of what you get when you run the Solidity frontend on
real input. For the design and the full `FE`-code list, see
[`specs/foreign-frontends.md`](specs/foreign-frontends.md); for the capability
access-control mode, [`specs/solidity-access-control-via-capabilities.md`](specs/solidity-access-control-via-capabilities.md).

## The model in one paragraph

The frontend is an **untrusted** source-to-source translator: it lowers a Solidity
contract to SIGIL **text**, which is then re-verified from scratch by the mature Rust
`sigil-compiler` (the trust anchor). It translates **one deployable contract at a
time** — either a single self-contained file, or a **multi-file project**
(`--project-root`), where imports resolve and the inheritance hierarchy (abstract
bases, interfaces) is flattened into the entry file's one concrete contract. Untrusted
`import` strings never drive filesystem reads: the trusted CLI walks the root once and
resolution is a pure in-memory lookup. Either way it is a **fail-closed gate**, not a
best-effort transpiler: the input either translates to SIGIL that the trusted compiler
independently proves safe, or it is rejected with a precise `FE` code naming exactly
the unsupported/unfaithful construct. The existential risk it exists to prevent is a
translation that *compiles but means something weaker than the source*; every rejection
is the frontend refusing to take that risk.

```
sigil translate --from solidity Contract.sol      # emit the SIGIL text
sigil check     --from solidity Contract.sol      # translate AND re-verify (the trust handoff)
sigil check     --from solidity --project-root oz/ oz/contracts/mocks/token/ERC20Mock.sol
                                                  # multi-file: resolve imports, flatten bases
```

Pipeline: `lex → parse → flatten (inheritance) → validate identifiers → desugar
(inline internal calls + modifiers, normalize, fold funds-moves to atomic ops) →
check (sound, fail-closed) → emit → parse self-check`, then hand the text to the
trusted compiler.

---

## Example 1 — a contract that translates (the happy path)

A full, event-free ERC20 core (`tests/frontends/solidity/compile/erc20_full.sol`):

```solidity
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;
    mapping(address => mapping(address => uint256)) allowance;

    function balanceOf(address who) public view returns (uint256) { return balances[who]; }
    function allowanceOf(address owner, address spender) public view returns (uint256) { return allowance[owner][spender]; }
    function approve(address spender, uint256 amount) public { allowance[msg.sender][spender] = amount; }
    function transfer(address to, uint256 amount) public {
        require(balances[msg.sender] >= amount);
        balances[msg.sender] -= amount;
        balances[to] += amount;
    }
    function transferFrom(address from, address to, uint256 amount) public returns (bool) {
        require(allowance[from][msg.sender] >= amount);
        allowance[from][msg.sender] -= amount;
        balances[from] -= amount;
        balances[to] += amount;
        return true;
    }
}
```

`sigil translate --from solidity erc20_full.sol` emits:

```sigil
module erc20_full;

record Token { balances: BoundedMap_u256_u256_64, allowance: BoundedMap2_u256_u256_u256_64 }

impl Token {
    pub fn new() -> Token {
        return Token { balances: BoundedMap_u256_u256_64::new(), allowance: BoundedMap2_u256_u256_u256_64::new() };
    }
    pub fn balanceOf(self: Token, who: u256) -> u256 { return self.balances.get_or(who, 0); }
    pub fn allowanceOf(self: Token, owner: u256, spender: u256) -> u256 { return self.allowance.get_or(owner, spender, 0); }
    pub fn approve(self: Token @Mut, __fe_sender: u256, spender: u256, amount: u256) {
        self.allowance.insert(__fe_sender, spender, amount);
    }
    pub fn transfer(self: Token @Mut, __fe_sender: u256, to: u256, amount: u256) {
        trap_if(!((self.balances.get_or(__fe_sender, 0) >= amount)));
        self.balances.transfer(__fe_sender, to, amount);
    }
    pub fn transferFrom(self: Token @Mut, __fe_sender: u256, from: u256, to: u256, amount: u256) -> bool {
        trap_if(!((self.allowance.get_or(from, __fe_sender, 0) >= amount)));
        self.allowance.transfer_from(self.balances, from, __fe_sender, to, amount);
        return true;
    }
}
```

What the lowering made explicit: `msg.sender` is now a parameter (`__fe_sender`),
arithmetic is checked `u256` (overflow **traps**), mappings are bounded, and — the
load-bearing part — `transferFrom`'s allowance debit + balance move fold into **one
atomic** `transfer_from`. They can't be two separate writes: SIGIL has no atomic
revert, so a trap between them would desync funds from allowance. (A non-canonical
`transferFrom` that *can't* fold is rejected with FE412 rather than mistranslated.)

`sigil check --from solidity erc20_full.sol` then re-verifies it through the trusted
compiler:

```
Compiled `<multi-module>` from stdlib/sigil/bounded_map2_u256_u256_u256.sigil.
Wasm size: 44686 bytes. AIR functions: 58. Runtime fuel budget: 1416.
```

That's a real artifact the *trusted* compiler signed off on — not the frontend
asserting its own output is fine.

---

## Example 2 — a real-world token: the project pipeline, and the rejection report

Point it at an OpenZeppelin-style token **as a lone file** and it refuses at the first
unresolvable base — imports parse, but a single file cannot supply them:

```solidity
pragma solidity ^0.8.20;
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";
contract MyToken is ERC20, Ownable { /* ... */ }
```
```
error: FE476: base contract `Ownable` is not defined in this file (cross-file imports are not resolved)
error: translation failed
```

Hand it the **project** instead — the trusted CLI walks the root, imports resolve as
pure in-memory lookups, and the real, unmodified OpenZeppelin hierarchy (`Context`,
`IERC20`, `IERC20Metadata`, `IERC20Errors`, `ERC20`, the entry) flattens into the one
concrete contract and compiles end-to-end:

```
$ sigil check --from solidity --project-root openzeppelin/ \
      openzeppelin/contracts/mocks/token/ERC20Mock.sol
Compiled `<multi-module>` from contracts/mocks/token/ERC20Mock.sol.
Wasm size: 46034 bytes. AIR functions: 62. Runtime fuel budget: 1464.
```

That is the actual OZ `ERC20Mock.sol` — `transfer`/`approve`/`transferFrom`/mint/burn,
internal calls inlined, the funds-moves folded to atomic primitives — signed off by the
trusted compiler. Probing the other real-world constructs individually gives, in each
case, either a faithful lowering or a precise refusal:

| Construct | Result |
|---|---|
| `import` + inheritance (`is ERC20`), abstract/interface bases | **resolve & flatten** under `--project-root`; unresolvable in a lone file → **FE476**; a `library` base → **FE476** |
| external call (`IERC20(t).transfer(...)`) | **FE401** (out of subset — no external calls, so no reentrancy surface at all) |
| `event Transfer(...)` / `emit` | **discarded** (events have no SIGIL effect); an effectful emit arg → **FE481** |
| `uint8`…`uint248` | **translates** — the `u256` carrier plus a frontend-enforced `2^N` width trap |
| `bytes32` | **translates** — a full-width opaque id on the `u256` carrier (role ids, hashes) |
| `int*` / `bytesN` (N<32) | **FE410** "outside the SOL allow-set" (signed and left-aligned widths stay out) |
| `unchecked { ... }` | **translates as CHECKED** — where Solidity wraps, SIGIL traps (a declared, fail-loud divergence; OZ's guarded `unchecked` never hits it) |
| `using X for Y` | **FE477** (only `using SafeMath for uint256` is recognized — its `.add`/`.sub` fold to checked ops) |
| `mapping(=>mapping(=>mapping))` (3-deep) | **FE440** "nesting deeper than 2 levels… no bounded analog" |
| a storage write before a trap-capable op (non-CEI) | **reordered** into checks-then-effects when provably order-independent (values hoisted, guards first); a genuinely order-dependent body → **FE412** |

So compiling a *repo* is not a build — it's a **triage report**: per entry contract,
either verified SIGIL or an auditable, precise reason it can't be faithfully
represented. Never a silent miscompile.

---

## Example 3 — the capability upgrade (a translation *stronger* than the source)

Opt in with one comment directive, `// sigil:cap-access-control`, and the `onlyOwner`
access-control pattern changes meaning. Take a single contract:

```solidity
contract Config {
    address owner;
    uint256 fee;
    modifier onlyOwner() { require(msg.sender == owner); _; }
    function setFee(uint256 v) public onlyOwner { fee = v; }
}
```

**Without** the directive (faithful, but *forgeable* — `__fe_sender` is caller-supplied,
exactly as Solidity's `msg.sender` would be if the EVM didn't make it unforgeable):

```sigil
record Config { owner: u256, fee: u256 }
pub fn setFee(self: Config @Mut, __fe_sender: u256, v: u256) {
    trap_if(!((__fe_sender == self.owner)));
    self.fee = v;
}
```

**With** the directive (the gate becomes an unforgeable capability; the `owner` field
and the runtime check both disappear):

```sigil
cap type Config_Deploy { mint_owner }
cap type Config_Owner mintable_by Config_Deploy { all }
record Config { fee: u256 }

impl Config {
    pub fn new(__fe_deploy: &Config_Deploy) -> (Config, Config_Owner) {
        let __fe_c = Config { fee: 0 };
        return (__fe_c, mint Config_Owner for __fe_c);
    }
    pub fn setFee(self: Config @Mut, __fe_owner: &Config_Owner, v: u256) {
        self.fee = v;                       // no runtime check at all
    }
}
```

### Why it's unforgeable (demonstrated, not asserted)

`setFee` now demands a `&Config_Owner`. The only `Config_Owner` in existence is minted
once inside `new()`, which itself requires `&Config_Deploy`. You can't fabricate either:

- **Construct it?** A field-less capability has no record-literal form — `Config_Owner { }`
  is a *parse error*. There is no expression that builds a `Config_Owner` except `mint`.
- **Mint it without authority?** The same `mint` statement compiles with `&Config_Deploy`
  in scope and is refused without it:

```sigil
// holds the authority → OK (compiles to wasm)
fn deploy(__fe_deploy: &Config_Deploy) -> Config_Owner {
    let c: Config = Config { fee: 0 };
    let owner: Config_Owner = mint Config_Owner for c;
    return owner;
}
// no authority in scope → rejected by the trusted compiler:
fn attacker(c: Config @Mut) -> Config_Owner {
    let owner: Config_Owner = mint Config_Owner for c;   // ERROR
    return owner;
}
```
```
error: `mint Config_Owner` requires an in-scope immutable borrow of its minting
       authority `Config_Deploy` (a `&Config_Deploy` parameter)
```

Caps are also linear (can't be copied). So a caller who didn't deploy has **no path**
to a `Config_Owner`, and therefore literally cannot compile a call to `setFee` — the
authorization is enforced statically by the trusted compiler, not by a runtime check a
code path might skip. The frontend turned a forgeable runtime check into an
unforgeable, compile-time-proven one: a translation provably *stronger* than its source.

(Scope: cap-mode covers the `onlyOwner` access-control pattern. A cap-mode *full ERC20*
is rejected with FE454 on `approve`/`transferFrom`, because using `msg.sender` as a map
key under a dropped gate is an unsound coexistence the frontend refuses.)

---

## What a successful translation is (and isn't)

Even on the happy path, the output is a **verified bounded model**, not a redeployable
EVM artifact:

- **bounded** — `BoundedMap` holds ≤ 64 entries; the 65th distinct key *traps*. A token
  with thousands of holders won't run, by construction.
- **no EVM ambient** — no gas, reentrancy, `msg.value`/ether, or events; `msg.sender` is
  forgeable plumbing unless you opt into the `&Cap` gate.
- **traps don't roll back** — which is *why* only checks-then-effects contracts translate.

The point is not to recompile Solidity for the EVM. It is to land a contract's logic in
a capability-secure, statically-verified, overflow-trapping language where you can prove
properties the EVM can't give you — and to refuse, precisely and loudly, anything it
can't make honest.
