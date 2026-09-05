// A bounded token ledger (SOL1): a `mapping(address => uint256)` balance store, a
// view `balanceOf`, and a CEI-clean single-write `mint`. NOT a full ERC20 — the map
// is capacity-bounded (64 keys; the 65th distinct-key insert traps) and there is no
// `transfer` yet (the two-write transfer + `msg.sender` caller-authority land in
// SOL1b). Synergy: balances are full u256 and every overflow traps by construction.
pragma solidity ^0.8.0;
contract Ledger {
    mapping(address => uint256) balances;
    uint256 total;

    function balanceOf(address who) public view returns (uint256) {
        return balances[who];
    }

    function mint(address to, uint256 amount) public {
        balances[to] = balances[to] + amount;
    }
}
