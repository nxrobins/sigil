// SOL-MULTIMAP M-A: a transfer + a separate-map update (a staking/reward token shape) — a recognized
// atomic `balances.transfer()` PLUS a plain write to a DISTINCT `rewardDebt` map. FE412-blocked before
// this rung. `reserve_multi_map` reserves the deferred `rewardDebt` map (read-only) BEFORE the transfer,
// runs the self-atomic transfer (if it traps, `rewardDebt` was only reserved — nothing committed), then
// the trap-free `rewardDebt` insert last — exactly the `transfer_from` multi-map orchestration.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;
    mapping(address => uint256) rewardDebt;

    function transferWithReward(address from, address to, uint256 amt, uint256 r) public {
        balances[from] -= amt;
        balances[to] += amt;
        rewardDebt[to] += r;
    }
}
