// expect-fe: FE412
// SOL-MULTIMAP M-A EX-A2 (≤1 transfer): two folded `transfer()`s (on distinct maps) cannot both be made
// atomic — a transfer's balance-sufficiency check `trap_if(fb < amount)` is NOT reservable, so the first
// transfer commits, then the second's balance check can trap → the first is stranded. `reserve_multi_map`
// bails on ≥2 transfers → the body stays non-CEI → FE412 (the second `MapTransfer` follows the first commit).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    mapping(address => uint256) staking;

    function f(address from, address to, uint256 amt) public {
        balances[from] -= amt;
        balances[to] += amt;
        staking[from] -= amt;
        staking[to] += amt;
    }
}
