// expect-fe: FE412
// SOL-MULTIWRITE EX-2 (no WAW): a location written TWICE cannot be hoisted+reordered — the two writes
// read the same pre-write value in the hoisted lets, so the reorder would drop one write's effect
// (`totalSupply` would end at `old + b` instead of the source's `old + a + b`). `total_cei` bails on a
// double-written location → the body stays non-CEI → FE412 (the map write / second bump follows the
// first committed write).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    uint256 totalSupply;

    function f(address k, uint256 x, uint256 a, uint256 b) public {
        totalSupply = totalSupply + a;
        balances[k] = x;
        totalSupply = totalSupply + b;
    }
}
