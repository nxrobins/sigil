// expect-fe: FE412
// SOL-MULTIWRITE EX-4 (straight-line only): a storage write inside an `if` branch is a CONDITIONAL
// commit — not simply hoistable to the top of the body. `total_cei` bails on any top-level `if` → the
// body stays non-CEI → FE412 (the branch's `total` arithmetic runs after the committed `balances`
// write). Cross-branch writes (OZ 5.x `_update`) are a declared anti-goal.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    uint256 total;

    function f(address a, uint256 x, bool c) public {
        balances[a] = x;
        if (c) {
            total = total + x;
        }
    }
}
