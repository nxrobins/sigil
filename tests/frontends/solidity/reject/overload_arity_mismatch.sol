// expect-fe: FE420
// SOL-XFILE PR3/OVL: a call to an overloaded name whose ARG COUNT matches no declared overload arity
// (`bump` exists at arity 1 and 2; `bump(a, a, a)` passes 3) → FE420 (fail-closed). Valid Solidity
// never produces this — solc resolves every call to a declared overload — so it guards a malformed
// input, never a real contract. Pins the disambiguation's arity-mismatch reject.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function bump(uint256 v) public {
        x = v;
    }

    function bump(uint256 v, uint256 w) public {
        x = v;
    }

    function go(uint256 a) public {
        bump(a, a, a);
    }
}
