// expect-fe: FE401
// A `_;` outside a modifier body is not a statement (the `in_modifier` flag gates
// placeholder recognition) — it falls through to a fail-closed parse reject.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function setX(uint256 v) public {
        _;
        x = v;
    }
}
