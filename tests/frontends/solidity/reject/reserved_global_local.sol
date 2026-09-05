// expect-fe: FE420
// SOL1b adversarial-review fix (L3-02): a LOCAL named `msg`/`tx`/`block` must be
// rejected too (not just params/state), so the reserved-EVM-global invariant the
// msg.sender rewrite relies on holds in every binding position.
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    function f() public { uint256 msg = 7; x = msg; }
}
