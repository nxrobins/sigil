// expect-fe: FE420
// `msg`/`tx`/`block` are reserved EVM globals — a user identifier shadowing one would
// make the `msg.sender` → `__fe_sender` rewrite ambiguous, so it is rejected.
pragma solidity ^0.8.0;
contract C { function f(uint256 msg) public pure returns (uint256) { return msg; } }
