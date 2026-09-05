// expect-fe: FE480
// The ternary `cond ? a : b` is unsupported (guarded-if lowering is a deferred follow-on).
pragma solidity ^0.8.0;
contract C { uint256 x; function f(uint256 a, uint256 b) public { x = a > b ? a : b; } }
