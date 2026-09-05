// expect-fe: FE401
// Fix-4: a `revert()` with no terminating `;` must fail closed (the old token-eater
// scanned to the next `;`, silently swallowing the following `x = a;` statement).
pragma solidity ^0.8.0;
contract C { uint256 x; function f(uint256 a) public { revert() x = a; } }
