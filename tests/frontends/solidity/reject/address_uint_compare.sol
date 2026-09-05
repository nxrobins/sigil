// expect-fe: FE443
// NC-L3b/LM4: address never silently mixes with uint256 (no implicit conversion).
pragma solidity ^0.8.0;
contract C { function f(address a, uint256 u) public pure returns (bool) { return a == u; } }
