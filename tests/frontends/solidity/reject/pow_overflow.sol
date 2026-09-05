// expect-fe: FE430
// A constant `**` whose result exceeds the u256 range [0, 2^256) — Solidity 0.8 reverts on this
// overflow, so the fold rejects it.
pragma solidity ^0.8.0;
contract C { function f() public pure returns (uint256) { return 10 ** 78; } }
