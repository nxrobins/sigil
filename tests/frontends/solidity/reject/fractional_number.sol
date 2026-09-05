// expect-fe: FE430
// A genuinely-fractional literal cannot be a u256 (no unit-suffix context) — fail-closed.
pragma solidity ^0.8.0;
contract C { uint256 x; function f() public { x = 1.5; } }
