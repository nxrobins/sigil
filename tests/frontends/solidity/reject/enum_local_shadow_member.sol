// expect-fe: FE410
// A local shadowing an enum name: `Color.Red` is then member access on the LOCAL (a u256),
// NOT enum-member access — it must NOT silently emit index 0 (EX-8 shadow guard).
pragma solidity ^0.8.0;
contract C { enum Color { Red, Green } function f() public pure returns (uint256) { uint256 Color = 5; return Color.Red; } }
