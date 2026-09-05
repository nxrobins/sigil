// expect-fe: FE445
// A relational compare requires both operands the SAME enum (no enum-vs-uint).
pragma solidity ^0.8.0;
contract C { enum E { A, B } E s; function f(uint256 x) public view returns (bool) { return s < x; } }
