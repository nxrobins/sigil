// expect-fe: FE445
// An enum admits only the six comparisons, never arithmetic.
pragma solidity ^0.8.0;
contract C { enum E { A, B } E s; function f() public view returns (uint256) { return s + 1; } }
