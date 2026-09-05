// expect-fe: FE411
// Fix-2b: a fabricated major (`^2.0.0`, `1.0.0`) is rejected — Solidity is `0.x`
// only, so the pragma floor is pinned to the real 0.8.x line.
pragma solidity ^2.0.0;
contract C { uint256 x; function g() public view returns (uint256) { return x; } }
