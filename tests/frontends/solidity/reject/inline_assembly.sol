// expect-fe: FE478
// Inline assembly (YUL) is a separate low-level sub-language — precise-rejected, not a byte error.
pragma solidity ^0.8.0;
contract C { uint256 x; function f() public { assembly { let y := 1 } } }
