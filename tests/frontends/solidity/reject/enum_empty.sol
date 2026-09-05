// expect-fe: FE467
// An empty enum has no valid zero-default.
pragma solidity ^0.8.0;
contract C { enum Empty {} uint256 x; }
