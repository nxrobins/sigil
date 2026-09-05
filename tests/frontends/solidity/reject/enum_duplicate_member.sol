// expect-fe: FE467
// A duplicate member name would alias two tags to the same index.
pragma solidity ^0.8.0;
contract C { enum E { A, B, A } uint256 x; }
