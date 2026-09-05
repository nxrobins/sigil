// expect-fe: FE411
// NC-S3: pre-0.8 wraps by default; no faithful checked target.
pragma solidity ^0.7.0;
contract C { uint256 b; function f(uint256 a) public { b = a; } }
