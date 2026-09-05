// expect-fe: FE476
// A base named in `is` that is not defined in this file (cross-file imports are not resolved).
pragma solidity ^0.8.0;
contract B is Missing { uint256 y; }
