// expect-fe: FE442
// NC-L3/LM6: `[]` on a non-mapping value is a type error the frontend must catch.
pragma solidity ^0.8.0;
contract C { function f(uint256 x) public pure returns (uint256) { return x[0]; } }
