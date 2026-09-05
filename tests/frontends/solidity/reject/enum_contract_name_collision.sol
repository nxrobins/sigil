// expect-fe: FE420
// An enum named after the contract collides with the contract record.
pragma solidity ^0.8.0;
contract C { enum C { A, B } uint256 x; }
