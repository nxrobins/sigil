// expect-fe: FE420
// An enum named like a stdlib bounded-map type the frontend emits.
pragma solidity ^0.8.0;
contract C { enum BoundedMap_x { A, B } uint256 y; }
