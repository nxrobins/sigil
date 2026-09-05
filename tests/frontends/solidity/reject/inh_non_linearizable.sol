// expect-fe: FE471
// A non-linearizable hierarchy — D's bases impose contradictory orders (X before Y via A, Y before
// X via B). C3's merge has no valid head; solc rejects this identically.
pragma solidity ^0.8.0;
contract X { uint256 fx; }
contract Y { uint256 fy; }
contract A is X, Y { uint256 fa; }
contract B is Y, X { uint256 fb; }
contract D is A, B { uint256 fd; }
