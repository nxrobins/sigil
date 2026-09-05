// expect-fe: FE469
// An inheritance cycle — A is B, B is A. No concrete sink; C3 can't linearize. solc rejects it too.
pragma solidity ^0.8.0;
contract A is B { uint256 x; }
contract B is A { uint256 y; }
