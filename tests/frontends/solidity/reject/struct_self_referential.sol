// expect-fe: FE461
// EX-5: a struct that contains itself by value is an infinite-size record → rejected
// before emit (never relying on the trusted compiler to diverge).
pragma solidity ^0.8.0;
contract C {
    struct Node { uint256 v; Node next; }
}
