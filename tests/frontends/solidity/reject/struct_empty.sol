// expect-fe: FE461
// EX-5/shape: an empty struct (no fields) is a degenerate record → rejected.
pragma solidity ^0.8.0;
contract C {
    struct E { }
    E e;
}
