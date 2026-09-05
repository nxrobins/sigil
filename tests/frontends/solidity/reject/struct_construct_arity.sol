// expect-fe: FE460
// EX-1: positional construction must supply EVERY field exactly once. `Point` has two
// fields but is constructed with one arg → rejected (the compiler fails open on records).
pragma solidity ^0.8.0;
contract C {
    struct Point { uint256 x; uint256 y; }
    function f(uint256 a) public pure returns (Point memory) {
        return Point(a);
    }
}
