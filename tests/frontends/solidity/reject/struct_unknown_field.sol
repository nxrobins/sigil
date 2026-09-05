// expect-fe: FE460
// EX-1: field access of a field the struct does not declare → rejected.
pragma solidity ^0.8.0;
contract C {
    struct Point { uint256 x; uint256 y; }
    function f(Point memory p) public pure returns (uint256) {
        return p.z;
    }
}
