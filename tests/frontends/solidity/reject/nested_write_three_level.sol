// expect-fe: FE440
// EX-5/EX-6: a three-level index WRITE `m[a][b][c] = v` exceeds the 2-key shape.
pragma solidity ^0.8.0;
contract C {
    mapping(address => mapping(address => uint256)) m;
    function f(address a, address b, address c, uint256 v) public { m[a][b][c] = v; }
}
