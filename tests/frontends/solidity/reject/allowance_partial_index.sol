// expect-fe: FE442
// EX-5: a two-key map must be FULLY (twice) indexed in a value position; a singly
// indexed `m[a]` is an inner mapping, not a first-class value.
pragma solidity ^0.8.0;
contract C {
    mapping(address => mapping(address => uint256)) m;
    function f(address a) public view returns (uint256) { return m[a]; }
}
