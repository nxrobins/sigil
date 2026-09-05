// expect-fe: FE443
// NC-L3d/LM6: an `m[k]` key must match the mapping's declared key type — indexing an
// address-keyed map with a uint256 is an address/uint256 confusion (FE443).
pragma solidity ^0.8.0;
contract C { mapping(address => uint256) bal; function f(uint256 k) public view returns (uint256) { return bal[k]; } }
