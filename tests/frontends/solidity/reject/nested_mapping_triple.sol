// expect-fe: FE440
// EX-5: mapping nesting deeper than the supported 2 levels has no bounded analog.
pragma solidity ^0.8.0;
contract C { mapping(address => mapping(address => mapping(address => uint256))) m; }
