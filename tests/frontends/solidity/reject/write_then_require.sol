// expect-fe: FE412
// NC-S1: a require after a state write can't faithfully revert (no rollback).
pragma solidity ^0.8.0;
contract C { uint256 b; function f(uint256 a) public { b = a; require(a > 0); } }
