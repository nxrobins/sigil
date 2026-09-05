// expect-fe: FE412
// MC1: the killer case — y += a can overflow-trap AFTER x committed, destroying
// funds where Solidity would atomically revert. SOL0 rejects (defer to a hoisting slice).
pragma solidity ^0.8.0;
contract C { uint256 x; uint256 y; function f(uint256 a) public { x = x - a; y = y + a; } }
