// expect-fe: FE479
// Bitwise/shift operators are unsupported (stdlib-lowering deferred; never grown into native SIGIL).
pragma solidity ^0.8.0;
contract C { uint256 x; function f(uint256 a, uint256 b) public { x = a & b; } }
