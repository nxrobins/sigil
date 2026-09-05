// expect-fe: FE430
// NC-L3c/LM5: an address literal must fit in 160 bits; a >40-hex literal in address
// position is out of range.
pragma solidity ^0.8.0;
contract C { function f(address a) public pure returns (bool) { return a == 0x10000000000000000000000000000000000000000; } }
