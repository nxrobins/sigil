// expect-fe: FE462
// EX-3: implicit narrowing `uint256` → `uint8` is rejected (Solidity compile-errors it; a
// silent truncation would corrupt data). The carrier is invisible to the trusted compiler.
pragma solidity ^0.8.0;
contract C {
    uint8 x;
    function f(uint256 a) public { x = a; }
}
