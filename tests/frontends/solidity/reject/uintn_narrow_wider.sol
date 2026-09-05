// expect-fe: FE462
// EX-3: implicit narrowing of a WIDER uintN (`uint16` → `uint8`) is rejected. Widening
// (uint8 → uint16, uintN → uint256) is allowed; only narrowing needs an explicit cast.
pragma solidity ^0.8.0;
contract C {
    uint8 x;
    function f(uint16 a) public { x = a; }
}
