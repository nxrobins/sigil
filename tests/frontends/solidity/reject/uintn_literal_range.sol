// expect-fe: FE430
// EX-4: a literal that does not fit the target width (`256` into `uint8`) is rejected. The
// frontend is the sole gate — the u256 carrier would hold 256 silently.
pragma solidity ^0.8.0;
contract C {
    uint8 x;
    function f() public { x = 256; }
}
