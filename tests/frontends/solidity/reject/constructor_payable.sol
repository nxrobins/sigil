// expect-fe: FE464
// EX-4: a `payable` constructor models ether at deploy — no value transfer in SIGIL.
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    constructor() payable { x = 1; }
}
