// expect-fe: FE463
// EX-3: Solidity allows exactly one constructor; a second would silently drop init logic.
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    constructor() { x = 1; }
    constructor(uint256 a) { x = a; }
}
