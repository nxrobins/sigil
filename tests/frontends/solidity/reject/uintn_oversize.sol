// expect-fe: FE410
// A width > 256 (`uint264`) is not a Solidity type → outside the allow-set (uint256 is the
// max; it stays the full-width `u256` with no width-trap).
pragma solidity ^0.8.0;
contract C {
    uint264 x;
}
