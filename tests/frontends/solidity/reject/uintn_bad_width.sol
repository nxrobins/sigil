// expect-fe: FE410
// A non-multiple-of-8 width (`uint7`) is not a Solidity type → outside the allow-set.
pragma solidity ^0.8.0;
contract C {
    uint7 x;
}
