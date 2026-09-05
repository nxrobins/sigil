// expect-fe: FE420
// EX-6: a struct named like the contract emits two records of the same name (N002 at
// name-resolution, invisible to the FE500 self-check) → rejected by the frontend.
pragma solidity ^0.8.0;
contract C {
    struct C { uint256 x; }
}
