// expect-fe: FE491
// An array type is admitted ONLY in parameter position (the airdrop's `recipients`/`amounts`).
// A `uint256[]` STATE variable has no bounded-collection lowering → FE491. Confines the greenfield
// array surface to airdrop params; no dynamic storage array is created.
pragma solidity ^0.8.20;
contract C {
    uint256[] balances;

    function f() external {}
}
