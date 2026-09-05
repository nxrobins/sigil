// expect-fe: FE492
// The `for` header parses to an `AirdropLoop`, but the body is a plain accumulation, not the
// exact `[debit, credit]` transfer pair. Once a loop is recognized as an `AirdropLoop` it MUST
// be a valid airdrop or FE492 — a residual loop node never reaches the backend (fail-closed).
pragma solidity ^0.8.20;
contract C {
    uint256 total;

    function sum(uint256[] calldata amounts) external {
        for (uint256 i = 0; i < amounts.length; i++) {
            total = total + amounts[i];
        }
    }
}
