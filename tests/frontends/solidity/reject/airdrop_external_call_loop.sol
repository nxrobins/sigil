// expect-fe: FE401
// The TimelockController/multicall danger shape: a `for` loop making an EXTERNAL call per leg.
// The rigid `for` header parses to an `AirdropLoop`, but the body is a member-call (external),
// not an internal `_transfer` — `inline_internal_calls` rejects the non-`Var` callee → FE401,
// before `recognize_airdrop` ever runs. A batch of external calls is NOT a foldable airdrop.
pragma solidity ^0.8.20;
contract C {
    function batch(address[] calldata recipients, uint256[] calldata amounts) external {
        for (uint256 i = 0; i < recipients.length; i++) {
            recipients[i].transfer(amounts[i]);
        }
    }
}
